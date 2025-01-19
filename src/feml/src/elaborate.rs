use crate::core_syntax::{self, Term, TermBox};
use crate::evaluate::{apply_closure, evaluate};
use crate::intern::{self, Symbol};
use crate::parse_tree as pst;
use crate::token::Loc;
use crate::value::{self, Val, ValBox};

use std::collections::HashMap;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("{1} not defined")]
    NotDefined(Loc, String),
    #[error("expected {1}, got {2}")]
    TypeMismatch(Loc, String, String),
    #[error("unexpected parameter type {1}, expected {2}")]
    ParamTypeMismatch(Loc, String, String),
    #[error("expected function type, got {1}")]
    NotFunction(Loc, String),
    #[error("unable to infer type for {1}")]
    NoLambdaInfer(Loc, String),
}

impl Error {
    pub fn loc(&self) -> Loc {
        match self {
            Self::NotDefined(loc, _)
            | Self::TypeMismatch(loc, _, _)
            | Self::ParamTypeMismatch(loc, _, _)
            | Self::NotFunction(loc, _)
            | Self::NoLambdaInfer(loc, _) => *loc,
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct Context {
    intern_pool: intern::Pool,
    type_type: Type,
    constants: HashMap<Symbol, Type>,
    scope: HashMap<Symbol, Binding>,
    scope_depth: usize,
}

pub type Type = ValBox;

struct Binding {
    sym: Symbol,
    ty: Type,
    // level = (scope_depth - debruijn_index). this value is stable as new bindings are
    // introduced and can be used to obtain the correct debruijn index by subtracting from
    // scope_depth again.
    level: usize,
}

impl Context {
    pub fn new() -> Self {
        let intern_pool = intern::Pool::new();

        // initialize constants
        let sym_type = intern_pool.intern("type");
        let sym_nat = intern_pool.intern("nat");
        let type_type = value::con(sym_type);
        let type_nat = value::con(sym_nat);
        let mut constants = HashMap::new();
        constants.insert(sym_type, type_type.clone()); // type : type
        constants.insert(sym_nat, type_type.clone()); // nat : type
        constants.insert(intern_pool.intern("Z"), type_nat.clone()); // Z : nat
        constants.insert(
            // S : nat -> nat
            intern_pool.intern("S"),
            value::arrow(type_nat.clone(), type_nat.clone()),
        );

        Self {
            intern_pool,
            type_type,
            constants,
            scope: HashMap::with_capacity(32),
            scope_depth: 0,
        }
    }

    fn type_type(&self) -> Type {
        self.type_type.clone()
    }

    fn env(&self) -> value::Env {
        value::env_neutral(self.scope_depth)
    }

    pub fn elab_exp_infer(&mut self, exp: &pst::Exp<'_, '_>) -> Result<(TermBox, Type)> {
        match exp {
            pst::Exp::Var(x) => self.lookup(*x),
            pst::Exp::App(fun, arg) => self.elab_app_infer(fun, arg),
            pst::Exp::Lam(lam) => self.elab_lam_infer(lam),
            pst::Exp::Arr(arr) => self.elab_arr(arr).map(|t| (t, self.type_type())),
            pst::Exp::Mat { .. } => unimplemented!("match expressions"),
        }
    }

    pub fn elab_exp_check(&mut self, exp: &pst::Exp<'_, '_>, ty: Type) -> Result<TermBox> {
        match exp {
            pst::Exp::Lam(lam) => self.elab_lam_check(lam, ty),
            _ => {
                // no special checking rule, fall back to inference
                let (stx, inf_ty) = self.elab_exp_infer(exp)?;
                if !self.compatible(&inf_ty, &ty) {
                    return Err(Error::TypeMismatch(
                        exp.loc(),
                        self.pretty_value(&ty),
                        self.pretty_value(&inf_ty),
                    ));
                }
                Ok(stx)
            }
        }
    }

    pub fn elab_type(&mut self, ty_exp: &pst::Exp<'_, '_>) -> Result<Type> {
        let ty_tm = self.elab_exp_check(ty_exp, self.type_type())?;
        let ty = evaluate(self.env(), ty_tm);
        Ok(ty)
    }

    fn elab_app_infer(
        &mut self,
        fun: &pst::Exp<'_, '_>,
        arg: &pst::Arg<'_, '_>,
    ) -> Result<(TermBox, Type)> {
        let (fun_tm, fun_ty) = self.elab_exp_infer(fun)?;
        let (dom_ty, rng) = match &*fun_ty {
            Val::Pi(dom_ty, rng) => (dom_ty.clone(), rng),
            _ => return Err(Error::NotFunction(fun.loc(), self.pretty_value(&fun_ty))),
        };
        let arg_tm = self.elab_exp_check(arg, dom_ty)?;
        let arg = evaluate(self.env(), arg_tm.clone());
        let ret_ty = apply_closure(rng, arg);
        Ok((core_syntax::app(fun_tm, arg_tm), ret_ty))
    }

    fn elab_lam_infer(&mut self, lam: &pst::Lambda<'_, '_>) -> Result<(TermBox, Type)> {
        let param_sym = lam.name.intern(&self.intern_pool);
        let param_ty = match lam.param {
            Some(param) => self.elab_type(param.ty)?,
            None => return Err(Error::NoLambdaInfer(lam.name.loc, lam.name.to_string())),
        };
        let (body_tm, ret_ty) = {
            let prev = self.bind(param_sym, param_ty.clone());
            let result = self.elab_exp_infer(lam.body);
            self.unbind(prev);
            result?
        };
        let ret = core_syntax::Abs {
            param: param_sym,
            body: reify(self.scope_depth + 1, &ret_ty),
        };
        Ok((
            core_syntax::lam(param_sym, body_tm),
            value::pi(param_ty, ret, self.env()),
        ))
    }

    fn elab_lam_check(&mut self, lam: &pst::Lambda<'_, '_>, ty: Type) -> Result<TermBox> {
        let param_sym = lam.name.intern(&self.intern_pool);
        let (dom_ty, rng) = match &*ty {
            Val::Pi(dom_ty, rng) => (dom_ty.clone(), rng),
            _ => return Err(Error::NotFunction(lam.loc(), self.pretty_value(&ty))),
        };
        if let Some(param) = lam.param {
            let param_ann_ty = self.elab_type(param.ty)?;
            if !self.compatible(&dom_ty, &param_ann_ty) {
                return Err(Error::ParamTypeMismatch(
                    param.ty.loc(),
                    self.pretty_value(&param_ann_ty),
                    self.pretty_value(&dom_ty),
                ));
            }
        }
        let body_tm = {
            let prev = self.bind(param_sym, dom_ty);
            let param_v = self.env().nth(0);
            let rng_ty = apply_closure(rng, param_v);
            let result = self.elab_exp_check(lam.body, rng_ty);
            self.unbind(prev);
            result?
        };
        Ok(core_syntax::lam(param_sym, body_tm))
    }

    fn elab_arr(&mut self, arr: &pst::Arrow<'_, '_>) -> Result<TermBox> {
        let dom = self.elab_exp_check(arr.dom, self.type_type())?;
        let dom_ty = evaluate(self.env(), dom.clone());
        match arr.param {
            Some(param) => {
                let param_sym = param.name.intern(&self.intern_pool);
                let rng = {
                    let prev = self.bind(param_sym, dom_ty);
                    let result = self.elab_exp_check(arr.rng, self.type_type());
                    self.unbind(prev);
                    result?
                };
                Ok(core_syntax::pi(dom, param_sym, rng))
            }
            None => {
                let rng = {
                    self.scope_depth += 1;
                    //self.bind_without_name(None);
                    let result = self.elab_exp_check(arr.rng, self.type_type());
                    self.scope_depth -= 1;
                    //self.unbind(None);
                    result?
                };
                Ok(core_syntax::pi(dom, Symbol::UNDERSCORE, rng))
            }
        }
    }

    fn lookup(&self, name: pst::Name) -> Result<(TermBox, Type)> {
        let sym = name.intern(&self.intern_pool);
        if let Some(binding) = self.scope.get(&sym) {
            let idx = self.scope_depth - binding.level;
            return Ok((core_syntax::var(idx), binding.ty.clone()));
        }
        if let Some(con_ty) = self.constants.get(&sym) {
            return Ok((core_syntax::con(sym), con_ty.clone()));
        }
        Err(Error::NotDefined(name.loc, name.id.to_string()))
    }

    fn bind(&mut self, sym: Symbol, ty: Type) -> Option<Binding> {
        self.scope_depth += 1;
        let binding = Binding {
            sym,
            ty,
            level: self.scope_depth,
        };
        self.scope.insert(binding.sym, binding)
    }

    fn unbind(&mut self, prev: Option<Binding>) {
        self.scope_depth -= 1;
        if let Some(prev_binding) = prev {
            self.scope.insert(prev_binding.sym, prev_binding);
        }
    }

    fn compatible(&self, t1: &Type, t2: &Type) -> bool {
        let tm1 = reify(self.scope_depth, t1);
        let tm2 = reify(self.scope_depth, t2);
        tm1.alpha_eq(&tm2)
    }

    pub fn pretty_term(&self, tm: &Term) -> String {
        // TODO: pass context to .display() to populate names
        tm.display(&self.intern_pool).to_string()
    }

    pub fn pretty_value(&self, v: &Val) -> String {
        let tm = reify(self.scope_depth, v);
        self.pretty_term(&tm)
    }
}

fn reify(level: usize, v: &Val) -> TermBox {
    // TODO: type-based reification for proper eta-expansion
    match v {
        Val::Con(c, vs) => {
            let mut tm = core_syntax::con(*c);
            for v in vs {
                let arg = reify(level, v);
                tm = core_syntax::app(tm, arg);
            }
            tm
        }
        Val::NeVar(l) => core_syntax::var(level - l),
        Val::NeApp(fun, arg) => {
            let fun_tm = reify(level, fun);
            let arg_tm = reify(level, arg);
            core_syntax::app(fun_tm, arg_tm)
        }
        Val::Pi(dom, rng) => {
            let dom_tm = reify(level, dom);
            let rng_v = apply_closure(rng, value::neutral(level + 1));
            let rng_tm = reify(level + 1, &rng_v);
            core_syntax::pi(dom_tm, rng.sym, rng_tm)
        }
        Val::Fun(fun) => {
            let body_v = apply_closure(fun, value::neutral(level + 1));
            let body_tm = reify(level + 1, &body_v);
            core_syntax::lam(fun.sym, body_tm)
        }
    }
}
