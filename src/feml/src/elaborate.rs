use crate::core_syntax::{self, Term, TermBox};
use crate::evaluate::{apply_closure, evaluate};
use crate::intern::{self, Symbol};
use crate::parse_tree as pst;
use crate::token::Loc;
use crate::value::{self, Level, Val, ValBox};

use std::collections::HashMap;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("{1} not in scope")]
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
    scope: Vec<Binding>,
}

pub type Type = ValBox;

struct Binding {
    sym: Option<Symbol>,
    ty: Type,
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
            scope: vec![],
        }
    }

    fn type_type(&self) -> Type {
        self.type_type.clone()
    }

    fn level(&self) -> Level {
        self.scope.len()
    }

    fn env(&self) -> value::Env {
        value::env_neutral(self.level())
    }

    fn scope_find(&self, sym: Symbol) -> Option<(&Binding, Level)> {
        for (idx, binding) in self.scope.iter().enumerate().rev() {
            if binding.sym == Some(sym) {
                return Some((binding, idx + 1));
            }
        }
        None
    }

    fn scope_intro(&mut self, sym: Option<Symbol>, ty: Type) -> Level {
        self.scope.push(Binding { sym, ty });
        self.scope.len()
    }

    fn scope_exit(&mut self) {
        let binding = self.scope.pop();
        assert!(binding.is_some());
    }

    pub fn elab_exp_infer(&mut self, exp: &pst::Exp<'_, '_>) -> Result<(TermBox, Type)> {
        match exp {
            pst::Exp::Var(x) => self.elab_var(*x),
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

    fn elab_var(&self, name: pst::Name) -> Result<(TermBox, Type)> {
        let sym = name.intern(&self.intern_pool);
        if let Some((binding, lvl)) = self.scope_find(sym) {
            let idx = self.level() - lvl;
            return Ok((core_syntax::var(idx), binding.ty.clone()));
        }
        if let Some(con_ty) = self.constants.get(&sym) {
            return Ok((core_syntax::con(sym), con_ty.clone()));
        }
        Err(Error::NotDefined(name.loc, name.id.to_string()))
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
        let (level, (body_tm, ret_ty)) = {
            self.scope_intro(Some(param_sym), param_ty.clone());
            let result = self.elab_exp_infer(lam.body);
            let level = self.level();
            self.scope_exit();
            (level, result?)
        };
        let ret = core_syntax::Abs {
            param: param_sym,
            body: reify(level, &ret_ty),
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
            self.scope_intro(Some(param_sym), dom_ty);
            let rng_ty = apply_closure(rng, value::neutral(self.level()));
            let result = self.elab_exp_check(lam.body, rng_ty);
            self.scope_exit();
            result?
        };
        Ok(core_syntax::lam(param_sym, body_tm))
    }

    fn elab_arr(&mut self, arr: &pst::Arrow<'_, '_>) -> Result<TermBox> {
        let dom = self.elab_exp_check(arr.dom, self.type_type())?;
        let dom_ty = evaluate(self.env(), dom.clone());
        let param_sym = arr.param.map(|param| param.name.intern(&self.intern_pool));
        let rng = {
            self.scope_intro(param_sym, dom_ty);
            let result = self.elab_exp_check(arr.rng, self.type_type());
            self.scope_exit();
            result?
        };
        Ok(core_syntax::pi(
            dom,
            param_sym.unwrap_or(Symbol::UNDERSCORE),
            rng,
        ))
    }

    fn compatible(&self, t1: &Type, t2: &Type) -> bool {
        let tm1 = reify(self.level(), t1);
        let tm2 = reify(self.level(), t2);
        tm1.alpha_eq(&tm2)
    }

    pub fn pretty_term(&self, tm: &Term) -> String {
        let scope = self.scope.iter();
        let context = scope
            .map(|binding| binding.sym.unwrap_or(Symbol::UNDERSCORE))
            .collect::<Vec<Symbol>>();
        tm.display(&self.intern_pool, &context).to_string()
    }

    pub fn pretty_value(&self, v: &Val) -> String {
        let tm = reify(self.level(), v);
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
