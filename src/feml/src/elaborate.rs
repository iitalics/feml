use crate::core_syntax::{self, Constant, TermBox};
use crate::evaluate::{apply_closure, evaluate};
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
            | Self::NotFunction(loc, _)
            | Self::NoLambdaInfer(loc, _) => *loc,
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct Context<'e> {
    scope: HashMap<&'e str, Binding<'e>>,
    scope_depth: usize,
}

pub type Type<'e> = ValBox<'e>;

struct Binding<'e> {
    ty: Type<'e>,
    // level = (scope_depth - debruijn_index). this value is stable as new bindings are
    // introduced and can be used to obtain the correct debruijn index by subtracting from
    // scope_depth again.
    level: usize,
}

fn look_up_in_global_env(x: &str) -> Option<Constant> {
    match x {
        "S" => Some(Constant::S),
        "Z" => Some(Constant::Z),
        "nat" => Some(Constant::TypeNat),
        "type" => Some(Constant::TypeType),
        _ => None,
    }
}

impl<'e> Context<'e> {
    pub fn new() -> Self {
        Self {
            scope: HashMap::with_capacity(32),
            scope_depth: 0,
        }
    }

    fn env(&self) -> value::Env<'e> {
        value::env_neutral(self.scope_depth)
    }

    pub fn elab_exp_infer(&mut self, exp: &pst::Exp<'e, '_>) -> Result<(TermBox<'e>, Type<'e>)> {
        match exp {
            pst::Exp::Var(x) => self.lookup(*x),
            pst::Exp::App(fun, arg) => self.elab_app_infer(fun, arg),
            pst::Exp::Lam(lam) => self.elab_lam_infer(lam),
            pst::Exp::Arr(arr) => self.elab_arr(arr).map(|t| (t, value::type_type())),
            pst::Exp::Mat { .. } => unimplemented!("match expressions"),
        }
    }

    pub fn elab_exp_check(&mut self, exp: &pst::Exp<'e, '_>, ty: Type<'e>) -> Result<TermBox<'e>> {
        match exp {
            pst::Exp::Lam(lam) => self.elab_lam_check(lam, ty),
            _ => {
                // no special checking rule, fall back to inference
                let (stx, inf_ty) = self.elab_exp_infer(exp)?;
                if !compatible(&inf_ty, &ty) {
                    return Err(Error::TypeMismatch(
                        exp.loc(),
                        ty.to_string(),
                        inf_ty.to_string(),
                    ));
                }
                Ok(stx)
            }
        }
    }

    pub fn elab_type(&mut self, ty_exp: &pst::Exp<'e, '_>) -> Result<Type<'e>> {
        let ty_tm = self.elab_exp_check(ty_exp, value::type_type())?;
        let ty = evaluate(self.env(), ty_tm);
        Ok(ty)
    }

    fn elab_app_infer(
        &mut self,
        fun: &pst::Exp<'e, '_>,
        arg: &pst::Arg<'e, '_>,
    ) -> Result<(TermBox<'e>, Type<'e>)> {
        let (fun_tm, fun_ty) = self.elab_exp_infer(fun)?;
        let (dom_ty, rng) = match &*fun_ty {
            Val::Pi(dom_ty, rng) => (dom_ty.clone(), rng),
            _ => return Err(Error::NotFunction(fun.loc(), fun_ty.to_string())),
        };
        let arg_tm = self.elab_exp_check(arg, dom_ty)?;
        let arg = evaluate(self.env(), arg_tm.clone());
        let ret_ty = apply_closure(rng, arg);
        Ok((core_syntax::app(fun_tm, arg_tm), ret_ty))
    }

    fn elab_lam_infer(&mut self, lam: &pst::Lambda<'e, '_>) -> Result<(TermBox<'e>, Type<'e>)> {
        let arg_id = lam.name.id;
        let arg_ty = match lam.param {
            Some(param) => self.elab_type(param.ty)?,
            None => return Err(Error::NoLambdaInfer(lam.name.loc, lam.name.to_string())),
        };
        let (body_tm, ret_ty) = {
            let prev = self.bind(arg_id, arg_ty.clone());
            let result = self.elab_exp_infer(lam.body);
            self.unbind(arg_id, prev);
            result?
        };
        let ret = core_syntax::Abs {
            id: arg_id,
            body: reify(self.scope_depth + 1, &ret_ty),
        };
        Ok((
            core_syntax::lam(arg_id, body_tm),
            value::pi(arg_ty, ret, self.env()),
        ))
    }

    fn elab_lam_check(&mut self, lam: &pst::Lambda<'e, '_>, ty: Type<'e>) -> Result<TermBox<'e>> {
        let arg_id = lam.name.id;
        let (dom_ty, rng) = match &*ty {
            Val::Pi(dom_ty, rng) => (dom_ty.clone(), rng),
            _ => return Err(Error::NotFunction(lam.loc(), ty.to_string())),
        };
        if let Some(param) = lam.param {
            let arg_ann_ty = self.elab_type(param.ty)?;
            if !compatible(&dom_ty, &arg_ann_ty) {
                return Err(Error::TypeMismatch(
                    param.ty.loc(),
                    arg_ann_ty.to_string(),
                    dom_ty.to_string(),
                ));
            }
        }
        let body_tm = {
            let prev = self.bind(arg_id, dom_ty);
            let arg_v = self.env().nth(0);
            let rng_ty = apply_closure(rng, arg_v);
            let result = self.elab_exp_check(lam.body, rng_ty);
            self.unbind(arg_id, prev);
            result?
        };
        Ok(core_syntax::lam(arg_id, body_tm))
    }

    fn elab_arr(&mut self, arr: &pst::Arrow<'e, '_>) -> Result<TermBox<'e>> {
        let dom = self.elab_exp_check(arr.dom, value::type_type())?;
        let dom_ty = evaluate(self.env(), dom.clone());
        match arr.param {
            Some(param) => {
                let dom_id = param.name.id;
                let rng = {
                    let prev = self.bind(dom_id, dom_ty);
                    let result = self.elab_exp_check(arr.rng, value::type_type());
                    self.unbind(dom_id, prev);
                    result?
                };
                Ok(core_syntax::pi(dom, dom_id, rng))
            }
            None => {
                let rng = {
                    self.scope_depth += 1;
                    let result = self.elab_exp_check(arr.rng, value::type_type());
                    self.scope_depth -= 1;
                    result?
                };
                Ok(core_syntax::pi(dom, "_", rng))
            }
        }
    }

    fn lookup(&self, name: pst::Name<'e>) -> Result<(TermBox<'e>, Type<'e>)> {
        if let Some(binding) = self.scope.get(&name.id) {
            let idx = self.scope_depth - binding.level;
            return Ok((core_syntax::var(idx), binding.ty.clone()));
        }
        if let Some(c) = look_up_in_global_env(name.id) {
            return Ok((core_syntax::cst(c), constant_type(c)));
        }
        Err(Error::NotDefined(name.loc, name.id.to_string()))
    }

    fn bind(&mut self, id: &'e str, ty: Type<'e>) -> Option<Binding<'e>> {
        self.scope_depth += 1;
        let binding = Binding {
            level: self.scope_depth,
            ty,
        };
        self.scope.insert(id, binding)
    }

    fn unbind(&mut self, id: &'e str, prev: Option<Binding<'e>>) {
        self.scope_depth -= 1;
        if let Some(prev_binding) = prev {
            self.scope.insert(id, prev_binding);
        }
    }
}

fn constant_type(c: Constant) -> Type<'static> {
    match c {
        Constant::Z => value::type_nat(),
        Constant::S => value::arrow(value::type_nat(), value::type_nat()),
        Constant::TypeNat => value::type_type(),
        Constant::TypeType => value::type_type(),
    }
}

fn compatible(t1: &Type<'_>, t2: &Type<'_>) -> bool {
    match (&**t1, &**t2) {
        (Val::TypeType, Val::TypeType) => true,
        (Val::TypeType, _) | (_, Val::TypeType) => false,
        (Val::TypeNat, Val::TypeNat) => true,
        (Val::TypeNat, _) | (_, Val::TypeNat) => false,
        (Val::Neu(x), Val::Neu(y)) => x == y,
        (Val::Neu(_), _) | (_, Val::Neu(_)) => false,
        (_, _) => {
            eprintln!("*TODO* {t1} \u{2264}? {t2}");
            true
        }
    }
}

fn reify<'e>(level: usize, v: &Val<'e>) -> TermBox<'e> {
    match v {
        Val::TypeType => core_syntax::cst(Constant::TypeType),
        Val::TypeNat => core_syntax::cst(Constant::TypeNat),
        Val::CtorS => core_syntax::cst(Constant::S),
        Val::Neu(l) => core_syntax::var(level - l),
        Val::Nat(n) => {
            // FIXME: lol. should just have nat constants instead of this
            let mut tm = core_syntax::cst(Constant::Z);
            let mut s = None;
            for _ in 0..*n {
                let s = s.get_or_insert_with(|| core_syntax::cst(Constant::S));
                tm = core_syntax::app(s.clone(), tm);
            }
            tm
        }
        Val::Pi(dom, rng) => {
            let dom_tm = reify(level, dom);
            let rng_v = apply_closure(rng, value::neu(level + 1));
            let rng_tm = reify(level + 1, &rng_v);
            core_syntax::pi(dom_tm, rng.id, rng_tm)
        }
        Val::Fun(fun) => {
            let body_v = apply_closure(fun, value::neu(level + 1));
            let body_tm = reify(level + 1, &body_v);
            core_syntax::lam(fun.id, body_tm)
        }
    }
}
