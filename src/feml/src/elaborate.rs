use crate::core_syntax::{self, Constant, TermBox};
use crate::parse_tree as pst;
use crate::token::Loc;
use crate::value::{self, Type, Val};

use std::collections::HashMap;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("{1} not defined")]
    NotDefined(Loc, String),
    #[error("expected {1}, got {2}")]
    TypeMismatch(Loc, String, String),
    #[error("expected function type, got {1}")]
    TypeNotArrow(Loc, String),
    #[error("unable to infer type for {1}")]
    NoLambdaInfer(Loc, String),
    #[error("invalid type expression: {1}")]
    InvalidType(Loc, String),
}

impl Error {
    pub fn loc(&self) -> Loc {
        match self {
            Self::NotDefined(loc, _)
            | Self::TypeMismatch(loc, _, _)
            | Self::TypeNotArrow(loc, _)
            | Self::NoLambdaInfer(loc, _)
            | Self::InvalidType(loc, _) => *loc,
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct Context<'e> {
    scope: HashMap<&'e str, Binding>,
    scope_depth: usize,
}

struct Binding {
    ty: Type,
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

impl<'s> Context<'s> {
    pub fn new() -> Self {
        Self {
            scope: HashMap::with_capacity(32),
            scope_depth: 0,
        }
    }

    pub fn elab_exp_infer(&mut self, exp: &pst::Exp<'s, '_>) -> Result<(TermBox<'s>, Type)> {
        match exp {
            pst::Exp::Var(x) => self.lookup(*x),
            pst::Exp::App(fun, arg) => self.elab_app_infer(fun, arg),
            pst::Exp::Lam(lam) => self.elab_lam_infer(lam),
            pst::Exp::Arr { .. } => unimplemented!("elab Arr"),
            pst::Exp::Mat { .. } => unimplemented!("elab Mat"),
        }
    }

    pub fn elab_exp_check(&mut self, exp: &pst::Exp<'s, '_>, ty: Type) -> Result<TermBox<'s>> {
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

    fn elab_app_infer(
        &mut self,
        fun: &pst::Exp<'s, '_>,
        arg: &pst::Arg<'s, '_>,
    ) -> Result<(TermBox<'s>, Type)> {
        let (fun_tm, fun_ty) = self.elab_exp_infer(fun)?;
        let (arg_ty, ret_ty) = assert_arrow_type(fun.loc(), fun_ty)?;
        let arg_tm = self.elab_exp_check(arg, arg_ty)?;
        Ok((core_syntax::app(fun_tm, arg_tm), ret_ty))
    }

    fn elab_lam_infer(&mut self, lam: &pst::Lambda<'s, '_>) -> Result<(TermBox<'s>, Type)> {
        let arg_id = lam.name.id;
        let arg_ty = match lam.param {
            Some(param) => self.elab_ty(param.ty)?,
            None => return Err(Error::NoLambdaInfer(lam.name.loc, lam.name.to_string())),
        };
        let (body_tm, body_ty) = {
            let prev = self.bind(arg_id, arg_ty.clone());
            let result = self.elab_exp_infer(&lam.body);
            self.unbind(arg_id, prev);
            result?
        };
        Ok((
            core_syntax::lam(arg_id, body_tm),
            value::arrow(arg_ty, body_ty),
        ))
    }

    fn elab_lam_check(&mut self, lam: &pst::Lambda<'s, '_>, ty: Type) -> Result<TermBox<'s>> {
        let arg_id = lam.name.id;
        let (arg_ty, ret_ty) = assert_arrow_type(lam.loc(), ty)?;
        if let Some(param) = lam.param {
            let arg_ann_ty = self.elab_ty(param.ty)?;
            if !compatible(&arg_ty, &arg_ann_ty) {
                return Err(Error::TypeMismatch(
                    param.ty.loc(),
                    arg_ann_ty.to_string(),
                    arg_ty.to_string(),
                ));
            }
        }
        let body_tm = {
            let prev = self.bind(arg_id, arg_ty);
            let result = self.elab_exp_check(&lam.body, ret_ty);
            self.unbind(arg_id, prev);
            result?
        };
        Ok(core_syntax::lam(arg_id, body_tm))
    }

    fn lookup(&self, name: pst::Name<'s>) -> Result<(TermBox<'s>, Type)> {
        if let Some(binding) = self.scope.get(&name.id) {
            let idx = self.scope_depth - binding.level;
            return Ok((core_syntax::var(idx), binding.ty.clone()));
        }
        if let Some(c) = look_up_in_global_env(name.id) {
            return Ok((core_syntax::cst(c), constant_type(c)));
        }
        Err(Error::NotDefined(name.loc, name.id.to_string()))
    }

    fn bind(&mut self, id: &'s str, ty: Type) -> Option<Binding> {
        self.scope_depth += 1;
        let binding = Binding {
            level: self.scope_depth,
            ty,
        };
        self.scope.insert(id, binding)
    }

    fn unbind(&mut self, id: &'s str, prev: Option<Binding>) {
        self.scope_depth -= 1;
        if let Some(prev_binding) = prev {
            self.scope.insert(id, prev_binding);
        }
    }

    pub fn elab_ty(&mut self, tyexp: &pst::Exp<'s, '_>) -> Result<Type> {
        match tyexp {
            pst::Exp::Var(n) if n.id == "nat" => Ok(value::type_nat()),
            pst::Exp::Var(n) if n.id == "type" => Ok(value::type_type()),
            pst::Exp::Arr(arr) if arr.param.is_none() => {
                let dom = self.elab_ty(&arr.dom)?;
                let rng = self.elab_ty(&arr.rng)?;
                Ok(value::arrow(dom, rng))
            }
            _ => Err(Error::InvalidType(tyexp.loc(), tyexp.to_string())),
        }
    }
}

fn constant_type(c: Constant) -> Type {
    match c {
        Constant::Z => value::type_nat(),
        Constant::S => value::arrow(value::type_nat(), value::type_nat()),
        Constant::TypeNat => value::type_type(),
        Constant::TypeType => value::type_type(),
    }
}

fn assert_arrow_type<'e>(loc: Loc, t: Type) -> Result<(Type, Type)> {
    match &*t {
        Val::Arrow(dom, rng) => Ok((dom.clone(), rng.clone())),
        _ => Err(Error::TypeNotArrow(loc, t.to_string())),
    }
}

fn compatible(t1: &Type, t2: &Type) -> bool {
    match (&**t1, &**t2) {
        (Val::TypeType, Val::TypeType) => true,
        (Val::TypeNat, Val::TypeNat) => true,
        (Val::Arrow(dom1, rng1), Val::Arrow(dom2, rng2)) => {
            if !compatible(dom2, dom1) {
                return false;
            }
            compatible(rng1, rng2)
        }
        (_, _) => false,
    }
}
