use crate::core_syntax as stx;
use crate::parse_tree as pst;
use crate::token::Loc;
use crate::value as val;

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
    ty: val::Type,
    // level = (scope_depth - debruijn_index). this value is stable as new bindings are
    // introduced and can be used to obtain the correct debruijn index by subtracting from
    // scope_depth again.
    level: usize,
}

fn look_up_in_global_env(x: &str) -> Option<stx::Constant> {
    match x {
        "S" => Some(stx::Constant::S),
        "Z" => Some(stx::Constant::Z),
        "nat" => Some(stx::Constant::TypeNat),
        "type" => Some(stx::Constant::TypeType),
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

    pub fn elab_exp_infer(
        &mut self,
        exp: &pst::Exp<'s, '_>,
    ) -> Result<(stx::Exp<'s>, val::Type)> {
        match exp {
            pst::Exp::Var(x) => self.lookup(*x),
            pst::Exp::App(fun, arg) => self.elab_app_infer(fun, arg),
            pst::Exp::Lam(lam) => self.elab_lam_infer(lam),
            pst::Exp::Arr { .. } => unimplemented!("elab Arr"),
            pst::Exp::Mat { .. } => unimplemented!("elab Mat"),
        }
    }

    pub fn elab_exp_check(
        &mut self,
        exp: &pst::Exp<'s, '_>,
        ty: val::Type,
    ) -> Result<stx::Exp<'s>> {
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
    ) -> Result<(stx::Exp<'s>, val::Type)> {
        let (fun_stx, fun_ty) = self.elab_exp_infer(fun)?;
        let (arg_ty, ret_ty) = assert_arrow_type(fun.loc(), fun_ty)?;
        let arg_stx = self.elab_exp_check(arg, arg_ty)?;
        let app = Box::new(stx::Ex::App(fun_stx, arg_stx));
        Ok((app, ret_ty))
    }

    fn elab_lam_infer(
        &mut self,
        lam: &pst::Lambda<'s, '_>,
    ) -> Result<(stx::Exp<'s>, val::Type)> {
        let arg_id = lam.name.id;
        let arg_ty = match lam.param {
            Some(param) => self.elab_ty(param.ty)?,
            None => return Err(Error::NoLambdaInfer(lam.name.loc, lam.name.to_string())),
        };
        let (body_stx, body_ty) = {
            let prev = self.bind(arg_id, arg_ty.clone());
            let result = self.elab_exp_infer(&lam.body);
            self.unbind(arg_id, prev);
            result?
        };
        let lam = stx::Lam(arg_id, body_stx);
        let lam = Box::new(stx::Ex::Lam(lam));
        let ty = val::arrow(arg_ty, body_ty);
        Ok((lam, ty))
    }

    fn elab_lam_check(
        &mut self,
        lam: &pst::Lambda<'s, '_>,
        ty: val::Type,
    ) -> Result<stx::Exp<'s>> {
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
        let body_stx = {
            let prev = self.bind(arg_id, arg_ty);
            let result = self.elab_exp_check(&lam.body, ret_ty);
            self.unbind(arg_id, prev);
            result?
        };
        let lam = stx::Lam(arg_id, body_stx);
        Ok(Box::new(stx::Ex::Lam(lam)))
    }

    fn lookup(&self, name: pst::Name<'s>) -> Result<(stx::Exp<'s>, val::Type)> {
        if let Some(binding) = self.scope.get(&name.id) {
            let idx = self.scope_depth - binding.level;
            let var = Box::new(stx::Ex::Var(idx));
            let ty = binding.ty.clone();
            return Ok((var, ty));
        }
        if let Some(c) = look_up_in_global_env(name.id) {
            let cst = Box::new(stx::Ex::Cst(c));
            let ty = constant_type(c);
            return Ok((cst, ty));
        }
        Err(Error::NotDefined(name.loc, name.id.to_string()))
    }

    fn bind(&mut self, id: &'s str, ty: val::Type) -> Option<Binding> {
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

    pub fn elab_ty(&mut self, tyexp: &pst::Exp<'s, '_>) -> Result<val::Type> {
        match tyexp {
            pst::Exp::Var(n) if n.id == "nat" => Ok(val::type_nat()),
            pst::Exp::Var(n) if n.id == "type" => Ok(val::type_type()),
            pst::Exp::Arr(arr) if arr.param.is_none() => {
                let dom = self.elab_ty(&arr.dom)?;
                let rng = self.elab_ty(&arr.rng)?;
                Ok(val::arrow(dom, rng))
            }
            _ => Err(Error::InvalidType(tyexp.loc(), tyexp.to_string())),
        }
    }
}

fn constant_type(c: stx::Constant) -> val::Type {
    match c {
        stx::Constant::Z => val::type_nat(),
        stx::Constant::S => val::arrow(val::type_nat(), val::type_nat()),
        stx::Constant::TypeNat => val::type_type(),
        stx::Constant::TypeType => val::type_type(),
    }
}

fn assert_arrow_type<'e>(loc: Loc, t: val::Type) -> Result<(val::Type, val::Type)> {
    match &*t {
        val::Va::Arrow(dom, rng) => Ok((dom.clone(), rng.clone())),
        _ => Err(Error::TypeNotArrow(loc, t.to_string())),
    }
}

fn compatible(t1: &val::Type, t2: &val::Type) -> bool {
    match (&**t1, &**t2) {
        (val::Va::TypeType, val::Va::TypeType) => true,
        (val::Va::TypeNat, val::Va::TypeNat) => true,
        (val::Va::Arrow(dom1, rng1), val::Va::Arrow(dom2, rng2)) => {
            if !compatible(dom2, dom1) {
                return false;
            }
            compatible(rng1, rng2)
        }
        (_, _) => false,
    }
}
