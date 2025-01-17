use crate::core_syntax as stx;
use crate::parse_tree as pst;
use crate::token::Loc;

use std::collections::HashMap;
use std::fmt;

#[derive(Debug)]
pub enum Error {
    NotDefined(Loc, String),
    TypeMismatch(Loc, String, String),
    TypeNotArrow(Loc, String),
    NoLambdaInfer(Loc, String),
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

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotDefined(_, x) => write!(f, "{x} not defined"),
            Self::TypeMismatch(_, t, s) => write!(f, "expected {t}, got {s}"),
            Self::TypeNotArrow(_, s) => write!(f, "expected function type, got {s}"),
            Self::NoLambdaInfer(_, id) => write!(f, "unable to infer type for {id}"),
            Self::InvalidType(_, e) => write!(f, "invalid type expression {e}"),
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct Context<'s> {
    scope: HashMap<&'s str, Binding>,
    scope_depth: usize,
}

struct Binding {
    // a binding level (scope_depth - debruijn_index). this value is stable as new
    // bindings are introduced and can be used to obtain the correct debruijn index by
    // subtracting from scope_depth again.
    level: usize,
    ty: stx::Type,
}

fn look_up_in_global_env(x: &str) -> Option<stx::Constant> {
    match x {
        "S" => Some(stx::Constant::S),
        "Z" => Some(stx::Constant::Z),
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
    ) -> Result<(Box<stx::Exp<'s>>, stx::Type)> {
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
        ty: &stx::Ty,
    ) -> Result<Box<stx::Exp<'s>>> {
        match exp {
            pst::Exp::Lam(lam) if lam.param.is_none() => self.elab_lam_check(lam, ty),
            _ => {
                let (stx, inf_ty) = self.elab_exp_infer(exp)?;
                if !inf_ty.compatible(ty) {
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
    ) -> Result<(Box<stx::Exp<'s>>, stx::Type)> {
        let (fun_stx, fun_ty) = self.elab_exp_infer(fun)?;
        let (arg_ty, ret_ty) = match &*fun_ty {
            stx::Ty::Arr(dom, rng) => (dom, rng),
            _ => return Err(Error::TypeNotArrow(fun.loc(), fun_ty.to_string())),
        };
        let arg_stx = self.elab_exp_check(arg, arg_ty)?;
        Ok((Box::new(stx::Exp::App(fun_stx, arg_stx)), ret_ty.clone()))
    }

    fn elab_lam_infer(
        &mut self,
        lam: &pst::Lambda<'s, '_>,
    ) -> Result<(Box<stx::Exp<'s>>, stx::Type)> {
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
        let lam = Box::new(stx::Exp::Abs(arg_id, body_stx));
        let ty = stx::Type::new(stx::Ty::Arr(arg_ty, body_ty));
        Ok((lam, ty))
    }

    fn elab_lam_check(
        &mut self,
        lam: &pst::Lambda<'s, '_>,
        ty: &stx::Ty,
    ) -> Result<Box<stx::Exp<'s>>> {
        let arg_id = lam.name.id;
        let (arg_ty, ret_ty) = match ty {
            stx::Ty::Arr(dom, rng) => (dom, rng),
            _ => return Err(Error::TypeNotArrow(lam.loc(), ty.to_string())),
        };
        if let Some(param) = lam.param {
            let arg_ann_ty = self.elab_ty(param.ty)?;
            if !ty.compatible(&arg_ann_ty) {
                return Err(Error::TypeMismatch(
                    param.loc(),
                    arg_ann_ty.to_string(),
                    ty.to_string(),
                ));
            }
        }
        let body_stx = {
            let prev = self.bind(arg_id, arg_ty.clone());
            let result = self.elab_exp_check(&lam.body, ret_ty);
            self.unbind(arg_id, prev);
            result?
        };
        Ok(Box::new(stx::Exp::Abs(arg_id, body_stx)))
    }

    fn lookup(&self, name: pst::Name<'s>) -> Result<(Box<stx::Exp<'s>>, stx::Type)> {
        if let Some(binding) = self.scope.get(&name.id) {
            let idx = self.scope_depth - binding.level;
            let var = Box::new(stx::Exp::Var(idx));
            let ty = binding.ty.clone();
            return Ok((var, ty));
        }

        if let Some(c) = look_up_in_global_env(name.id) {
            // Some(cst) => Ok(stx::Exp::Const(cst)),
            // None => ,
            let cst = Box::new(stx::Exp::Const(c));
            let ty = c.get_type();
            return Ok((cst, ty));
        }

        Err(Error::NotDefined(name.loc, name.id.to_string()))
    }

    fn bind(&mut self, id: &'s str, ty: stx::Type) -> Option<Binding> {
        self.scope_depth += 1;
        self.scope.insert(
            id,
            Binding {
                level: self.scope_depth,
                ty,
            },
        )
    }

    fn unbind(&mut self, id: &'s str, prev: Option<Binding>) {
        self.scope_depth -= 1;
        if let Some(prev_binding) = prev {
            self.scope.insert(id, prev_binding);
        }
    }

    pub fn elab_ty(&mut self, tyexp: &pst::Ty<'s, '_>) -> Result<stx::Type> {
        match tyexp {
            pst::Exp::Var(name) if name.id == "nat" => Ok(stx::Type::new(stx::Ty::Nat)),
            pst::Exp::Arr(arr) if arr.param.is_none() => {
                let dom = self.elab_ty(arr.dom)?;
                let rng = self.elab_ty(arr.rng)?;
                Ok(stx::Type::new(stx::Ty::Arr(dom, rng)))
            }
            _ => Err(Error::InvalidType(tyexp.loc(), tyexp.to_string())),
        }
    }
}
