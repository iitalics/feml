use crate::core_syntax as stx;
use crate::parse_tree as pst;
use crate::token::Loc;

use std::collections::HashMap;

#[derive(Debug)]
pub enum Error {
    NotDefined(Loc, String),
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct Context<'s> {
    // maps binding names to (scope_depth - debruijn_index). this value is stable as new
    // bindings are introduced and can be used to obtain the correct debruijn index by
    // subtracting from scope_depth again.
    scope: HashMap<&'s str, usize>,
    scope_depth: usize,
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

    pub fn elab_exp(&mut self, exp: &pst::Exp<'s, '_>) -> Result<Box<stx::Exp<'s>>> {
        match exp {
            pst::Exp::Var(x) => self.lookup(*x).map(Box::new),
            pst::Exp::App(fun, arg) => self.elab_app(fun, arg).map(Box::new),
            pst::Exp::Lam(lam) => self.elab_lam(lam).map(Box::new),
            pst::Exp::Arr { .. } => unimplemented!("elab Arr"),
            pst::Exp::Mat { .. } => unimplemented!("elab Mat"),
        }
    }

    fn lookup(&self, name: pst::Name<'s>) -> Result<stx::Exp<'s>> {
        if let Some(&lvl) = self.scope.get(&name.id) {
            let idx = self.scope_depth - lvl;
            return Ok(stx::Exp::Var(idx));
        }
        match look_up_in_global_env(name.id) {
            Some(cst) => Ok(stx::Exp::Const(cst)),
            None => Err(Error::NotDefined(name.loc, name.id.to_string())),
        }
    }

    fn bind(&mut self, id: &'s str) -> Option<usize> {
        self.scope_depth += 1;
        self.scope.insert(id, self.scope_depth)
    }

    fn unbind(&mut self, id: &'s str, prev: Option<usize>) {
        self.scope_depth -= 1;
        if let Some(prev_lvl) = prev {
            self.scope.insert(id, prev_lvl);
        }
    }

    fn elab_app(&mut self, fun: &pst::Exp<'s, '_>, arg: &pst::Arg<'s, '_>) -> Result<stx::Exp<'s>> {
        let fun_stx = self.elab_exp(fun)?;
        let arg_stx = self.elab_exp(arg)?;
        Ok(stx::Exp::App(fun_stx, arg_stx))
    }

    fn elab_lam(&mut self, lam: &pst::Lambda<'s, '_>) -> Result<stx::Exp<'s>> {
        let id = lam.name.id;
        let prev = self.bind(id);
        let body_stx_result = self.elab_exp(lam.body);
        self.unbind(id, prev);
        Ok(stx::Exp::Abs(id, body_stx_result?))
    }
}
