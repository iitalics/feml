use crate::core_syntax as stx;
use crate::parse_tree as pst;
use crate::parse_tree::{ExpHnd, Name};
use crate::token::Loc;

use std::collections::HashMap;

#[derive(Debug)]
pub enum Error {
    NotDefined(Loc, String),
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct Context<'p, 's> {
    parse_tree: &'p pst::ParseTree<'s>,
    env: HashMap<&'s str, usize>,
    depth: usize,
}

fn look_up_in_global_env(x: &str) -> Option<stx::Constant> {
    match x {
        "S" => Some(stx::Constant::S),
        "Z" => Some(stx::Constant::Z),
        _ => None,
    }
}

impl<'p, 's> Context<'p, 's> {
    pub fn new(parse_tree: &'p pst::ParseTree<'s>) -> Self {
        Self {
            parse_tree,
            env: HashMap::with_capacity(32),
            depth: 0,
        }
    }

    pub fn elab_exp(&mut self, exp: ExpHnd) -> Result<Box<stx::Exp<'s>>> {
        match self.parse_tree.view_exp(exp) {
            pst::Exp::Var(x) => self.lookup(*x).map(Box::new),
            pst::Exp::App(fun, arg) => self.elab_app(*fun, *arg).map(Box::new),
            pst::Exp::Lam(lam) => self.elab_lam(lam.name, lam.body).map(Box::new),
            pst::Exp::Arr { .. } => unimplemented!("elab Arr"),
            pst::Exp::Mat { .. } => unimplemented!("elab Mat"),
        }
    }

    fn lookup(&self, name: Name<'s>) -> Result<stx::Exp<'s>> {
        if let Some(&lvl) = self.env.get(&name.id) {
            let idx = self.depth - lvl - 1;
            return Ok(stx::Exp::Var(idx));
        }
        match look_up_in_global_env(name.id) {
            Some(cst) => Ok(stx::Exp::Const(cst)),
            None => Err(Error::NotDefined(name.loc, name.id.to_string())),
        }
    }

    fn bind(&mut self, id: &'s str) -> Option<usize> {
        let lvl = self.depth;
        self.depth += 1;
        self.env.insert(id, lvl)
    }

    fn unbind(&mut self, id: &'s str, prev: Option<usize>) {
        self.depth -= 1;
        if let Some(prev_lvl) = prev {
            self.env.insert(id, prev_lvl);
        }
    }

    fn elab_app(&mut self, fun: ExpHnd, arg: ExpHnd) -> Result<stx::Exp<'s>> {
        let fun_stx = self.elab_exp(fun)?;
        let arg_stx = self.elab_exp(arg)?;
        Ok(stx::Exp::App(fun_stx, arg_stx))
    }

    fn elab_lam(&mut self, name: Name<'s>, body: ExpHnd) -> Result<stx::Exp<'s>> {
        let id = name.id;
        let prev = self.bind(id);
        let body_stx_result = self.elab_exp(body);
        self.unbind(id, prev);
        Ok(stx::Exp::Abs(id, body_stx_result?))
    }
}
