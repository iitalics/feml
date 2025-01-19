use crate::core_syntax as stx;
use crate::intern::Symbol;

use std::rc::Rc;

pub type ValBox = Rc<Val>;

pub enum Val {
    // constructors
    Con(Symbol, Vec<ValBox>),
    // function value
    Fun(Clos),
    // function type
    Pi(ValBox, Clos),
    // neutral variables
    NeVar(Level),
    // neutral application
    NeApp(ValBox, ValBox),
}

pub type Level = usize;

#[derive(Clone)]
pub struct Clos {
    pub sym: Symbol,
    pub exp: stx::TermBox,
    pub env: Env,
}

impl Clos {
    fn new(abs: stx::Abs, env: Env) -> Self {
        Self {
            sym: abs.param,
            exp: abs.body,
            env,
        }
    }
}

#[derive(Clone)]
pub enum Env {
    Ne(Level),
    Cons(ValBox, Rc<Env>),
}

impl Env {
    pub fn nth(&self, mut i: usize) -> ValBox {
        let mut env = self;
        loop {
            match (env, i) {
                (Env::Ne(n), i) => {
                    assert!(i < *n);
                    return neutral(*n - i);
                }
                (Env::Cons(v, _), 0) => return v.clone(),
                (Env::Cons(_, rest), _) => {
                    env = rest;
                    i -= 1;
                }
            }
        }
    }
}

// == Constructors ==

pub fn con(sym: Symbol) -> ValBox {
    ValBox::new(Val::Con(sym, vec![]))
}

pub fn con_extend(sym: Symbol, args: &[ValBox], new_arg: ValBox) -> ValBox {
    let mut args = Vec::from_iter(args.iter().cloned());
    args.push(new_arg);
    ValBox::new(Val::Con(sym, args))
}

pub fn pi(dom: ValBox, rng: stx::Abs, env: Env) -> ValBox {
    ValBox::new(Val::Pi(dom, Clos::new(rng, env)))
}

pub fn arrow(dom: ValBox, rng: ValBox) -> ValBox {
    // (T -> U) == Pi (_ : T). U
    let env = env_cons(rng, env_empty());
    let rng = stx::Abs {
        param: Symbol::UNDERSCORE,
        body: stx::var(1),
    };
    pi(dom, rng, env)
}

pub fn fun(lam: stx::Abs, env: Env) -> ValBox {
    ValBox::new(Val::Fun(Clos::new(lam, env)))
}

pub fn neutral(lvl: Level) -> ValBox {
    ValBox::new(Val::NeVar(lvl))
}

pub fn env_empty() -> Env {
    env_neutral(0)
}

pub fn env_neutral(n: usize) -> Env {
    Env::Ne(n)
}

pub fn env_cons(v: ValBox, env: Env) -> Env {
    Env::Cons(v, Rc::new(env))
}
