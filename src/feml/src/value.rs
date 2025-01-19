use crate::core_syntax as stx;
use crate::intern::{self, Symbol};

use std::fmt;
use std::rc::Rc;

pub type ValBox = Rc<Val>;

pub enum Val {
    // constructors
    Con(Symbol, Vec<ValBox>),
    // function value
    Fun(Clos),
    // function type
    Pi(ValBox, Clos),
    // neutral
    Neu(usize),
}

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
    Neutral(usize),
    Cons(ValBox, Rc<Env>),
}

impl Env {
    pub fn nth(&self, mut i: usize) -> ValBox {
        let mut env = self;
        loop {
            match (env, i) {
                (Env::Neutral(n), i) => {
                    assert!(i < *n);
                    return neu(*n - i);
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

pub fn neu(lvl: usize) -> ValBox {
    ValBox::new(Val::Neu(lvl))
}

pub fn env_empty() -> Env {
    env_neutral(0)
}

pub fn env_neutral(n: usize) -> Env {
    Env::Neutral(n)
}

pub fn env_cons(v: ValBox, env: Env) -> Env {
    Env::Cons(v, Rc::new(env))
}

// == Pretty printing ==

pub struct DisplayVal<'s, 'v> {
    val: &'v Val,
    intern_pool: &'s intern::Pool,
    prec: u32,
}

impl Val {
    // FIXME: pretty printing values is not really appropriate. you should reify values
    // back into terms and then pretty print terms. this would enable printing closures
    // and neutral terms.
    pub fn display<'s>(&self, intern_pool: &'s intern::Pool) -> DisplayVal<'s, '_> {
        self.display_prec(intern_pool, 0)
    }

    pub fn display_prec<'s>(&self, intern_pool: &'s intern::Pool, prec: u32) -> DisplayVal<'s, '_> {
        DisplayVal {
            val: self,
            intern_pool,
            prec,
        }
    }
}

impl fmt::Display for DisplayVal<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use crate::pretty_print_utils::{close, open};
        match self.val {
            Val::Con(c, args) => {
                open(f, self.prec, 2)?;
                write!(f, "{}", self.intern_pool.get(*c))?;
                for arg in args {
                    write!(f, " {}", arg.display_prec(self.intern_pool, 3))?;
                }
                close(f, self.prec, 2)
            }
            Val::Neu(lvl) => write!(f, "?{lvl}"),
            Val::Fun(_) => write!(f, "<Fun>"),
            Val::Pi(_, _) => write!(f, "<Pi>"),
        }
    }
}
