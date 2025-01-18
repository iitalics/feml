use crate::core_syntax as stx;

use std::fmt;
use std::rc::Rc;

pub type ValBox<'e> = Rc<Val<'e>>;

pub enum Val<'e> {
    // type
    TypeType,
    // nat
    TypeNat,
    // nat value
    Nat(u64),
    // nat S constructor
    CtorS,
    // function value
    Fun(Clos<'e>),
    // function type
    Pi(ValBox<'e>, Clos<'e>),
    // neutral
    Neu(usize),
}

#[derive(Clone)]
pub struct Clos<'e> {
    pub id: &'e str,
    pub exp: stx::TermBox<'e>,
    pub env: Env<'e>,
}

impl<'e> Clos<'e> {
    fn new(abs: stx::Abs<'e>, env: Env<'e>) -> Self {
        Self {
            id: abs.id,
            exp: abs.body,
            env,
        }
    }
}

#[derive(Clone)]
pub enum Env<'e> {
    Neutral(usize),
    Cons(ValBox<'e>, Rc<Env<'e>>),
}

impl<'e> Env<'e> {
    pub fn nth(&self, mut i: usize) -> ValBox<'e> {
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

pub fn type_type() -> ValBox<'static> {
    ValBox::new(Val::TypeType)
}

pub fn type_nat() -> ValBox<'static> {
    ValBox::new(Val::TypeNat)
}

pub fn nat(n: u64) -> ValBox<'static> {
    ValBox::new(Val::Nat(n))
}

pub fn ctor_s() -> ValBox<'static> {
    ValBox::new(Val::CtorS)
}

pub fn pi<'e>(dom: ValBox<'e>, rng: stx::Abs<'e>, env: Env<'e>) -> ValBox<'e> {
    ValBox::new(Val::Pi(dom, Clos::new(rng, env)))
}

pub fn arrow<'e>(dom: ValBox<'e>, rng: ValBox<'e>) -> ValBox<'e> {
    // (T -> U) == Pi (_ : T). U
    let env = env_cons(rng, env_empty());
    let rng = stx::Abs {
        id: "_",
        body: stx::var(1),
    };
    pi(dom, rng, env)
}

pub fn fun<'e>(lam: stx::Abs<'e>, env: Env<'e>) -> ValBox<'e> {
    ValBox::new(Val::Fun(Clos::new(lam, env)))
}

pub fn neu(lvl: usize) -> ValBox<'static> {
    ValBox::new(Val::Neu(lvl))
}

pub fn env_empty() -> Env<'static> {
    env_neutral(0)
}

pub fn env_neutral(n: usize) -> Env<'static> {
    Env::Neutral(n)
}

pub fn env_cons<'e>(v: ValBox<'e>, env: Env<'e>) -> Env<'e> {
    Env::Cons(v, Rc::new(env))
}

// == Pretty printing ==

// FIXME: pretty printing values is not really appropriate. you should reify values back
// into terms and then pretty print terms. this would enable printing closures and neutral
// terms.

// pub struct DisplayVal<'e, 'v> {
//     val: &'v Val<'e>,
//     prec: u32,
// }
// impl<'e> Val<'e> {
//     pub fn display_prec(&self, prec: u32) -> DisplayVal<'e, '_> {
//         DisplayVal { val: self, prec }
//     }
// }
// impl fmt::Display for DisplayVal<'_, '_> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         //use crate::pretty_print_utils::{close, open};
//     }
// }

impl fmt::Display for Val<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Val::TypeType => write!(f, "type"),
            Val::TypeNat => write!(f, "nat"),
            Val::Nat(n) => write!(f, "{n}"),
            Val::Neu(lvl) => write!(f, "?{lvl}"),
            Val::CtorS | Val::Fun(_) => write!(f, "[fn]"),
            Val::Pi(_, _) => write!(f, "[pi]"),
        }
    }
}
