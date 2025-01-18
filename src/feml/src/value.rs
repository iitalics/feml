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
    // t -> s
    Arrow(ValBox<'e>, ValBox<'e>),
    // closure value
    Abs(stx::Lam<'e>, Env<'e>),
    // neutral
    Neu(usize),
}

#[derive(Clone)]
pub enum Env<'e> {
    Neutral(usize),
    Cons(ValBox<'e>, Rc<Env<'e>>),
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

pub fn arrow<'e>(v1: ValBox<'e>, v2: ValBox<'e>) -> ValBox<'e> {
    ValBox::new(Val::Arrow(v1, v2))
}

pub fn abs<'e>(lam: stx::Lam<'e>, env: Env<'e>) -> ValBox<'e> {
    ValBox::new(Val::Abs(lam, env))
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

pub struct DisplayVal<'e, 'v> {
    val: &'v Val<'e>,
    prec: u32,
}

impl<'e> Val<'e> {
    pub fn display_prec(&self, prec: u32) -> DisplayVal<'e, '_> {
        DisplayVal { val: self, prec }
    }
}

impl fmt::Display for Val<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.display_prec(0).fmt(f)
    }
}

impl fmt::Display for DisplayVal<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use crate::pretty_print_utils::{close, open};
        match self.val {
            Val::TypeType => write!(f, "type"),
            Val::TypeNat => write!(f, "nat"),
            Val::Nat(n) => write!(f, "{n}"),
            Val::CtorS | Val::Abs(_, _) => write!(f, "[fn]"),
            Val::Neu(lvl) => write!(f, "?{lvl}"),
            Val::Arrow(dom, rng) => {
                open(f, self.prec, 1)?;
                write!(f, "{} -> {}", dom.display_prec(2), rng.display_prec(1))?;
                close(f, self.prec, 1)
            }
        }
    }
}
