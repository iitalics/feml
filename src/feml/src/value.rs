use crate::core_syntax as stx;

use std::fmt;
use std::rc::Rc;

pub type Val<'e> = Rc<Va<'e>>;
pub type Type = Val<'static>;

pub enum Va<'e> {
    // type
    TypeType,
    // nat
    TypeNat,
    // nat value
    Nat(u64),
    // nat S constructor
    CtorS,
    // t -> s
    Arrow(Val<'e>, Val<'e>),
    // closure value
    Abs(&'e stx::Lam<'e>, Env<'e>),
}

#[derive(Clone)]
pub enum Env<'e> {
    Empty,
    Cons(Val<'e>, Rc<Env<'e>>),
}

// == Constructors ==

pub fn type_type() -> Val<'static> {
    Val::new(Va::TypeType)
}

pub fn type_nat() -> Val<'static> {
    Val::new(Va::TypeNat)
}

pub fn nat(n: u64) -> Val<'static> {
    Val::new(Va::Nat(n))
}

pub fn ctor_s() -> Val<'static> {
    Val::new(Va::CtorS)
}

pub fn arrow<'e>(v1: Val<'e>, v2: Val<'e>) -> Val<'e> {
    Val::new(Va::Arrow(v1, v2))
}

pub fn abs<'e>(lam: &'e stx::Lam<'e>, env: Env<'e>) -> Val<'e> {
    Val::new(Va::Abs(lam, env))
}

pub fn empty() -> Env<'static> {
    Env::Empty
}

pub fn cons<'e>(v: Val<'e>, env: Env<'e>) -> Env<'e> {
    Env::Cons(v, Rc::new(env))
}

// == Pretty printing ==

pub struct DisplayVal<'e, 'v> {
    val: &'v Va<'e>,
    prec: u32,
}

impl<'e> Va<'e> {
    pub fn display_prec(&self, prec: u32) -> DisplayVal<'e, '_> {
        DisplayVal { val: self, prec }
    }
}

impl fmt::Display for Va<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.display_prec(0).fmt(f)
    }
}

impl fmt::Display for DisplayVal<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use crate::pretty_print_utils::{close, open};
        match self.val {
            Va::TypeType => write!(f, "type"),
            Va::TypeNat => write!(f, "nat"),
            Va::Nat(n) => write!(f, "{n}"),
            Va::CtorS | Va::Abs(_, _) => write!(f, "[fn]"),
            Va::Arrow(dom, rng) => {
                open(f, self.prec, 1)?;
                write!(f, "{} -> {}", dom.display_prec(2), rng.display_prec(1))?;
                close(f, self.prec, 1)
            }
        }
    }
}
