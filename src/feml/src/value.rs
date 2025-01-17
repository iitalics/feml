use crate::core_syntax::Exp;

use std::fmt;
use std::rc::Rc;

pub enum Val<'e> {
    S,
    Nat(u64),
    Abs(Environ<'e>, &'e Exp<'e>),
}

impl fmt::Display for Val<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Nat(n) => write!(f, "nat({})", *n),
            Self::Abs { .. } | Self::S => write!(f, "(fun)"),
        }
    }
}

pub enum Env<'e> {
    Empty,
    Cons(Value<'e>, Rc<Env<'e>>),
}

pub type Value<'e> = Rc<Val<'e>>;
pub type Environ<'e> = Rc<Env<'e>>;
