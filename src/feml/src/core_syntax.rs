use std::fmt;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Constant {
    TypeType,
    TypeNat,
    Z,
    S,
}

pub type Exp<'s> = Box<Ex<'s>>;

#[derive(Debug)]
pub enum Ex<'s> {
    // c
    Cst(Constant),
    // x
    Var(usize),
    // f a
    App(Exp<'s>, Exp<'s>),
    // fn x => e
    Lam(Lam<'s>),
}

#[derive(Debug)]
pub struct Lam<'s>(pub &'s str, pub Exp<'s>);

// == Pretty printing ==

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TypeNat => write!(f, "nat"),
            Self::TypeType => write!(f, "type"),
            Self::Z => write!(f, "Z"),
            Self::S => write!(f, "S"),
        }
    }
}

struct ExpDisplayContext<'s> {
    names: Vec<&'s str>,
}

impl<'s> ExpDisplayContext<'s> {
    fn new() -> Self {
        Self { names: vec![] }
    }

    fn fmt(&mut self, f: &mut fmt::Formatter<'_>, exp: &Ex<'s>, prec: u32) -> fmt::Result {
        use crate::pretty_print_utils::{close, open};
        match exp {
            Ex::Cst(c) => write!(f, "{c}"),
            Ex::Var(i) => {
                let name = self.names[self.names.len() - i - 1];
                write!(f, "{name}")
            }
            Ex::App(fun, arg) => {
                open(f, prec, 2)?;
                self.fmt(f, fun, 2)?;
                write!(f, " ")?;
                self.fmt(f, arg, 3)?;
                close(f, prec, 2)
            }
            Ex::Lam(Lam(name, body)) => {
                open(f, prec, 0)?;
                write!(f, "fn {name}")?;
                self.names.push(name);
                let result = write!(f, " => ")
                    .and_then(|_| self.fmt(f, body, 0))
                    .and_then(|_| close(f, prec, 0));
                self.names.pop();
                result
            }
        }
    }
}

impl fmt::Display for Exp<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        ExpDisplayContext::new().fmt(f, self, 0)
    }
}
