use std::fmt;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Constant {
    TypeType,
    TypeNat,
    Z,
    S,
}

pub type TermBox<'s> = Box<Term<'s>>;

#[derive(Debug)]
pub enum Term<'s> {
    // c
    Cst(Constant),
    // x
    Var(usize),
    // f a
    App(TermBox<'s>, TermBox<'s>),
    // fn x => e
    Lam(Lam<'s>),
}

#[derive(Debug)]
pub struct Lam<'s>(pub &'s str, pub TermBox<'s>);

// == Constructors ==

pub fn cst(c: Constant) -> TermBox<'static> {
    Box::new(Term::Cst(c))
}

pub fn var(i: usize) -> TermBox<'static> {
    Box::new(Term::Var(i))
}

pub fn app<'s>(fun: TermBox<'s>, arg: TermBox<'s>) -> TermBox<'s> {
    Box::new(Term::App(fun, arg))
}

pub fn lam<'s>(id: &'s str, body: TermBox<'s>) -> TermBox<'s> {
    Box::new(Term::Lam(Lam(id, body)))
}

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

struct DisplayTermContext<'s> {
    // convert debruijn indices into strings
    names: Vec<&'s str>,
}

impl<'s> DisplayTermContext<'s> {
    fn new() -> Self {
        Self { names: vec![] }
    }

    fn fmt(&mut self, f: &mut fmt::Formatter<'_>, exp: &Term<'s>, prec: u32) -> fmt::Result {
        use crate::pretty_print_utils::{close, open};
        match exp {
            Term::Cst(c) => write!(f, "{c}"),
            Term::Var(i) => {
                let name = self.names[self.names.len() - i - 1];
                write!(f, "{name}")
            }
            Term::App(fun, arg) => {
                open(f, prec, 2)?;
                self.fmt(f, fun, 2)?;
                write!(f, " ")?;
                self.fmt(f, arg, 3)?;
                close(f, prec, 2)
            }
            Term::Lam(Lam(name, body)) => {
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

impl fmt::Display for TermBox<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        DisplayTermContext::new().fmt(f, self, 0)
    }
}
