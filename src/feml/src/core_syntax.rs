use std::fmt;
use std::rc::Rc;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Constant {
    TypeType,
    TypeNat,
    Z,
    S,
}

pub type TermBox<'s> = Rc<Term<'s>>;

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
    // t -> s
    Arr(Arrow<'s>),
}

#[derive(Debug, Clone)]
pub struct Lam<'s> {
    pub arg_id: &'s str,
    pub body: TermBox<'s>,
}

#[derive(Debug, Clone)]
pub struct Arrow<'s> {
    // TODO: pi type
    pub dom: TermBox<'s>,
    pub rng: TermBox<'s>,
}

// == Constructors ==

pub fn cst(c: Constant) -> TermBox<'static> {
    Rc::new(Term::Cst(c))
}

pub fn var(i: usize) -> TermBox<'static> {
    Rc::new(Term::Var(i))
}

pub fn app<'s>(fun: TermBox<'s>, arg: TermBox<'s>) -> TermBox<'s> {
    Rc::new(Term::App(fun, arg))
}

pub fn lam<'s>(arg_id: &'s str, body: TermBox<'s>) -> TermBox<'s> {
    Rc::new(Term::Lam(Lam { arg_id, body }))
}

pub fn arrow<'s>(dom: TermBox<'s>, rng: TermBox<'s>) -> TermBox<'s> {
    Rc::new(Term::Arr(Arrow { dom, rng }))
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
            Term::Lam(Lam { arg_id, body }) => {
                open(f, prec, 0)?;
                write!(f, "fn {arg_id}")?;
                self.names.push(arg_id);
                let result = write!(f, " => ")
                    .and_then(|_| self.fmt(f, body, 0))
                    .and_then(|_| close(f, prec, 0));
                self.names.pop();
                result
            }
            Term::Arr(Arrow { dom, rng }) => {
                open(f, prec, 1)?;
                self.fmt(f, dom, 2)?;
                write!(f, " -> ")?;
                self.fmt(f, rng, 1)?;
                close(f, prec, 1)
            }
        }
    }
}

impl fmt::Display for Term<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        DisplayTermContext::new().fmt(f, self, 0)
    }
}
