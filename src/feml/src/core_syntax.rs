use crate::intern::{self, Symbol};

use std::borrow::Cow;
use std::fmt;
use std::rc::Rc;

pub type TermBox = Rc<Term>;

#[derive(Debug)]
pub enum Term {
    // c
    Con(Con),
    // x
    Var(usize),
    // f a
    App(TermBox, TermBox),
    // fn x => e
    Lam(Abs),
    // (x : t) -> s
    Pi(TermBox, Abs),
}

pub type Con = Symbol;

#[derive(Debug, Clone)]
pub struct Abs {
    pub param: Symbol,
    pub body: TermBox,
}

impl Term {
    pub fn alpha_eq(&self, rhs: &Term) -> bool {
        match (self, rhs) {
            (Term::Con(c1), Term::Con(c2)) => *c1 == *c2,
            (Term::Var(i1), Term::Var(i2)) => *i1 == *i2,
            (Term::App(f1, a1), Term::App(f2, a2)) => f1.alpha_eq(f2) && a1.alpha_eq(a2),
            (Term::Lam(b1), Term::Lam(b2)) => b1.alpha_eq(b2),
            (Term::Pi(d1, r1), Term::Pi(d2, r2)) => d2.alpha_eq(d1) && r1.alpha_eq(r2),
            (_, _) => false,
        }
    }
}

impl Abs {
    pub fn alpha_eq(&self, rhs: &Abs) -> bool {
        self.body.alpha_eq(&rhs.body)
    }
}

// == Constructors ==

pub fn con(c: Con) -> TermBox {
    Rc::new(Term::Con(c))
}

pub fn var(i: usize) -> TermBox {
    Rc::new(Term::Var(i))
}

pub fn app(fun: TermBox, arg: TermBox) -> TermBox {
    Rc::new(Term::App(fun, arg))
}

pub fn lam(param: Symbol, body: TermBox) -> TermBox {
    Rc::new(Term::Lam(Abs { param, body }))
}

pub fn pi(dom: TermBox, param: Symbol, rng: TermBox) -> TermBox {
    Rc::new(Term::Pi(dom, Abs { param, body: rng }))
}

// == Pretty printing ==

pub struct DisplayTerm<'s, 'c, 't> {
    intern_pool: &'s intern::Pool,
    context: &'c [Symbol],
    term: &'t Term,
}

impl Term {
    pub fn display<'s, 'c>(
        &self,
        intern_pool: &'s intern::Pool,
        context: &'c [Symbol],
    ) -> DisplayTerm<'s, 'c, '_> {
        DisplayTerm {
            intern_pool,
            context,
            term: self,
        }
    }
}

impl fmt::Display for DisplayTerm<'_, '_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ctx = DisplayTermContext::new(self.intern_pool);
        for sym in self.context {
            ctx.names.push(self.intern_pool.get(*sym).into());
        }
        ctx.fmt(f, self.term, 0)
    }
}

struct DisplayTermContext<'s> {
    intern_pool: &'s intern::Pool,
    // convert debruijn indices into strings
    names: Vec<Cow<'s, str>>,
}

impl<'s> DisplayTermContext<'s> {
    fn new(intern_pool: &'s intern::Pool) -> Self {
        Self {
            intern_pool,
            names: vec![],
        }
    }

    fn fresh(&self, symbol: Symbol) -> Cow<'s, str> {
        let orig_id = self.intern_pool.get(symbol);
        let mut new_id = Cow::Borrowed(orig_id);
        let mut tries = 0;
        'in_use: loop {
            for prev_id in self.names.iter() {
                if prev_id == &new_id {
                    // add integer suffix to generate new name
                    // x -> x1 -> x2 -> ...
                    tries += 1;
                    new_id = Cow::Owned(format!("{orig_id}{tries}"));
                    continue 'in_use;
                }
            }
            return new_id;
        }
    }

    fn fmt(&mut self, f: &mut fmt::Formatter<'_>, term: &Term, prec: u32) -> fmt::Result {
        use crate::pretty_print_utils::{close, open};
        match term {
            Term::Con(c) => write!(f, "{}", self.intern_pool.get(*c)),
            Term::Var(i) => {
                if *i >= self.names.len() {
                    // FIXME: allow passing initial context of names for pretty printing
                    // these variables
                    write!(f, ".{i}")
                } else {
                    let id = &self.names[self.names.len() - i - 1];
                    write!(f, "{id}")
                }
            }
            Term::App(fun, arg) => {
                open(f, prec, 2)?;
                self.fmt(f, fun, 2)?;
                write!(f, " ")?;
                self.fmt(f, arg, 3)?;
                close(f, prec, 2)
            }
            Term::Lam(lam) => {
                open(f, prec, 0)?;
                let param = self.fresh(lam.param);
                write!(f, "fn {param}")?;
                self.names.push(param);
                let result = write!(f, " => ")
                    .and_then(|_| self.fmt(f, &lam.body, 0))
                    .and_then(|_| close(f, prec, 0));
                self.names.pop();
                result
            }
            Term::Pi(dom, rng) => {
                open(f, prec, 1)?;
                // TODO: if rng is constant in its argument, don't name the domain at all
                let param = self.fresh(rng.param);
                write!(f, "({param} : ")?;
                self.fmt(f, dom, 0)?;
                write!(f, ") -> ")?;
                self.names.push(param);
                let result = self.fmt(f, &rng.body, 1).and_then(|_| close(f, prec, 1));
                self.names.pop();
                result
            }
        }
    }
}
