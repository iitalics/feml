use std::fmt;
use std::rc::Rc;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Constant {
    Z,
    S,
}

#[derive(Clone, Debug)]
pub enum Exp<'s> {
    Const(Constant),
    Var(usize),
    App(Box<Exp<'s>>, Box<Exp<'s>>),
    Abs(&'s str, Box<Exp<'s>>),
}

#[derive(Clone, Debug)]
pub enum Ty {
    Nat,
    Arr(Type, Type),
}

pub type Type = Rc<Ty>;

impl Ty {
    pub fn compatible(&self, mut rhs: &Ty) -> bool {
        let mut lhs = self;
        loop {
            match lhs {
                Ty::Nat => break matches!(rhs, Ty::Nat),
                Ty::Arr(lhs_dom, lhs_rng) => match rhs {
                    Ty::Arr(rhs_dom, rhs_rng) => {
                        if !rhs_dom.compatible(lhs_dom) {
                            break false;
                        }
                        lhs = &lhs_rng;
                        rhs = &rhs_rng;
                    }
                    _ => break false,
                },
            }
        }
    }
}

impl Constant {
    pub fn get_type(&self) -> Type {
        match self {
            Constant::Z => Type::new(Ty::Nat),
            Constant::S => Type::new(Ty::Arr(Type::new(Ty::Nat), Type::new(Ty::Nat))),
        }
    }
}

// == Pretty printing ==

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constant::S => write!(f, "S"),
            Constant::Z => write!(f, "Z"),
        }
    }
}

struct ExpDisplayContext<'s> {
    names: Vec<&'s str>,
}

fn open(f: &mut fmt::Formatter<'_>, prec: u32, min_prec: u32) -> fmt::Result {
    if prec > min_prec {
        write!(f, "(")?;
    }
    Ok(())
}

fn close(f: &mut fmt::Formatter<'_>, prec: u32, min_prec: u32) -> fmt::Result {
    if prec > min_prec {
        write!(f, ")")?;
    }
    Ok(())
}

impl<'s> ExpDisplayContext<'s> {
    fn new() -> Self {
        Self { names: vec![] }
    }

    fn fmt(&mut self, f: &mut fmt::Formatter<'_>, exp: &Exp<'s>, prec: u32) -> fmt::Result {
        match exp {
            Exp::Const(c) => write!(f, "{c}"),
            Exp::Var(i) => {
                let name = self.names[self.names.len() - i - 1];
                write!(f, "{name}")
            }
            Exp::App(fun, arg) => {
                open(f, prec, 2)?;
                self.fmt(f, fun, 2)?;
                write!(f, " ")?;
                self.fmt(f, arg, 3)?;
                close(f, prec, 2)
            }
            Exp::Abs(name, body) => {
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

pub struct DisplayTy<'t> {
    ty: &'t Ty,
    prec: u32,
}

impl Ty {
    pub fn display_prec(&self, prec: u32) -> DisplayTy<'_> {
        DisplayTy { ty: self, prec }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.display_prec(0).fmt(f)
    }
}

impl fmt::Display for DisplayTy<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.ty {
            Ty::Nat => write!(f, "nat"),
            Ty::Arr(dom, rng) => {
                open(f, self.prec, 1)?;
                write!(f, "{} -> {}", dom.display_prec(2), rng.display_prec(1))?;
                close(f, self.prec, 1)
            }
        }
    }
}
