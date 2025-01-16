use crate::intern::Str;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Constant {
    Z,
    S,
}

#[derive(Clone, Debug)]
pub enum Exp<'i> {
    Const(Constant),
    Var(usize),
    App(Box<Exp<'i>>, Box<Exp<'i>>),
    Abs(Str<'i>, Box<Exp<'i>>),
}
