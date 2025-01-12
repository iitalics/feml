use crate::intern::{Intern, Str};
use crate::token::Loc;
use std::fmt;

pub struct ParseTree<'s> {
    decl: Vec<Decl>,
    sig: Vec<Sig<'s>>,
    exp: Vec<Exp<'s>>,
}

type Hnd = u32;
pub type DeclHnd = Hnd;
pub type SigHnd = Hnd;
pub type ExpHnd = Hnd;
pub type TyHnd = ExpHnd;

#[derive(Clone)]
pub enum Decl {
    Def {
        loc: Loc,
        sig: SigHnd,
        body: ExpHnd,
    },
    Data {
        loc: Loc,
        sig: SigHnd,
        ctors: Vec<SigHnd>,
    },
}

#[derive(Clone)]
pub struct Sig<'s> {
    pub name: Name<'s>,
    pub params: Vec<Param<'s>>,
    pub ret_ty: TyHnd,
}

#[derive(Copy, Clone)]
pub struct Name<'s> {
    pub loc: Loc,
    pub id: Str<'s>,
    pub is_oper: bool,
}

#[derive(Copy, Clone)]
pub struct Param<'s> {
    pub loc: Loc,
    pub id: Str<'s>,
    pub ty: TyHnd,
}

#[derive(Clone)]
pub enum Exp<'s> {
    Var(Name<'s>),
    App(App<'s>),
    Arr(Arr),
}

#[derive(Clone)]
pub struct Arr {
    pub dom: ExpHnd,
    pub rng: ExpHnd,
}

#[derive(Clone)]
pub struct App<'s> {
    pub head: Name<'s>,
    pub args: Vec<ExpHnd>,
}

fn extend<T>(nodes: &mut Vec<T>, item: T) -> Hnd {
    let h = nodes.len() as Hnd;
    nodes.push(item);
    h
}

impl<'s> ParseTree<'s> {
    pub fn new() -> Self {
        Self {
            decl: Vec::with_capacity(64),
            sig: Vec::with_capacity(64),
            exp: Vec::with_capacity(1024),
        }
    }

    pub fn decls(&self) -> std::ops::Range<DeclHnd> {
        0..(self.decl.len() as Hnd)
    }

    pub fn alloc_decl(&mut self, decl: Decl) -> DeclHnd {
        extend(&mut self.decl, decl)
    }

    pub fn view_decl(&self, h: ExpHnd) -> &Decl {
        &self.decl[h as usize]
    }

    pub fn alloc_sig(&mut self, sig: Sig<'s>) -> SigHnd {
        extend(&mut self.sig, sig)
    }

    pub fn view_sig(&self, h: SigHnd) -> &Sig<'s> {
        &self.sig[h as usize]
    }

    pub fn alloc_exp(&mut self, exp: Exp<'s>) -> ExpHnd {
        extend(&mut self.exp, exp)
    }

    pub fn view_exp(&self, h: ExpHnd) -> &Exp<'s> {
        &self.exp[h as usize]
    }
}

// pretty printing

pub struct DisplayDecl<'t, 's> {
    parse_tree: &'t ParseTree<'s>,
    intern: &'s Intern,
    decl: DeclHnd,
}

impl fmt::Display for DisplayDecl<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.parse_tree.fmt_decl(f, self.intern, self.decl)
    }
}

pub struct DisplayExp<'t, 's> {
    parse_tree: &'t ParseTree<'s>,
    intern: &'s Intern,
    exp: ExpHnd,
}

impl fmt::Display for DisplayExp<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.parse_tree.fmt_exp(f, self.intern, self.exp, 0)
    }
}

impl<'s> ParseTree<'s> {
    pub fn display_decl<'t>(&'t self, intern: &'s Intern, decl: DeclHnd) -> DisplayDecl<'t, 's> {
        DisplayDecl {
            parse_tree: self,
            intern,
            decl,
        }
    }

    pub fn display_exp<'t>(&'t self, intern: &'s Intern, exp: ExpHnd) -> DisplayExp<'t, 's> {
        DisplayExp {
            parse_tree: self,
            intern,
            exp,
        }
    }

    fn fmt_decl(&self, f: &mut fmt::Formatter<'_>, int: &Intern, decl: DeclHnd) -> fmt::Result {
        match self.view_decl(decl) {
            Decl::Def { sig, body, .. } => {
                write!(f, "def ")?;
                self.fmt_sig(f, int, *sig)?;
                write!(f, " = ")?;
                self.fmt_exp(f, int, *body, 0)?;
                write!(f, ";")
            }

            Decl::Data { sig, ctors, .. } => {
                write!(f, "data ")?;
                self.fmt_sig(f, int, *sig)?;
                write!(f, " {{")?;
                for ctor in ctors.iter() {
                    write!(f, " ")?;
                    self.fmt_sig(f, int, *ctor)?;
                    write!(f, ";")?;
                }
                write!(f, " }};")
            }
        }
    }

    fn fmt_sig(&self, f: &mut fmt::Formatter<'_>, int: &Intern, sig: SigHnd) -> fmt::Result {
        let sig = self.view_sig(sig);
        self.fmt_name(f, int, &sig.name)?;
        for param in sig.params.iter() {
            write!(f, " (")?;
            f.write_str(int.get(param.id))?;
            write!(f, " : ")?;
            self.fmt_exp(f, int, param.ty, 0)?;
            write!(f, ")")?;
        }
        write!(f, " : ")?;
        self.fmt_exp(f, int, sig.ret_ty, 0)
    }

    fn fmt_exp(
        &self,
        f: &mut fmt::Formatter<'_>,
        int: &Intern,
        exp: ExpHnd,
        prec: u32,
    ) -> fmt::Result {
        match self.view_exp(exp) {
            Exp::Var(name) => self.fmt_name(f, int, name),
            Exp::Arr(Arr { dom, rng }) => {
                if prec > 0 {
                    write!(f, "(")?;
                }
                self.fmt_exp(f, int, *dom, 1)?;
                write!(f, " -> ")?;
                self.fmt_exp(f, int, *rng, 0)?;
                if prec > 0 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Exp::App(App { head, args }) => {
                if prec > 1 {
                    write!(f, "(")?;
                }
                self.fmt_name(f, int, head)?;
                for arg in args.iter() {
                    write!(f, " ")?;
                    self.fmt_exp(f, int, *arg, 2)?;
                }
                if prec > 1 {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }

    fn fmt_name(&self, f: &mut fmt::Formatter<'_>, int: &Intern, name: &Name<'s>) -> fmt::Result {
        if name.is_oper {
            write!(f, "({})", int.get(name.id))
        } else {
            write!(f, "{}", int.get(name.id))
        }
    }
}
