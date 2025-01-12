use crate::intern::{Intern, Str};
use crate::token::Loc;
use std::fmt;

/// The parse tree is the immediate result of parsing which has not had any type- or
/// wellformedness-checks done yet.
pub struct ParseTree<'s> {
    decl: Vec<Decl>,
    sig: Vec<Sig<'s>>,
    exp: Vec<Exp<'s>>,
}

impl<'s> ParseTree<'s> {
    pub fn new() -> Self {
        Self {
            decl: Vec::with_capacity(256),
            sig: Vec::with_capacity(256),
            exp: Vec::with_capacity(4096),
        }
    }

    pub fn decls(&self) -> Vec<DeclHnd> {
        (0..self.decl.len()).map(|i| DeclHnd(i as _)).collect()
    }

    pub fn alloc_decl(&mut self, decl: Decl) -> DeclHnd {
        DeclHnd(extend(&mut self.decl, decl))
    }

    pub fn view_decl(&self, h: DeclHnd) -> &Decl {
        &self.decl[h.0 as usize]
    }

    pub fn alloc_sig(&mut self, sig: Sig<'s>) -> SigHnd {
        SigHnd(extend(&mut self.sig, sig))
    }

    pub fn view_sig(&self, h: SigHnd) -> &Sig<'s> {
        &self.sig[h.0 as usize]
    }

    pub fn alloc_exp(&mut self, exp: Exp<'s>) -> ExpHnd {
        ExpHnd(extend(&mut self.exp, exp))
    }

    pub fn view_exp(&self, h: ExpHnd) -> &Exp<'s> {
        &self.exp[h.0 as usize]
    }
}

// == Handles ==

type Hnd = u32;

/// Handle referencing a declaration.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct DeclHnd(Hnd);

/// Handle referencing a signature.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct SigHnd(Hnd);

/// Handle referencing an expression.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ExpHnd(Hnd);

pub type TyHnd = ExpHnd;

// == Syntax tree ==

/// Names of identifiers or operators.
#[derive(Copy, Clone)]
pub struct Name<'s> {
    pub loc: Loc,
    pub id: Str<'s>,
    pub is_operator: bool,
}

impl<'s> Name<'s> {
    pub fn ident(loc: Loc, id: Str<'s>) -> Self {
        Self {
            loc,
            id,
            is_operator: false,
        }
    }

    pub fn operator(loc: Loc, id: Str<'s>) -> Self {
        Self {
            loc,
            id,
            is_operator: true,
        }
    }
}

/// Top-level declarations.
#[derive(Clone)]
pub enum Decl {
    Def {
        loc_def: Loc,
        sig: SigHnd,
        body: ExpHnd,
    },
    Data {
        loc_data: Loc,
        sig: SigHnd,
        ctors: Vec<SigHnd>,
    },
}

/// Signatures for definitions.
#[derive(Clone)]
pub struct Sig<'s> {
    pub name: Name<'s>,
    pub params: Vec<Param<'s>>,
    //pub loc_cl : Loc,
    pub ret_ty: TyHnd,
}

/// Parameters to definitions.
#[derive(Copy, Clone)]
pub struct Param<'s> {
    pub name: Name<'s>,
    pub ty: TyHnd,
}

/// Expressions.
#[derive(Clone)]
pub enum Exp<'s> {
    // x
    Var(Name<'s>),
    // f a
    App(ExpHnd, Arg),
    // d -> r
    Arr(Arr),
}

// TODO: named/explicit args
type Arg = ExpHnd;

/// Arrow types.
#[derive(Clone)]
pub struct Arr {
    pub dom: ExpHnd,
    pub rng: ExpHnd,
}

fn extend<T>(nodes: &mut Vec<T>, item: T) -> Hnd {
    let h = nodes.len() as Hnd;
    nodes.push(item);
    h
}

// == Pretty printing ==

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
            self.fmt_name(f, int, &param.name)?;
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
            Exp::App(fun, arg) => {
                if prec > 1 {
                    write!(f, "(")?;
                }
                self.fmt_exp(f, int, *fun, 1)?;
                write!(f, " ")?;
                self.fmt_exp(f, int, *arg, 2)?;
                if prec > 1 {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }

    fn fmt_name(&self, f: &mut fmt::Formatter<'_>, int: &Intern, name: &Name<'s>) -> fmt::Result {
        if name.is_operator {
            write!(f, "({})", int.get(name.id))
        } else {
            write!(f, "{}", int.get(name.id))
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_construct_and_pretty_print() {
        let int = Intern::new();
        let mut pt = ParseTree::new();

        #[allow(non_snake_case)]
        #[rustfmt::skip]
        let decl = {
            let loc = Loc::default();
            let str_A = int.intern("A");
            let str_eq = int.intern("==");
            let str_refl = int.intern("refl");
            let str_type = int.intern("type");
            let str_x = int.intern("x");
            let nm_A = Name::ident(loc, str_A);
            let nm_eq = Name::operator(loc, str_eq);
            let nm_refl = Name::ident(loc, str_refl);
            let nm_type = Name::ident(loc, str_type);
            let nm_x = Name::ident(loc, str_x);
            let var_A = pt.alloc_exp(Exp::Var(nm_A));
            let var_eq = pt.alloc_exp(Exp::Var(nm_eq));
            let var_type = pt.alloc_exp(Exp::Var(nm_type));
            let var_x = pt.alloc_exp(Exp::Var(nm_x));
            // (A : type)
            let param_A = Param { name: nm_A, ty: var_type };
            // (x : A)
            let param_x = Param { name: nm_x, ty: var_A };
            // A -> type
            let exp_arr_A_type = pt.alloc_exp(Exp::Arr(Arr {
                dom: var_A,
                rng: var_type,
            }));
            // (==) A x x
            let exp_x_eq_x = pt.alloc_exp(Exp::App(var_eq, var_A));
            let exp_x_eq_x = pt.alloc_exp(Exp::App(exp_x_eq_x, var_x));
            let exp_x_eq_x = pt.alloc_exp(Exp::App(exp_x_eq_x, var_x));
            // (==) (A : type) (x : A) : A -> type
            let sig_eq = pt.alloc_sig(Sig {
                name: nm_eq,
                params: vec![param_A, param_x],
                ret_ty: exp_arr_A_type,
            });
            // refl : (==) A x x
            let sig_refl = pt.alloc_sig(Sig {
                name: nm_refl,
                params: vec![],
                ret_ty: exp_x_eq_x,
            });
            // data (==) {...}
            pt.alloc_decl(Decl::Data {
                loc_data: loc,
                sig: sig_eq,
                ctors: vec![sig_refl],
            })
        };

        assert_eq!(
            pt.display_decl(&int, decl).to_string(),
            "data (==) (A : type) (x : A) : A -> type { refl : (==) A x x; };",
        );

        let exp = {
            let loc = Loc::default();
            let str_x = int.intern("x");
            let str_y = int.intern("y");
            let nm_x = Name::ident(loc, str_x);
            let nm_y = Name::ident(loc, str_y);
            let var_x = pt.alloc_exp(Exp::Var(nm_x));
            let var_y = pt.alloc_exp(Exp::Var(nm_y));
            let exp_x_x = pt.alloc_exp(Exp::App(var_x, var_x));
            let exp_y_y = pt.alloc_exp(Exp::App(var_y, var_y));
            pt.alloc_exp(Exp::App(exp_x_x, exp_y_y))
        };

        assert_eq!(pt.display_exp(&int, exp).to_string(), "x x (y y)");
    }
}
