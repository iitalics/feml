use crate::token::Loc;
use std::fmt;

pub type Allocator = bumpalo::Bump;

pub fn allocator() -> Allocator {
    Allocator::new()
}

// == Syntax tree ==

/// Names of identifiers or operators.
#[derive(Copy, Clone)]
pub struct Name<'s> {
    pub loc: Loc,
    pub id: &'s str,
    pub is_operator: bool,
}

impl<'s> Name<'s> {
    pub fn ident(loc: Loc, id: &'s str) -> Self {
        Self {
            loc,
            id,
            is_operator: false,
        }
    }

    pub fn operator(loc: Loc, id: &'s str) -> Self {
        Self {
            loc,
            id,
            is_operator: true,
        }
    }
}

/// Top-level declarations.
#[derive(Copy, Clone)]
pub enum Decl<'s, 'a> {
    Def {
        loc_def: Loc,
        sig: &'a Sig<'s, 'a>,
        body: &'a Exp<'s, 'a>,
        //pub loc_sm: Loc,
    },
    Data {
        loc_data: Loc,
        sig: &'a Sig<'s, 'a>,
        //pub loc_lc: Loc,
        ctors: &'a [&'a Sig<'s, 'a>],
        //pub loc_rc: Loc,
        //pub loc_sm: Loc,
    },
    Assert {
        loc_assert: Loc,
        exp: &'a Exp<'s, 'a>,
        //pub loc_cl: Loc,
        ty: &'a Ty<'s, 'a>,
        //pub loc_sm: Loc,
    },
}

/// Signatures for definitions.
// name (x : t) ... : u
#[derive(Clone)]
pub struct Sig<'s, 'a> {
    pub name: Name<'s>,
    pub params: &'a [Param<'s, 'a>],
    //pub loc_cl : Loc,
    pub ret_ty: &'a Ty<'s, 'a>,
}

/// Parameters to definitions.
// (x : t)
#[derive(Copy, Clone)]
pub struct Param<'s, 'a> {
    //pub loc_lp : Loc,
    pub name: Name<'s>,
    //pub loc_cl : Loc,
    pub ty: &'a Ty<'s, 'a>,
    //pub loc_rp : Loc,
}

impl Param<'_, '_> {
    pub fn loc(&self) -> Loc {
        //self.loc_lp
        self.name.loc
    }
}

/// Expressions.
#[derive(Copy, Clone)]
pub enum Exp<'s, 'a> {
    // x
    Var(Name<'s>),
    // f a
    App(&'a Exp<'s, 'a>, &'a Arg<'s, 'a>),
    // d -> r
    Arr(Arrow<'s, 'a>),
    // fn x => e
    Lam(Lambda<'s, 'a>),
    // match v { p => e; }
    Mat(Match<'s, 'a>),
}

impl Exp<'_, '_> {
    pub fn loc(&self) -> Loc {
        let mut this = self;
        loop {
            match this {
                Exp::Var(name) => break name.loc,
                Exp::App(fun, _) => this = fun,
                Exp::Arr(arr) => match arr.param {
                    Some(p) => break p.loc(),
                    None => this = arr.dom,
                },
                Exp::Lam(lam) => break lam.loc(),
                //Exp::Mat(mat) => break mat.loc(),
                Exp::Mat(mat) => this = mat.subject,
            }
        }
    }
}

pub type Ty<'s, 'a> = Exp<'s, 'a>;

// TODO: named/explicit args
pub type Arg<'s, 'a> = Exp<'s, 'a>;

/// Arrow types.
// x -> u, (x : t) -> u
#[derive(Copy, Clone)]
pub struct Arrow<'s, 'a> {
    // note: dom is redundant if param is not None
    pub dom: &'a Ty<'s, 'a>,
    pub param: Option<Param<'s, 'a>>,
    //pub loc_ar : Loc,
    pub rng: &'a Ty<'s, 'a>,
}

impl<'s, 'a> Arrow<'s, 'a> {
    pub fn unnamed(dom: &'a Exp<'s, 'a>, rng: &'a Exp<'s, 'a>) -> Self {
        Self {
            dom,
            param: None,
            rng,
        }
    }

    pub fn named(dom: Param<'s, 'a>, rng: &'a Exp<'s, 'a>) -> Self {
        Self {
            dom: dom.ty,
            param: Some(dom),
            rng,
        }
    }
}

/// Lambda expressions.
#[derive(Copy, Clone)]
pub struct Lambda<'s, 'a> {
    //pub loc_fn: Loc,
    // note: name is redundant if param is not None
    pub name: Name<'s>,
    pub param: Option<Param<'s, 'a>>,
    //pub loc_rr: Loc,
    pub body: &'a Exp<'s, 'a>,
}

impl<'s, 'a> Lambda<'s, 'a> {
    pub fn loc(&self) -> Loc {
        //self.loc_fn,
        self.name.loc
    }

    pub fn untyped(name: Name<'s>, body: &'a Exp<'s, 'a>) -> Self {
        Self {
            name,
            param: None,
            body,
        }
    }

    pub fn typed(param: Param<'s, 'a>, body: &'a Exp<'s, 'a>) -> Self {
        Self {
            name: param.name,
            param: Some(param),
            body,
        }
    }
}

/// Match expressions.
#[derive(Copy, Clone)]
pub struct Match<'s, 'a> {
    pub subject: &'a Exp<'s, 'a>,
    pub cases: &'a [MatchCase<'s, 'a>],
}

pub type MatchCase<'s, 'a> = (&'a Pat<'s, 'a>, &'a Exp<'s, 'a>);

/// Patterns.
#[derive(Copy, Clone)]
pub enum Pat<'s, 'a> {
    // _
    Any(Loc),
    // x
    Var(Name<'s>),
    // f a
    App(&'a Pat<'s, 'a>, &'a PatArg<'s, 'a>),
}

type PatArg<'s, 'a> = Pat<'s, 'a>;

// == Pretty printing ==

impl fmt::Display for Decl<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Decl::Def { sig, body, .. } => {
                write!(f, "def {sig} = {body};")
            }

            Decl::Data { sig, ctors, .. } => {
                write!(f, "data {sig} {{")?;
                for ctor in ctors.iter() {
                    write!(f, " {ctor};")?;
                }
                write!(f, " }};")
            }

            Decl::Assert { exp, ty, .. } => {
                write!(f, "assert {exp} : {ty};")
            }
        }
    }
}

impl fmt::Display for Sig<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)?;
        for Param { name, ty } in self.params.iter() {
            write!(f, " ({name} : {ty})")?;
        }
        write!(f, " : {}", self.ret_ty)
    }
}

/// Display formatting for [`Exp`] at a specific precedence level.
pub struct DisplayExp<'s, 'a, 'e> {
    exp: &'e Exp<'s, 'a>,
    prec: u32,
}

impl<'s, 'a> Exp<'s, 'a> {
    pub fn display_prec(&self, prec: u32) -> DisplayExp<'s, 'a, '_> {
        DisplayExp { exp: self, prec }
    }
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

impl fmt::Display for Exp<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.display_prec(0).fmt(f)
    }
}

impl fmt::Display for DisplayExp<'_, '_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.exp {
            Exp::Var(name) => write!(f, "{name}"),
            Exp::Arr(Arrow { dom, param, rng }) => {
                open(f, self.prec, 1)?;
                match param {
                    Some(Param { name, ty }) => {
                        write!(f, "({name} : {ty})")?;
                    }
                    None => {
                        write!(f, "{}", dom.display_prec(2))?;
                    }
                }
                write!(f, " -> {}", rng.display_prec(1))?;
                close(f, self.prec, 1)
            }
            Exp::App(fun, arg) => {
                open(f, self.prec, 2)?;
                write!(f, "{} {}", fun.display_prec(2), arg.display_prec(3))?;
                close(f, self.prec, 2)
            }
            Exp::Lam(Lambda { name, param, body }) => {
                open(f, self.prec, 0)?;
                write!(f, "fn ")?;
                match param {
                    Some(Param { name, ty }) => write!(f, "({name} : {ty})")?,
                    None => write!(f, "{name}")?,
                }
                write!(f, " => {}", body.display_prec(0))?;
                close(f, self.prec, 0)
            }
            Exp::Mat(Match { subject, cases }) => {
                open(f, self.prec, 0)?;
                write!(f, "match {} {{", subject.display_prec(2))?;
                for (lhs, rhs) in cases.iter() {
                    write!(f, " {lhs} => {rhs};")?;
                }
                write!(f, " }}")?;
                close(f, self.prec, 0)
            }
        }
    }
}

/// Display formatting for [`Pat`] at a specific precedence level.
pub struct DisplayPat<'s, 'a, 'p> {
    pat: &'p Pat<'s, 'a>,
    prec: u32,
}

impl<'s, 'a> Pat<'s, 'a> {
    pub fn display_prec(&self, prec: u32) -> DisplayPat<'s, 'a, '_> {
        DisplayPat { pat: self, prec }
    }
}

impl fmt::Display for Pat<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.display_prec(0).fmt(f)
    }
}

impl fmt::Display for DisplayPat<'_, '_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.pat {
            Pat::Any(_) => write!(f, "_"),
            Pat::Var(name) => write!(f, "{name}"),
            Pat::App(head, arg) => {
                open(f, self.prec, 2)?;
                write!(f, "{} {}", head.display_prec(2), arg.display_prec(3))?;
                close(f, self.prec, 2)
            }
        }
    }
}

impl fmt::Display for Name<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.is_operator {
            true => write!(f, "({})", self.id),
            false => write!(f, "{}", self.id),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[allow(non_snake_case)]
    fn test_construct_and_pretty_print() {
        let al = allocator();
        let loc = Loc::default();

        let nm_A = Name::ident(loc, "A");
        let nm_B = Name::ident(loc, "B");
        let nm_C = Name::ident(loc, "C");
        let nm_S = Name::ident(loc, "S");
        let nm_Z = Name::ident(loc, "Z");
        let nm_eq = Name::operator(loc, "==");
        let nm_nat = Name::ident(loc, "nat");
        let nm_refl = Name::ident(loc, "refl");
        let nm_type = Name::ident(loc, "type");
        let nm_x = Name::ident(loc, "x");
        let nm_y = Name::ident(loc, "y");
        let var_A = al.alloc(Exp::Var(nm_A));
        let var_B = al.alloc(Exp::Var(nm_B));
        let var_C = al.alloc(Exp::Var(nm_C));
        let var_S = al.alloc(Exp::Var(nm_S));
        let var_Z = al.alloc(Exp::Var(nm_Z));
        let var_eq = al.alloc(Exp::Var(nm_eq));
        let var_nat = al.alloc(Exp::Var(nm_nat));
        let var_type = al.alloc(Exp::Var(nm_type));
        let var_x = al.alloc(Exp::Var(nm_x));
        let var_y = al.alloc(Exp::Var(nm_y));

        #[rustfmt::skip]
        let decl = {
            // (A : type)
            let param_A = Param { name: nm_A, ty: var_type };
            // (x : A)
            let param_x = Param { name: nm_x, ty: var_A };
            // A -> type
            let exp_arr_A_type = al.alloc(Exp::Arr(Arrow::unnamed(var_A, var_type)));
            // (==) A x x
            let exp_x_eq_x = al.alloc(Exp::App(var_eq, var_A));
            let exp_x_eq_x = al.alloc(Exp::App(exp_x_eq_x, var_x));
            let exp_x_eq_x = al.alloc(Exp::App(exp_x_eq_x, var_x));
            // (==) (A : type) (x : A) : A -> type
            let sig_eq = al.alloc(Sig {
                name: nm_eq,
                params: al.alloc_slice_copy(&[param_A, param_x]),
                ret_ty: exp_arr_A_type,
            });
            // refl : (==) A x x
            let sig_refl = al.alloc(Sig {
                name: nm_refl,
                params: &[],
                ret_ty: exp_x_eq_x,
            });
            // data (==) {...}
            al.alloc(Decl::Data {
                loc_data: loc,
                sig: sig_eq,
                ctors: std::slice::from_ref(al.alloc(&*sig_refl)),
            })
        };

        assert_eq!(
            format!("{decl}"),
            "data (==) (A : type) (x : A) : A -> type { refl : (==) A x x; };",
        );

        let exp = {
            let exp_x_x = al.alloc(Exp::App(var_x, var_x));
            let exp_y_y = al.alloc(Exp::App(var_y, var_y));
            let exp_app = al.alloc(Exp::App(exp_x_x, exp_y_y));
            let exp_fn_y = al.alloc(Exp::Lam(Lambda::untyped(nm_y, exp_app)));
            let par_x_nat = Param {
                name: nm_x,
                ty: var_nat,
            };
            let exp_fn_x = al.alloc(Exp::Lam(Lambda::typed(par_x_nat, exp_fn_y)));
            exp_fn_x
        };

        assert_eq!(format!("{exp}"), "fn (x : nat) => fn y => x x (y y)");

        let decl = {
            let app_S_Z = al.alloc(Exp::App(var_S, var_Z));
            let par_x_B = Param {
                name: nm_x,
                ty: var_B,
            };
            let arr_B_C = al.alloc(Exp::Arr(Arrow::named(par_x_B, var_C)));
            let arr_A_B_C = al.alloc(Exp::Arr(Arrow::unnamed(var_A, arr_B_C)));
            al.alloc(Decl::Assert {
                loc_assert: loc,
                exp: app_S_Z,
                ty: arr_A_B_C,
            })
        };

        assert_eq!(format!("{decl}"), "assert S Z : A -> (x : B) -> C;");

        let exp = {
            let exp_S_y = al.alloc(Exp::App(var_S, var_y));
            let exp_S_S_y = al.alloc(Exp::App(var_S, exp_S_y));
            let pat_Z = al.alloc(Pat::Var(nm_Z));
            let pat_S = al.alloc(Pat::Var(nm_S));
            let pat_y = al.alloc(Pat::Var(nm_y));
            let pat_S_y = al.alloc(Pat::App(pat_S, pat_y));
            let cases = [(&*pat_Z, &*var_Z), (&*pat_S_y, &*exp_S_S_y)];
            al.alloc(Exp::Mat(Match {
                subject: var_x,
                cases: al.alloc_slice_copy(&cases),
            }))
        };

        assert_eq!(format!("{exp}"), "match x { Z => Z; S y => S (S y); }");
    }
}
