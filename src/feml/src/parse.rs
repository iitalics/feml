use std::fmt;
use std::mem;

use crate::intern::Intern;
use crate::parse_tree::{Arr, Decl, Exp, Name, Param, ParseTree, Sig};
use crate::parse_tree::{ExpHnd, SigHnd, TyHnd};
use crate::token::{Keyword, Loc, Token};

#[derive(Debug)]
pub enum Error {
    Expected(Loc, &'static str, String),
    Unexpected(Loc, String, &'static str),
    UnexpectedEOF(Loc),
}

fn expected(loc: Loc, a: &'static str, b: Token<'_>) -> Error {
    Error::Expected(loc, a, b.to_string())
}

fn unexpected(loc: Loc, a: Token<'_>, b: &'static str) -> Error {
    Error::Unexpected(loc, a.to_string(), b)
}

impl Error {
    pub fn loc(&self) -> Loc {
        match self {
            Error::Expected(loc, _, _)
            | Error::Unexpected(loc, _, _)
            | Error::UnexpectedEOF(loc) => *loc,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Expected(_, a, b) => write!(f, "expected {a}, found {b} instead"),
            Error::Unexpected(_, a, b) => write!(f, "unexpected {a}, was looking for {b}"),
            // TODO: "unclosed ...?"
            Error::UnexpectedEOF(_) => write!(f, "reached end of file earlier than expected"),
        }
    }
}

pub struct Parser<'i> {
    intern: &'i Intern,
    parse_tree: ParseTree<'i>,
    state: S<'i>,
    reduce_name: Vec<RName>,
    reduce_sig: Vec<RSig>,
    reduce_exp: Vec<RExp<'i>>,
    reduce_param: Vec<RParam<'i>>,
}

// infix operator precedence
#[derive(Copy, Clone)]
enum Prec {
    Left(i16),
    Right(i16),
}

impl Prec {
    fn arrow() -> Self {
        Prec::Right(i16::MIN)
    }

    fn by_name(op: &str) -> Self {
        match op {
            "==" => Prec::Left(4),
            "+" => Prec::Left(5),
            "*" => Prec::Left(6),
            _ => Prec::Left(2),
        }
    }

    fn binding_power(&self) -> i16 {
        match *self {
            Prec::Left(bp) | Prec::Right(bp) => bp,
        }
    }

    fn binds_rhs(&self, rhs: Prec) -> bool {
        match *self {
            Prec::Left(bp) => bp < rhs.binding_power(),
            Prec::Right(bp) => bp <= rhs.binding_power(),
        }
    }
}

enum Op<'i> {
    // arrow operator
    Arr,
    // named operator
    Name(Name<'i>),
}

// parser state
enum S<'i> {
    Error,
    Top,
    Def,
    Def1(Loc, SigHnd),
    Def2(Loc, SigHnd, TyHnd),
    Name,
    NameOp(Loc),
    NameOpRP(Name<'i>),
    Sig,
    Sig1(Name<'i>, Vec<Param<'i>>),
    Param,
    Param1,
    Param2(Name<'i>),
    Param3(Name<'i>, TyHnd),
    Exp,
    Infix(Prec),
    InfixOp(Prec, ExpHnd),
    App,
    AppArg(ExpHnd),
    Term,
    TermLP(Loc),
    TermRP(ExpHnd),
}

// parser reduction for Name type
enum RName {
    Sig1,
    ExpVar,
}

// parser reduction for Sig type
enum RSig {
    Def1(Loc),
}

// parser reduction for Param type
enum RParam<'i> {
    Sig1(Name<'i>, Vec<Param<'i>>),
}

// parser reduction for Exp type
enum RExp<'i> {
    Def2(Loc, SigHnd),
    Sig(Name<'i>, Vec<Param<'i>>),
    Param3(Name<'i>),
    InfixOp(Prec),
    InfixOpApply(Prec, ExpHnd, Op<'i>),
    AppArg,
    AppApply(ExpHnd),
    TermRP,
}

impl<'i> Parser<'i> {
    pub fn new(intern: &'i Intern) -> Self {
        Self {
            intern,
            parse_tree: ParseTree::new(),
            state: S::Top,
            reduce_name: vec![],
            reduce_sig: vec![],
            reduce_exp: vec![],
            reduce_param: vec![],
        }
    }

    pub fn feed(&mut self, loc: Loc, t: Token<'_>) -> Result<(), Error> {
        loop {
            match mem::replace(&mut self.state, S::Error) {
                S::Error => panic!("cannot process token in error state"),

                // <top> ::= <def> | <data>
                S::Top => match t {
                    Token::Kw(Keyword::Def) => {
                        self.state = S::Def;
                        continue;
                    }
                    _ => return Err(unexpected(loc, t, "'def' or 'data' declaration")),
                },

                // <def> ::=
                //   "def" <sig> "=" <exp> ";"
                S::Def => match t {
                    Token::Kw(Keyword::Def) => {
                        self.reduce_sig.push(RSig::Def1(loc));
                        self.state = S::Sig;
                        break;
                    }
                    _ => return Err(expected(loc, "'def'", t)),
                },
                S::Def1(loc_def, sig) => match t {
                    Token::Eq => {
                        self.reduce_exp.push(RExp::Def2(loc_def, sig));
                        self.state = S::Exp;
                        break;
                    }
                    _ => return Err(expected(loc, "'=' after signature", t)),
                },
                S::Def2(loc_def, sig, body) => match t {
                    Token::Sm => {
                        self.parse_tree.alloc_decl(Decl::Def { loc_def, sig, body });
                        self.state = S::Top;
                        break;
                    }
                    _ => return Err(expected(loc, "';' after expression", t)),
                },

                // <name> ::=
                //   <ident> | "(" <oper> ")"
                S::Name => match t {
                    Token::Ident(ident) => {
                        let name = Name::ident(loc, self.intern.intern(ident));
                        self.reduce_name(name);
                        break;
                    }
                    Token::LP => {
                        self.state = S::NameOp(loc);
                        break;
                    }
                    _ => return Err(expected(loc, "identifier or (operator)", t)),
                },
                S::NameOp(loc_lp) => match t {
                    Token::Oper(op) => {
                        // note: "(+)" gets assigned the "(" for its loc, not "+"
                        let name = Name::operator(loc_lp, self.intern.intern(op));
                        self.state = S::NameOpRP(name);
                        break;
                    }
                    _ => return Err(expected(loc, "operator name", t)),
                },
                S::NameOpRP(name) => match t {
                    Token::RP => {
                        self.reduce_name(name);
                        break;
                    }
                    _ => return Err(expected(loc, "')' after operator name", t)),
                },

                // <sig> ::= <name> {<param>} ":" <ty>
                S::Sig => {
                    self.reduce_name.push(RName::Sig1);
                    self.state = S::Name;
                    continue;
                }
                S::Sig1(name, params) => match t {
                    Token::LP => {
                        self.reduce_param.push(RParam::Sig1(name, params));
                        self.state = S::Param;
                        continue;
                    }
                    Token::Cl => {
                        self.reduce_exp.push(RExp::Sig(name, params));
                        self.state = S::Exp;
                        break;
                    }
                    _ => return Err(expected(loc, "'(name : ty)' or ':'", t)),
                },

                // <param> ::= "(" <name> ":" <ty> ")"
                S::Param => match t {
                    Token::LP => {
                        // TODO: "[name : ty]"
                        self.state = S::Param1;
                        break;
                    }
                    _ => return Err(expected(loc, "'('", t)),
                },
                S::Param1 => match t {
                    // FIXME: currently this only allows params to be <id>, but the BNF
                    // says we should support <name>, ie "def f ((+) : A) ..."
                    Token::Ident(ident) => {
                        let name = Name::ident(loc, self.intern.intern(ident));
                        self.state = S::Param2(name);
                        break;
                    }
                    _ => return Err(expected(loc, "identifier", t)),
                },
                S::Param2(name) => match t {
                    Token::Cl => {
                        self.reduce_exp.push(RExp::Param3(name));
                        self.state = S::Exp;
                        break;
                    }
                    _ => return Err(expected(loc, "':'", t)),
                },
                S::Param3(name, ty) => match t {
                    Token::RP => {
                        self.reduce_param(Param { name, ty });
                        break;
                    }
                    _ => return Err(expected(loc, "')'", t)),
                },

                // <exp> ::=
                //   "fn" <...>
                //   "match" <...>
                //   <infix>
                S::Exp => {
                    // TODO: Keyword::Fn
                    // TODO: Keyword::Match
                    self.state = S::Infix(Prec::arrow());
                    continue;
                }

                // <infix> ::=
                //   <app> {<oper> <app>}
                S::Infix(prec) => {
                    self.reduce_exp.push(RExp::InfixOp(prec));
                    self.state = S::App;
                    continue;
                }
                S::InfixOp(prec, lhs) => {
                    let op_and_prec = match t {
                        Token::Ar => {
                            let op_prec = Prec::arrow();
                            prec.binds_rhs(op_prec).then_some((Op::Arr, op_prec))
                        }
                        Token::Oper(op) => {
                            let op_prec = Prec::by_name(op);
                            prec.binds_rhs(op_prec).then(|| {
                                let name = Name::operator(loc, self.intern.intern(op));
                                (Op::Name(name), op_prec)
                            })
                        }
                        _ => None,
                    };

                    let Some((op, rhs_prec)) = op_and_prec else {
                        self.reduce_exp(lhs);
                        continue;
                    };

                    self.reduce_exp.push(RExp::InfixOpApply(prec, lhs, op));
                    self.state = S::Infix(rhs_prec);
                    break;
                }

                // <app> ::=
                //   <term> {<arg>}
                // <arg> ::=
                //   <term>
                S::App => {
                    self.reduce_exp.push(RExp::AppArg);
                    self.state = S::Term;
                    continue;
                }
                S::AppArg(head) => match t {
                    Token::Ident(_) | Token::LP => {
                        self.reduce_exp.push(RExp::AppApply(head));
                        self.state = S::Term;
                        continue;
                    }
                    _ => {
                        self.reduce_exp(head);
                        continue;
                    }
                },

                // <term> ::=
                //   <name>
                //   "(" <exp> ")"
                S::Term => match t {
                    Token::Ident(_) => {
                        self.reduce_name.push(RName::ExpVar);
                        self.state = S::Name;
                        continue;
                    }
                    Token::LP => {
                        self.state = S::TermLP(loc);
                        break;
                    }
                    _ => return Err(unexpected(loc, t, "expression")),
                },
                S::TermLP(loc_lp) => match t {
                    // if we see "(<oper>" then we decide that we are parsing <name> ::=
                    // (<oper>), otherwise we are parsing <term> ::= (<exp>).
                    Token::Oper(_) => {
                        self.reduce_name.push(RName::ExpVar);
                        self.state = S::NameOp(loc_lp);
                        continue;
                    }
                    _ => {
                        self.reduce_exp.push(RExp::TermRP);
                        self.state = S::Exp;
                        continue;
                    }
                },
                S::TermRP(exp) => match t {
                    Token::RP => {
                        self.reduce_exp(exp);
                        break;
                    }
                    _ => return Err(expected(loc, "')' after expression", t)),
                },
            }
        }
        Ok(())
    }

    pub fn end_of_file(self, loc: Loc) -> Result<ParseTree<'i>, Error> {
        match self.state {
            S::Error => panic!("cannot process EOF in error state"),
            S::Top => Ok(self.parse_tree),
            _ => Err(Error::UnexpectedEOF(loc)),
        }
    }

    fn reduce_name(&mut self, name: Name<'i>) {
        match self.reduce_name.pop().unwrap() {
            RName::Sig1 => self.state = S::Sig1(name, vec![]),
            RName::ExpVar => {
                let var = self.parse_tree.alloc_exp(Exp::Var(name));
                self.reduce_exp(var);
            }
        }
    }

    fn reduce_sig(&mut self, sig: SigHnd) {
        match self.reduce_sig.pop().unwrap() {
            RSig::Def1(loc) => self.state = S::Def1(loc, sig),
        }
    }

    fn reduce_exp(&mut self, exp: ExpHnd) {
        match self.reduce_exp.pop().unwrap() {
            RExp::Def2(loc, sig) => self.state = S::Def2(loc, sig, exp),
            RExp::Param3(name) => self.state = S::Param3(name, exp),
            RExp::AppArg => self.state = S::AppArg(exp),
            RExp::InfixOp(prec) => self.state = S::InfixOp(prec, exp),
            RExp::TermRP => self.state = S::TermRP(exp),
            RExp::Sig(name, params) => {
                let sig = self.parse_tree.alloc_sig(Sig {
                    name,
                    params,
                    ret_ty: exp,
                });
                self.reduce_sig(sig)
            }
            RExp::InfixOpApply(prec, lhs, op) => {
                let app = match op {
                    Op::Arr => {
                        // lhs -> exp
                        let arr = Arr { dom: lhs, rng: exp };
                        self.parse_tree.alloc_exp(Exp::Arr(arr))
                    }
                    Op::Name(op) => {
                        // ((op lhs) exp)
                        let fun = self.parse_tree.alloc_exp(Exp::Var(op));
                        let app = self.parse_tree.alloc_exp(Exp::App(fun, lhs));
                        self.parse_tree.alloc_exp(Exp::App(app, exp))
                    }
                };
                self.state = S::InfixOp(prec, app);
            }
            RExp::AppApply(head) => {
                let app = self.parse_tree.alloc_exp(Exp::App(head, exp));
                self.state = S::AppArg(app);
            }
        }
    }

    fn reduce_param(&mut self, param: Param<'i>) {
        match self.reduce_param.pop().unwrap() {
            RParam::Sig1(name, mut params) => {
                params.push(param);
                self.state = S::Sig1(name, params);
            }
        }
    }
}
