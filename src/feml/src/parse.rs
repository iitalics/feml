use std::fmt;
use std::mem;

use crate::intern::{Intern, Str};
use crate::parse_tree::{Decl, Exp, Name, Param, ParseTree, Sig};
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
    reduce_sig: Vec<RSig>,
    reduce_exp: Vec<RExp<'i>>,
    reduce_param: Vec<RParam<'i>>,
}

// parser state
enum S<'i> {
    Error,
    Top,
    Def,
    Def1(Loc, SigHnd),
    Def2(Loc, SigHnd, TyHnd),
    Sig,
    Sig1(Name<'i>, Vec<Param<'i>>),
    Param,
    Param1(Loc),
    Param2(Loc, Str<'i>),
    Param3(Loc, Str<'i>, TyHnd),
    Exp,
    TermRP(ExpHnd),
    App(ExpHnd),
    Term,
}

// parser reduction for Sig type
enum RSig {
    Def1(Loc),
}

// parser reduction for Exp type
enum RExp<'i> {
    Def2(Loc, SigHnd),
    Sig(Name<'i>, Vec<Param<'i>>),
    Param3(Loc, Str<'i>),
    AppArgs,
    AppApply(ExpHnd),
    TermRP,
}

// parser reduction for Param type
enum RParam<'i> {
    Sig1(Name<'i>, Vec<Param<'i>>),
}

impl<'i> Parser<'i> {
    pub fn new(intern: &'i Intern) -> Self {
        Self {
            intern,
            parse_tree: ParseTree::new(),
            state: S::Top,
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
                S::Def1(loc, sig) => match t {
                    Token::Eq => {
                        self.reduce_exp.push(RExp::Def2(loc, sig));
                        self.state = S::Exp;
                        break;
                    }
                    _ => {
                        return Err(expected(loc, "'=' after signature", t));
                    }
                },
                S::Def2(loc, sig, body) => match t {
                    Token::Sm => {
                        self.parse_tree.alloc_decl(Decl::Def { loc, sig, body });
                        self.state = S::Top;
                        break;
                    }
                    _ => {
                        return Err(expected(loc, "';' after expression", t));
                    }
                },

                // <sig> ::= <name> {<param>} ":" <ty>
                S::Sig => match t {
                    Token::Ident(ident) => {
                        let name = Name::ident(loc, self.intern.intern(ident));
                        self.state = S::Sig1(name, vec![]);
                        break;
                    }
                    _ => {
                        return Err(expected(loc, "identifier", t));
                    }
                },
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
                    _ => {
                        return Err(expected(loc, "'(name : ty)' or ':'", t));
                    }
                },

                // <param> ::= "(" <name> ":" <ty> ")"
                S::Param => match t {
                    Token::LP => {
                        self.state = S::Param1(loc);
                        break;
                    }
                    _ => return Err(expected(loc, "'('", t)),
                },
                S::Param1(loc) => match t {
                    Token::Ident(ident) => {
                        let id = self.intern.intern(ident);
                        self.state = S::Param2(loc, id);
                        break;
                    }
                    _ => return Err(expected(loc, "identifier", t)),
                },
                S::Param2(loc, id) => match t {
                    Token::Cl => {
                        self.reduce_exp.push(RExp::Param3(loc, id));
                        self.state = S::Exp;
                        break;
                    }
                    _ => return Err(expected(loc, "':'", t)),
                },
                S::Param3(loc, id, ty) => match t {
                    Token::RP => {
                        self.reduce_param(Param { loc, id, ty });
                        break;
                    }
                    _ => return Err(expected(loc, "')'", t)),
                },

                // <exp> ::=
                //   "fn" <...>
                //   "match" <...>
                //   <app> {<oper> <app>}
                S::Exp => {
                    // TODO: Keyword::Fn
                    // TODO: Keyword::Match
                    self.reduce_exp.push(RExp::AppArgs);
                    self.state = S::Term;
                    continue;
                }

                // <app> ::=
                //   <term> |
                //   <app> <arg>
                // <arg> ::=
                //   <term>
                S::App(head) => match t {
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
                    Token::Ident(ident) => {
                        let name = Name::ident(loc, self.intern.intern(ident));
                        let var = self.parse_tree.alloc_exp(Exp::Var(name));
                        self.reduce_exp(var);
                        break;
                    }
                    Token::LP => {
                        self.reduce_exp.push(RExp::TermRP);
                        self.state = S::Exp;
                        break;
                    }
                    _ => return Err(unexpected(loc, t, "expression")),
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

    fn reduce_sig(&mut self, sig: SigHnd) {
        match self.reduce_sig.pop().unwrap() {
            RSig::Def1(loc) => self.state = S::Def1(loc, sig),
        }
    }

    fn reduce_exp(&mut self, exp: ExpHnd) {
        match self.reduce_exp.pop().unwrap() {
            RExp::Def2(loc, sig) => self.state = S::Def2(loc, sig, exp),
            RExp::Param3(loc, id) => self.state = S::Param3(loc, id, exp),
            RExp::AppArgs => self.state = S::App(exp),
            RExp::TermRP => self.state = S::TermRP(exp),
            RExp::Sig(name, params) => {
                let sig = self.parse_tree.alloc_sig(Sig {
                    name,
                    params,
                    ret_ty: exp,
                });
                self.reduce_sig(sig)
            }
            RExp::AppApply(fun) => {
                let app = self.parse_tree.alloc_exp(Exp::App(fun, exp));
                self.state = S::App(app);
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
