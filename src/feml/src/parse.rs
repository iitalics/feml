use std::fmt;
use std::mem;

use crate::intern::Intern;
use crate::parse_tree::{Arrow, Decl, Exp, Name, Param, ParseTree, Sig};
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
    // arrow operator (a -> b)
    Arrow,
    // named operator (a * b)
    Name(Name<'i>),
}

// parser state
enum S<'i> {
    Error,
    Top,
    Def,
    DefEq(Loc, SigHnd),
    DefSm(Loc, SigHnd, TyHnd),
    Name,
    NameOp(Loc),
    NameOpRP(Name<'i>),
    Sig,
    SigParams(Name<'i>, Vec<Param<'i>>),
    Param,
    ParamName,
    ParamCl(Name<'i>),
    ParamRP(Name<'i>, TyHnd),
    Exp,
    Infix(Prec),
    InfixOp(Prec, ExpHnd),
    App,
    AppArg(ExpHnd),
    Term,
    TermLP(Loc),
    TermRP(ExpHnd),
    InfixMaybeParamId(Prec, Loc),
    InfixMaybeParamCl(Prec, Name<'i>),
    InfixArrowAr(Prec, Param<'i>),
}

// parser reduction for Name type
enum RName {
    SigParams,
    ExpVar,
}

// parser reduction for Sig type
enum RSig {
    DefEq(Loc),
}

// parser reduction for Param type
enum RParam<'i> {
    SigParam(Name<'i>, Vec<Param<'i>>),
    InfixArrowAr(Prec),
}

// parser reduction for Exp type
enum RExp<'i> {
    DefSm(Loc, SigHnd),
    Sig(Name<'i>, Vec<Param<'i>>),
    ParamRP(Name<'i>),
    InfixOp(Prec),
    InfixOpApply(Prec, ExpHnd, Op<'i>),
    AppArg,
    AppApply(ExpHnd),
    TermRP,
    InfixArrowApply(Prec, Param<'i>),
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
                        self.reduce_sig.push(RSig::DefEq(loc));
                        self.state = S::Sig;
                        break;
                    }
                    _ => return Err(expected(loc, "'def'", t)),
                },
                S::DefEq(loc_def, sig) => match t {
                    Token::Eq => {
                        self.reduce_exp.push(RExp::DefSm(loc_def, sig));
                        self.state = S::Exp;
                        break;
                    }
                    _ => return Err(expected(loc, "'=' after signature", t)),
                },
                S::DefSm(loc_def, sig, body) => match t {
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
                    self.reduce_name.push(RName::SigParams);
                    self.state = S::Name;
                    continue;
                }
                S::SigParams(name, params) => match t {
                    Token::LP => {
                        self.reduce_param.push(RParam::SigParam(name, params));
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
                        self.state = S::ParamName;
                        break;
                    }
                    _ => return Err(expected(loc, "'('", t)),
                },
                S::ParamName => match t {
                    // FIXME: currently this only allows params to be <id>, but the BNF
                    // says we should support <name>, ie "def f ((+) : A) ..."
                    Token::Ident(ident) => {
                        let name = Name::ident(loc, self.intern.intern(ident));
                        self.state = S::ParamCl(name);
                        break;
                    }
                    _ => return Err(expected(loc, "identifier", t)),
                },
                S::ParamCl(name) => match t {
                    Token::Cl => {
                        self.reduce_exp.push(RExp::ParamRP(name));
                        self.state = S::Exp;
                        break;
                    }
                    _ => return Err(expected(loc, "':'", t)),
                },
                S::ParamRP(name, ty) => match t {
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
                //   <infix> "->" <infix>
                //   <param> "->" <infix>
                S::Infix(prec) => match t {
                    // if an expr starts with "(" at the highest precedence level then we
                    // have to be prepared for expr of the form "(x : t) -> e"
                    Token::LP if prec.binds_rhs(Prec::arrow()) => {
                        self.state = S::InfixMaybeParamId(prec, loc);
                        break;
                    }
                    _ => {
                        self.reduce_exp.push(RExp::InfixOp(prec));
                        self.state = S::App;
                        continue;
                    }
                },
                S::InfixOp(prec, lhs) => {
                    // Some if t is an operator that we should parse, otherwise None and
                    // we should stop parsing operators.
                    let op_and_prec = match t {
                        Token::Ar => {
                            let op_prec = Prec::arrow();
                            prec.binds_rhs(op_prec).then_some((Op::Arrow, op_prec))
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

                // <infix> ::= ... | <param> "->" <infix>
                S::InfixMaybeParamId(prec, loc_lp) => match t {
                    Token::Ident(ident) => {
                        // currently seen "(id" so we have to be prepared for expr of the
                        // form "(id : ty) -> ..."
                        let name = Name::ident(loc, self.intern.intern(ident));
                        self.state = S::InfixMaybeParamCl(prec, name);
                        break;
                    }
                    _ => {
                        // encountered something else so revert parse state to what it
                        // would have been if we abandoned looking for arrow types
                        self.reduce_exp.push(RExp::InfixOp(prec));
                        self.reduce_exp.push(RExp::AppArg);
                        self.state = S::TermLP(loc_lp);
                        continue;
                    }
                },
                S::InfixMaybeParamCl(prec, name) => match t {
                    Token::Cl => {
                        // currently seen "(id :" so now we commit to this being arrow
                        // syntax
                        self.reduce_param.push(RParam::InfixArrowAr(prec));
                        self.reduce_exp.push(RExp::ParamRP(name));
                        self.state = S::Exp;
                        break;
                    }
                    _ => {
                        // see previous comment but this time its much worse
                        self.reduce_exp.push(RExp::InfixOp(prec));
                        self.reduce_exp.push(RExp::AppArg);
                        self.reduce_exp.push(RExp::TermRP);
                        self.reduce_exp.push(RExp::InfixOp(Prec::arrow()));
                        self.reduce_exp.push(RExp::AppArg);
                        self.reduce_name.push(RName::ExpVar);
                        self.reduce_name(name);
                        continue;
                    }
                },
                S::InfixArrowAr(prec, param) => match t {
                    Token::Ar => {
                        self.reduce_exp.push(RExp::InfixArrowApply(prec, param));
                        self.state = S::Infix(Prec::arrow());
                        break;
                    }
                    _ => return Err(expected(loc, "'->' after named function parameter", t)),
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
            RName::SigParams => self.state = S::SigParams(name, vec![]),
            RName::ExpVar => {
                let var = self.parse_tree.alloc_exp(Exp::Var(name));
                self.reduce_exp(var);
            }
        }
    }

    fn reduce_sig(&mut self, sig: SigHnd) {
        match self.reduce_sig.pop().unwrap() {
            RSig::DefEq(loc) => self.state = S::DefEq(loc, sig),
        }
    }

    fn reduce_exp(&mut self, exp: ExpHnd) {
        match self.reduce_exp.pop().unwrap() {
            RExp::DefSm(loc, sig) => self.state = S::DefSm(loc, sig, exp),
            RExp::ParamRP(name) => self.state = S::ParamRP(name, exp),
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
                    Op::Arrow => {
                        // lhs -> exp
                        let arrow = Arrow::unnamed(lhs, exp);
                        self.parse_tree.alloc_exp(Exp::Arr(arrow))
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
            RExp::InfixArrowApply(prec, param) => {
                // (name : ty) -> exp
                let arrow = Arrow::named(param.name, param.ty, exp);
                let arr = self.parse_tree.alloc_exp(Exp::Arr(arrow));
                self.state = S::InfixOp(prec, arr);
            }
        }
    }

    fn reduce_param(&mut self, param: Param<'i>) {
        match self.reduce_param.pop().unwrap() {
            RParam::InfixArrowAr(prec) => self.state = S::InfixArrowAr(prec, param),
            RParam::SigParam(name, mut params) => {
                params.push(param);
                self.state = S::SigParams(name, params);
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::token::Tokenizer;

    #[test]
    fn test_parse_print() {
        static INPUT: &str = "
def f : (Q : A -> type) -> (x : A)
     -> P == Q
     -> P x == Q x
=
  x + (y + w) * z;
";

        // named infix operators get made into prefix operators with the appropriate order
        // of operations
        static OUTPUT: &str = "
def f : (Q : A -> type) -> (x : A) -> (==) P Q -> (==) (P x) (Q x) = (+) x ((*) ((+) y w) z);
";

        let int = Intern::new();
        let mut prs = Parser::new(&int);
        let mut tkz = Tokenizer::new(INPUT);
        for r in &mut tkz {
            let (loc, t) = r.unwrap();
            prs.feed(loc, t).unwrap();
        }
        let tree = prs.end_of_file(tkz.loc()).unwrap();
        let decl = tree.decls()[0];
        assert_eq!(tree.display_decl(&int, decl).to_string(), OUTPUT.trim());
    }
}
