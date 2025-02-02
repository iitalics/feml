use std::mem;

use crate::parse_tree;
use crate::parse_tree::{Arrow, Exp, Lambda, Match, MatchCase, Pat, Ty};
use crate::parse_tree::{Assert, Decl, Def, Name, Param, Sig};
use crate::token::{Keyword, Loc, Token};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("expected {1}, found {2} instead")]
    Expected(Loc, &'static str, String),
    #[error("unexpected {1}, was looking for {2}")]
    Unexpected(Loc, String, &'static str),
    #[error("reached end of file earlier than expected")]
    UnexpectedEOF(Loc),
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

fn expected(loc: Loc, a: &'static str, b: Token<'_>) -> Error {
    Error::Expected(loc, a, b.to_string())
}

fn unexpected(loc: Loc, a: Token<'_>, b: &'static str) -> Error {
    Error::Unexpected(loc, a.to_string(), b)
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
    // named operator (a <*> b)
    Name(Name<'i>),
}

pub struct Parser<'i, 'a> {
    ptal: &'a parse_tree::Allocator,
    decls: Vec<&'a Decl<'i, 'a>>,
    state: S<'i, 'a>,
    reduce_name: Vec<RName>,
    reduce_sig: Vec<RSig>,
    reduce_exp: Vec<RExp<'i, 'a>>,
    reduce_param: Vec<RParam<'i>>,
    reduce_pat: Vec<RPat<'i, 'a>>,
    reduce_match_case: Vec<RMatchCase<'i, 'a>>,
    param_list_stack: Vec<Vec<Param<'i, 'a>>>,
    match_case_stack: Vec<Vec<MatchCase<'i, 'a>>>,
}

// parser state
enum S<'i, 'a> {
    Error,
    Top,
    Def,
    DefEq(Loc, &'a Sig<'i, 'a>),
    DefSm(Loc, &'a Sig<'i, 'a>, &'a Ty<'i, 'a>),
    Assert,
    AssertCl(Loc, &'a Exp<'i, 'a>),
    AssertSm(Loc, &'a Exp<'i, 'a>, &'a Ty<'i, 'a>),
    Name,
    NameOp(Loc),
    NameOpRP(Name<'i>),
    Sig,
    SigParams(Name<'i>),
    Param,
    ParamName,
    ParamCl(Name<'i>),
    ParamRP(Name<'i>, &'a Ty<'i, 'a>),
    Exp,
    Infix(Prec),
    InfixOp(Prec, &'a Exp<'i, 'a>),
    App,
    AppArg(&'a Exp<'i, 'a>),
    Term,
    TermLP(Loc),
    TermRP(&'a Exp<'i, 'a>),
    InfixMaybeParamId(Prec, Loc),
    InfixMaybeParamCl(Prec, Name<'i>),
    InfixArrowAr(Prec, Param<'i, 'a>),
    Lam,
    LamParam,
    LamUntypedAr(Name<'i>),
    LamTypedAr(Param<'i, 'a>),
    Match,
    MatchLC(&'a Exp<'i, 'a>),
    MatchCases(&'a Exp<'i, 'a>),
    CaseRr(&'a Pat<'i, 'a>),
    CaseSm(&'a Pat<'i, 'a>, &'a Exp<'i, 'a>),
    Pat,
    PatAppArg(&'a Pat<'i, 'a>),
    PatTerm,
    PatTermLP(Loc),
    PatTermRP(&'a Pat<'i, 'a>),
}

// parser reduction for Name type
enum RName {
    SigParams,
    ExpVar,
    LamUntypedAr,
    PatVar,
}

// parser reduction for Sig type
enum RSig {
    DefEq(Loc),
}

// parser reduction for Param type
enum RParam<'i> {
    SigParam(Name<'i>),
    InfixArrowAr(Prec),
    LamTypedAr,
}

// parser reduction for Exp type
enum RExp<'i, 'a> {
    DefSm(Loc, &'a Sig<'i, 'a>),
    AssertCl(Loc),
    AssertSm(Loc, &'a Exp<'i, 'a>),
    Sig(Name<'i>),
    ParamRP(Name<'i>),
    InfixOp(Prec),
    InfixOpApply(Prec, &'a Exp<'i, 'a>, Op<'i>),
    AppArg,
    AppApply(&'a Exp<'i, 'a>),
    TermRP,
    InfixArrowApply(Prec, Param<'i, 'a>),
    LamUntyped(Name<'i>),
    LamTyped(Param<'i, 'a>),
    MatchLC,
    CaseSm(&'a Pat<'i, 'a>),
}

enum RPat<'i, 'a> {
    CaseRr,
    PatAppArg,
    PatAppApply(&'a Pat<'i, 'a>),
    PatTermRP,
}

enum RMatchCase<'i, 'a> {
    MatchCases(&'a Exp<'i, 'a>),
}

impl<'i, 'a> Parser<'i, 'a> {
    pub fn new(allocator: &'a parse_tree::Allocator) -> Self {
        Self {
            ptal: allocator,
            decls: vec![],
            state: S::Top,
            reduce_name: vec![],
            reduce_sig: vec![],
            reduce_exp: vec![],
            reduce_param: vec![],
            reduce_pat: vec![],
            reduce_match_case: vec![],
            param_list_stack: vec![],
            match_case_stack: vec![],
        }
    }

    pub fn feed(&mut self, loc: Loc, t: Token<'i>) -> Result<(), Error> {
        loop {
            match mem::replace(&mut self.state, S::Error) {
                S::Error => panic!("cannot process token in error state"),

                // <top> ::= <assert> | <def>
                S::Top => match t {
                    Token::Kw(Keyword::Def) => {
                        self.state = S::Def;
                        continue;
                    }
                    Token::Kw(Keyword::Assert) => {
                        self.state = S::Assert;
                        continue;
                    }
                    _ => return Err(unexpected(loc, t, "beginning of declaration")),
                },

                // <assert> ::=
                //   "assert" <exp> ":" <ty> ";"
                S::Assert => match t {
                    Token::Kw(Keyword::Assert) => {
                        self.reduce_exp.push(RExp::AssertCl(loc));
                        self.state = S::Exp;
                        break;
                    }
                    _ => return Err(expected(loc, "'assert'", t)),
                },
                S::AssertCl(loc_assert, exp) => match t {
                    Token::Cl => {
                        self.reduce_exp.push(RExp::AssertSm(loc_assert, exp));
                        self.state = S::Exp;
                        break;
                    }
                    _ => return Err(expected(loc, "':' after expression", t)),
                },
                S::AssertSm(loc_assert, exp, ty) => match t {
                    Token::Sm => {
                        let decl = Assert {
                            loc_assert,
                            exp,
                            ty,
                        };
                        let decl = self.ptal.alloc(Decl::Assert(decl));
                        self.decls.push(decl);
                        self.state = S::Top;
                        break;
                    }
                    _ => return Err(expected(loc, "';' after type", t)),
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
                        let def = Def { loc_def, sig, body };
                        let decl = self.ptal.alloc(Decl::Def(def));
                        self.decls.push(decl);
                        self.state = S::Top;
                        break;
                    }
                    _ => return Err(expected(loc, "';' after expression", t)),
                },

                // <name> ::=
                //   <ident> | "(" <oper> ")"
                S::Name => match t {
                    Token::Ident(id) => {
                        let name = Name::ident(loc, id);
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
                        let name = Name::operator(loc_lp, op);
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
                    self.param_list_stack.push(vec![]);
                    self.reduce_name.push(RName::SigParams);
                    self.state = S::Name;
                    continue;
                }
                S::SigParams(name) => match t {
                    Token::LP => {
                        self.reduce_param.push(RParam::SigParam(name));
                        self.state = S::Param;
                        continue;
                    }
                    Token::Cl => {
                        self.reduce_exp.push(RExp::Sig(name));
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
                    Token::Ident(id) => {
                        let name = Name::ident(loc, id);
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
                //   <infix>
                //   <lambda>
                //   <match>
                S::Exp => match t {
                    Token::Kw(Keyword::Fn) => {
                        self.state = S::Lam;
                        continue;
                    }
                    Token::Kw(Keyword::Match) => {
                        self.state = S::Match;
                        continue;
                    }
                    _ => {
                        self.state = S::Infix(Prec::arrow());
                        continue;
                    }
                },

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
                                let name = Name::operator(loc, op);
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
                    Token::Ident(id) => {
                        // currently seen "(id" so we have to be prepared for expr of the
                        // form "(id : ty) -> ..."
                        let name = Name::ident(loc, id);
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

                // <lambda> ::=
                //   "fn" <lparam> "=>" <exp>
                // <lparam> ::=
                //   <id> | <param>
                S::Lam => match t {
                    Token::Kw(Keyword::Fn) => {
                        self.state = S::LamParam;
                        break;
                    }
                    _ => return Err(expected(loc, "'fn'", t)),
                },
                S::LamParam => match t {
                    Token::Ident(_) => {
                        self.reduce_name.push(RName::LamUntypedAr);
                        self.state = S::Name;
                        continue;
                    }
                    Token::LP => {
                        self.reduce_param.push(RParam::LamTypedAr);
                        self.state = S::Param;
                        continue;
                    }
                    _ => return Err(expected(loc, "name or '(name : ty)'", t)),
                },
                state @ (S::LamUntypedAr(_) | S::LamTypedAr(_)) => match t {
                    Token::Rr => {
                        self.reduce_exp.push(match state {
                            S::LamUntypedAr(n) => RExp::LamUntyped(n),
                            S::LamTypedAr(p) => RExp::LamTyped(p),
                            _ => unreachable!(),
                        });
                        self.state = S::Exp;
                        break;
                    }
                    _ => return Err(expected(loc, "'=>' after lambda parameter", t)),
                },

                // <match> ::=
                //   "match" <exp> "{" {<case>} "}"
                // <case> ::=
                //   <pat> "=>" <exp> ";"
                S::Match => match t {
                    Token::Kw(Keyword::Match) => {
                        self.reduce_exp.push(RExp::MatchLC);
                        self.state = S::Exp;
                        break;
                    }
                    _ => return Err(expected(loc, "'match'", t)),
                },
                S::MatchLC(subject) => match t {
                    Token::LC => {
                        self.match_case_stack.push(vec![]);
                        self.state = S::MatchCases(subject);
                        break;
                    }
                    _ => return Err(expected(loc, "'{' after expression", t)),
                },
                S::MatchCases(subject) => match t {
                    Token::RC => {
                        let cases = self.match_case_stack.pop().unwrap();
                        let cases = self.ptal.alloc_slice_copy(&cases);
                        let mtch = Match { subject, cases };
                        let mat = self.ptal.alloc(Exp::Mat(mtch));
                        self.reduce_exp(mat);
                        break;
                    }
                    _ => {
                        self.reduce_match_case.push(RMatchCase::MatchCases(subject));
                        self.reduce_pat.push(RPat::CaseRr);
                        self.state = S::Pat;
                        continue;
                    }
                },
                S::CaseRr(pat) => match t {
                    Token::Rr => {
                        self.reduce_exp.push(RExp::CaseSm(pat));
                        self.state = S::Exp;
                        break;
                    }
                    _ => return Err(expected(loc, "'{' after expression", t)),
                },
                S::CaseSm(pat, exp) => match t {
                    Token::Sm => {
                        self.reduce_match_case((pat, exp));
                        break;
                    }
                    _ => return Err(expected(loc, "'{' after expression", t)),
                },

                // <pat> ::=
                //   {<pterm>}+
                // <pterm> ::=
                //   "_"
                //   "(" <pat> ")"
                //   <name>
                S::Pat => {
                    self.reduce_pat.push(RPat::PatAppArg);
                    self.state = S::PatTerm;
                    continue;
                }
                S::PatAppArg(head) => match t {
                    Token::Ident(_) | Token::LP | Token::Kw(Keyword::Wildcard) => {
                        self.reduce_pat.push(RPat::PatAppApply(head));
                        self.state = S::PatTerm;
                        continue;
                    }
                    _ => {
                        self.reduce_pat(head);
                        continue;
                    }
                },
                S::PatTerm => match t {
                    Token::Ident(_) => {
                        self.reduce_name.push(RName::PatVar);
                        self.state = S::Name;
                        continue;
                    }
                    Token::LP => {
                        self.state = S::PatTermLP(loc);
                        break;
                    }
                    Token::Kw(Keyword::Wildcard) => {
                        let any = self.ptal.alloc(Pat::Any(loc));
                        self.reduce_pat(any);
                        break;
                    }
                    _ => return Err(unexpected(loc, t, "pattern")),
                },
                S::PatTermLP(loc_lp) => match t {
                    Token::Oper(_) => {
                        self.reduce_name.push(RName::PatVar);
                        self.state = S::NameOp(loc_lp);
                        continue;
                    }
                    _ => {
                        self.reduce_pat.push(RPat::PatTermRP);
                        self.state = S::Pat;
                        continue;
                    }
                },
                S::PatTermRP(pat) => match t {
                    Token::RP => {
                        self.reduce_pat(pat);
                        break;
                    }
                    _ => return Err(expected(loc, "')'", t)),
                },
            }
        }
        Ok(())
    }

    pub fn end_of_file(self, loc: Loc) -> Result<Vec<&'a Decl<'a, 'i>>, Error> {
        match self.state {
            S::Error => panic!("cannot process EOF in error state"),
            S::Top => Ok(self.decls),
            _ => Err(Error::UnexpectedEOF(loc)),
        }
    }

    fn reduce_name(&mut self, name: Name<'i>) {
        match self.reduce_name.pop().unwrap() {
            RName::SigParams => self.state = S::SigParams(name),
            RName::LamUntypedAr => self.state = S::LamUntypedAr(name),
            RName::ExpVar => {
                let var = self.ptal.alloc(Exp::Var(name));
                self.reduce_exp(var);
            }
            RName::PatVar => {
                let var = self.ptal.alloc(Pat::Var(name));
                self.reduce_pat(var);
            }
        }
    }

    fn reduce_sig(&mut self, sig: &'a Sig<'i, 'a>) {
        match self.reduce_sig.pop().unwrap() {
            RSig::DefEq(loc) => self.state = S::DefEq(loc, sig),
        }
    }

    fn reduce_exp(&mut self, exp: &'a Exp<'i, 'a>) {
        match self.reduce_exp.pop().unwrap() {
            RExp::DefSm(loc, sig) => self.state = S::DefSm(loc, sig, exp),
            RExp::AssertCl(loc) => self.state = S::AssertCl(loc, exp),
            RExp::AssertSm(loc, e) => self.state = S::AssertSm(loc, e, exp),
            RExp::ParamRP(name) => self.state = S::ParamRP(name, exp),
            RExp::AppArg => self.state = S::AppArg(exp),
            RExp::InfixOp(prec) => self.state = S::InfixOp(prec, exp),
            RExp::TermRP => self.state = S::TermRP(exp),
            RExp::MatchLC => self.state = S::MatchLC(exp),
            RExp::CaseSm(pat) => self.state = S::CaseSm(pat, exp),
            RExp::Sig(name) => {
                let params = self.param_list_stack.pop().unwrap();
                let params = self.ptal.alloc_slice_copy(&params);
                let sig = self.ptal.alloc(Sig {
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
                        self.ptal.alloc(Exp::Arr(arrow))
                    }
                    Op::Name(op) => {
                        // ((op lhs) exp)
                        let fun = self.ptal.alloc(Exp::Var(op));
                        let app = self.ptal.alloc(Exp::App(fun, lhs));
                        self.ptal.alloc(Exp::App(app, exp))
                    }
                };
                self.state = S::InfixOp(prec, app);
            }
            RExp::AppApply(head) => {
                let app = self.ptal.alloc(Exp::App(head, exp));
                self.state = S::AppArg(app);
            }
            RExp::InfixArrowApply(prec, param) => {
                // (name : ty) -> exp
                let arrow = Arrow::named(param, exp);
                let arr = self.ptal.alloc(Exp::Arr(arrow));
                self.state = S::InfixOp(prec, arr);
            }
            RExp::LamUntyped(name) => {
                let lambda = Lambda::untyped(name, exp);
                let lam = self.ptal.alloc(Exp::Lam(lambda));
                // TODO: turn tail call into loop
                self.reduce_exp(lam);
            }
            RExp::LamTyped(param) => {
                let lambda = Lambda::typed(param, exp);
                let lam = self.ptal.alloc(Exp::Lam(lambda));
                self.reduce_exp(lam);
            }
        }
    }

    fn reduce_param(&mut self, param: Param<'i, 'a>) {
        match self.reduce_param.pop().unwrap() {
            RParam::InfixArrowAr(prec) => self.state = S::InfixArrowAr(prec, param),
            RParam::LamTypedAr => self.state = S::LamTypedAr(param),
            RParam::SigParam(name) => {
                let params = self.param_list_stack.last_mut().unwrap();
                params.push(param);
                self.state = S::SigParams(name);
            }
        }
    }

    fn reduce_pat(&mut self, pat: &'a Pat<'i, 'a>) {
        match self.reduce_pat.pop().unwrap() {
            RPat::CaseRr => self.state = S::CaseRr(pat),
            RPat::PatTermRP => self.state = S::PatTermRP(pat),
            RPat::PatAppArg => self.state = S::PatAppArg(pat),
            RPat::PatAppApply(head) => {
                let app = self.ptal.alloc(Pat::App(head, pat));
                self.state = S::PatAppArg(app);
            }
        }
    }

    fn reduce_match_case(&mut self, case: MatchCase<'i, 'a>) {
        match self.reduce_match_case.pop().unwrap() {
            RMatchCase::MatchCases(subject) => {
                let cases = self.match_case_stack.last_mut().unwrap();
                cases.push(case);
                self.state = S::MatchCases(subject);
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::token::Tokenizer;

    #[test]
    fn test_needs_drop() {
        assert!(!std::mem::needs_drop::<S<'_, '_>>());
        assert!(!std::mem::needs_drop::<RName>());
        assert!(!std::mem::needs_drop::<RSig>());
        assert!(!std::mem::needs_drop::<RExp<'_, '_>>());
        assert!(!std::mem::needs_drop::<RParam<'_>>());
        assert!(!std::mem::needs_drop::<RPat<'_, '_>>());
        assert!(!std::mem::needs_drop::<RMatchCase<'_, '_>>());
    }

    #[test]
    fn test_parse_print() {
        static INPUT: &str = "
def f : (Q : A -> type) -> (x : A)
     -> P == Q
     -> P x == Q x
=
  x + (y + w) * z;

def const (A : type) (B : type)
: A -> B -> A
= fn x => fn (y : B) => x;

def twice (n : nat) : nat = match n {
  Z => Z;
  S n' => S (S (twice n'));
};

assert match x { (::) (S n) ((::) _ nil) => x; } : nat;
";

        let ptal = parse_tree::allocator();
        let mut prs = Parser::new(&ptal);
        let mut tkz = Tokenizer::new(INPUT);
        for r in &mut tkz {
            let (loc, t) = r.unwrap();
            prs.feed(loc, t).unwrap();
        }
        let decls = prs.end_of_file(tkz.loc()).unwrap();

        assert_eq!(
            format!("{}", decls[0]),
            "
def f : (Q : A -> type) -> (x : A) -> (==) P Q -> (==) (P x) (Q x) = (+) x ((*) ((+) y w) z);
"
            .trim()
        );

        assert_eq!(
            format!("{}", decls[1]),
            "
def const (A : type) (B : type) : A -> B -> A = fn x => fn (y : B) => x;
"
            .trim()
        );

        assert_eq!(
            format!("{}", decls[2]),
            "
def twice (n : nat) : nat = match n { Z => Z; S n' => S (S (twice n')); };
"
            .trim()
        );

        assert_eq!(
            format!("{}", decls[3]),
            "
assert match x { (::) (S n) ((::) _ nil) => x; } : nat;
"
            .trim()
        );
    }
}
