use crate::domain as dmn;
use crate::domain::{Env, Lvl, Term, TermT, Type, Val, ValT};
use crate::intern::{self, Symbol};
use crate::nbe;
use crate::parse_tree as ast;
use crate::token::Loc;

use core::fmt;
use std::borrow::Cow;
use std::collections::HashMap;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("{1} not in scope")]
    NotDefined(Loc, String),
    #[error("expected {1}, got {2}")]
    TypeMismatch(Loc, String, String),
    #[error("unexpected parameter type {1}, expected {2}")]
    ParamTypeMismatch(Loc, String, String),
    #[error("expected function type, got {1}")]
    NotFunction(Loc, String),
    #[error("parameter {1} requires type annotation")]
    ParamRequiresAnnot(Loc, String),
}

impl Error {
    pub fn loc(&self) -> Loc {
        match self {
            Self::NotDefined(loc, _)
            | Self::TypeMismatch(loc, _, _)
            | Self::ParamTypeMismatch(loc, _, _)
            | Self::NotFunction(loc, _)
            | Self::ParamRequiresAnnot(loc, _) => *loc,
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct Context {
    intern_pool: intern::Pool,
    type_type: Type,
    constants: HashMap<Symbol, Type>,
    scope: Vec<Binding>,
}

struct Binding {
    name: Option<Symbol>,
    ty: Type,
    level: u32,
}

impl Context {
    pub fn new() -> Self {
        let intern_pool = intern::Pool::new();

        // initialize constants
        let sym_type = intern_pool.intern("type");
        let sym_nat = intern_pool.intern("nat");
        let type_type = dmn::val_con(sym_type);
        let type_nat = dmn::val_con(sym_nat);
        let mut constants = HashMap::new();
        constants.insert(sym_type, type_type); // type : type
        constants.insert(sym_nat, type_type); // nat : type
        constants.insert(
            // Z : nat
            intern_pool.intern("Z"),
            type_nat,
        );
        constants.insert(
            // S : nat
            intern_pool.intern("S"),
            dmn::val_arrow(type_nat, type_nat),
        );

        Self {
            intern_pool,
            type_type,
            constants,
            scope: vec![],
        }
    }

    fn bind(&mut self, name: Option<Symbol>, ty: Type) {
        let level = self.level() + 1;
        self.scope.push(Binding { name, ty, level })
    }

    fn unbind(&mut self) {
        let last = self.scope.pop();
        assert!(last.is_some());
    }

    fn find(&self, name: Symbol) -> Option<&Binding> {
        self.scope.iter().rev().find(|b| b.name == Some(name))
    }

    fn level(&self) -> Lvl {
        self.scope.len() as u32
    }

    fn env(&self) -> Env {
        dmn::env_neutral(self.level())
    }

    pub fn eval(&self, tm: Term) -> Val {
        nbe::eval(self.env(), tm)
    }

    pub fn reify(&self, val: Val) -> Term {
        nbe::reify(self.level(), val)
    }
}

pub fn elab_term_syn(cx: &mut Context, exp: &ast::Exp<'_, '_>) -> Result<(Term, Type)> {
    match exp {
        ast::Exp::Var(x) => syn_var(cx, x),
        ast::Exp::App(fun, arg) => syn_app(cx, fun, arg),
        ast::Exp::Arr(arr) => chk_arrow(cx, arr).map(|tm| (tm, cx.type_type)),
        ast::Exp::Lam(lam) => syn_lambda(cx, lam),
        ast::Exp::Mat(_) => unimplemented!("match elab"),
    }
}

pub fn elab_term_chk(cx: &mut Context, exp: &ast::Exp<'_, '_>, goal_ty: Type) -> Result<Term> {
    // some expressions can exploit bidir checking type
    #[allow(clippy::single_match)]
    match exp {
        ast::Exp::Lam(lambda) => {
            return chk_lambda(cx, lambda, goal_ty);
        }
        _ => {}
    }
    // fall back to inference and then comparing the types
    let (tm, inf_ty) = elab_term_syn(cx, exp)?;
    if !is_compatible(cx, inf_ty, goal_ty) {
        return Err(Error::TypeMismatch(
            exp.loc(),
            cx.display(goal_ty).to_string(),
            cx.display(inf_ty).to_string(),
        ));
    }
    Ok(tm)
}

pub fn elab_type(cx: &mut Context, exp: &ast::Exp<'_, '_>) -> Result<Type> {
    let tm = elab_term_chk(cx, exp, cx.type_type)?;
    let ty = cx.eval(tm);
    Ok(ty)
}

fn syn_var(cx: &mut Context, x: &ast::Name<'_>) -> Result<(Term, Type)> {
    let sym = x.intern(&cx.intern_pool);
    if let Some(binding) = cx.find(sym) {
        let idx = cx.level() - binding.level;
        return Ok((dmn::term_var(idx), binding.ty));
    }
    if let Some(&ty) = cx.constants.get(&sym) {
        return Ok((dmn::term_con(sym), ty));
    }
    Err(Error::NotDefined(x.loc, x.to_string()))
}

fn syn_app(
    cx: &mut Context,
    fun: &ast::Exp<'_, '_>,
    arg: &ast::Exp<'_, '_>,
) -> Result<(Term, Type)> {
    let (fun_tm, fun_ty) = elab_term_syn(cx, fun)?;
    let (dom_ty, rng) = match fun_ty {
        ValT::Pi(dom_ty, rng) => (dom_ty, rng),
        _ => {
            return Err(Error::NotFunction(
                fun.loc(),
                cx.display(fun_ty).to_string(),
            ))
        }
    };
    let arg_tm = elab_term_chk(cx, arg, dom_ty)?;
    let arg = cx.eval(arg_tm);
    let rng_ty = nbe::close(rng, arg);
    Ok((dmn::term_app(fun_tm, arg_tm), rng_ty))
}

fn syn_lambda(cx: &mut Context, lambda: &ast::Lambda<'_, '_>) -> Result<(Term, Type)> {
    let param_sym = lambda.name.intern(&cx.intern_pool);
    let dom_ty = match lambda.param {
        Some(param) => elab_type(cx, param.ty)?,
        None => {
            return Err(Error::ParamRequiresAnnot(
                lambda.name.loc,
                lambda.name.to_string(),
            ))
        }
    };
    let (body_tm, rng_tm) = {
        cx.bind(Some(param_sym), dom_ty);
        let result = elab_term_syn(cx, lambda.body);
        let result = result.map(|(tm, ty)| (tm, cx.reify(ty)));
        cx.unbind();
        result?
    };
    let body = dmn::Abs {
        name: Some(param_sym),
        body: body_tm,
    };
    let rng = dmn::Abs {
        name: Some(param_sym),
        body: rng_tm,
    };
    Ok((dmn::term_fn(body), dmn::val_pi(dom_ty, rng, cx.env())))
}

fn chk_lambda(cx: &mut Context, lambda: &ast::Lambda<'_, '_>, goal_ty: Type) -> Result<Term> {
    let (goal_dom_ty, goal_rng) = match goal_ty {
        ValT::Pi(dom_ty, rng) => (dom_ty, rng),
        _ => {
            return Err(Error::NotFunction(
                lambda.loc(),
                cx.display(goal_ty).to_string(),
            ))
        }
    };
    let param_sym = lambda.name.intern(&cx.intern_pool);
    let dom_ty = match lambda.param {
        Some(param) => {
            let param_ann_ty = elab_type(cx, param.ty)?;
            if !is_compatible(cx, param_ann_ty, goal_dom_ty) {
                return Err(Error::ParamTypeMismatch(
                    param.loc(),
                    cx.display(param_ann_ty).to_string(),
                    cx.display(goal_dom_ty).to_string(),
                ));
            }
            // use the provided type rather than the bidir inferred type. this improves
            // clarity of error messages even though the types are checked to be
            // compatible
            param_ann_ty
        }
        None => goal_dom_ty,
    };
    let body_tm = {
        cx.bind(Some(param_sym), dom_ty);
        let arg = dmn::val_neu(cx.level());
        let body_ty = nbe::close(goal_rng, arg);
        let result = elab_term_chk(cx, lambda.body, body_ty);
        cx.unbind();
        result?
    };
    let body = dmn::Abs {
        name: Some(param_sym),
        body: body_tm,
    };
    Ok(dmn::term_fn(body))
}

fn chk_arrow(cx: &mut Context, arrow: &ast::Arrow<'_, '_>) -> Result<Term> {
    let dom_tm = elab_term_chk(cx, arrow.dom, cx.type_type)?;
    let dom_ty = cx.eval(dom_tm);
    let param_sym = arrow.param.map(|p| p.name.intern(&cx.intern_pool));
    let rng_tm = {
        cx.bind(param_sym, dom_ty);
        let result = elab_term_chk(cx, arrow.rng, cx.type_type);
        cx.unbind();
        result?
    };
    let rng = dmn::Abs {
        name: param_sym,
        body: rng_tm,
    };
    Ok(dmn::term_pi(dom_tm, rng))
}

fn is_compatible(cx: &Context, ty1: Type, ty2: Type) -> bool {
    let tm1 = cx.reify(ty1);
    let tm2 = cx.reify(ty2);
    tm1.alpha_eq(tm2)
}

// == Pretty printing ==

pub struct DisplayTerm<'c> {
    cx: &'c Context,
    term: Term,
}

impl Context {
    pub fn display(&self, val: Val) -> DisplayTerm<'_> {
        self.display_term(self.reify(val))
    }

    pub fn display_term(&self, term: Term) -> DisplayTerm<'_> {
        DisplayTerm { cx: self, term }
    }
}

impl fmt::Display for DisplayTerm<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tf = TermFormatter::new(&self.cx.intern_pool);
        for binding in self.cx.scope.iter() {
            let name = binding.name.map_or(BLANK, |n| tf.fresh(n));
            tf.names.push(name);
        }
        tf.fmt(f, self.term, 0)
    }
}

struct TermFormatter<'s> {
    intern_pool: &'s intern::Pool,
    names: Vec<Cow<'s, str>>,
}

const BLANK: Cow<str> = Cow::Borrowed("");

impl<'s> TermFormatter<'s> {
    fn new(intern_pool: &'s intern::Pool) -> Self {
        Self {
            intern_pool,
            names: vec![],
        }
    }

    fn fresh(&self, symbol: Symbol) -> Cow<'s, str> {
        let orig_id = self.intern_pool.get(symbol);
        let mut new_id = Cow::Borrowed(orig_id);
        let mut tries = 1;
        'retry: loop {
            for prev_id in self.names.iter() {
                if prev_id == &new_id {
                    // add integer suffix to generate new name
                    // x -> x.2 -> x.3 -> ...
                    tries += 1;
                    new_id = Cow::Owned(format!("{orig_id}.{tries}"));
                    continue 'retry;
                }
            }
            return new_id;
        }
    }

    fn fmt(&mut self, f: &mut fmt::Formatter<'_>, term: Term, prec: u32) -> fmt::Result {
        use crate::pretty_print_utils::{close, open};
        match term {
            TermT::Con(con) => write!(f, "{}", self.intern_pool.get(*con)),
            TermT::Var(idx) => {
                assert!((*idx as usize) < self.names.len());
                let i = self.names.len() - (*idx as usize) - 1;
                write!(f, "{}", self.names[i])
            }
            TermT::App(fun, arg) => {
                open(f, prec, 2)?;
                self.fmt(f, fun, 2)?;
                write!(f, " ")?;
                self.fmt(f, arg, 3)?;
                close(f, prec, 2)
            }
            TermT::Fn(abs) => {
                let name = abs.name.map_or(BLANK, |n| self.fresh(n));
                open(f, prec, 0)?;
                write!(f, "fn {name} => ")?;
                self.names.push(name);
                let result = self.fmt(f, abs.body, 0);
                self.names.pop();
                result?;
                close(f, prec, 0)
            }
            TermT::Pi(dom, rng) => {
                open(f, prec, 1)?;
                match rng.name {
                    Some(n) => {
                        let name = self.fresh(n);
                        write!(f, "({name} : ")?;
                        self.fmt(f, dom, 0)?;
                        write!(f, ") -> ")?;
                        self.names.push(name);
                        let result = self.fmt(f, rng.body, 1);
                        self.names.pop();
                        result?;
                    }
                    None => {
                        self.fmt(f, dom, 2)?;
                        write!(f, " -> ")?;
                        self.names.push(BLANK);
                        let result = self.fmt(f, rng.body, 1);
                        self.names.pop();
                        result?;
                    }
                }
                close(f, prec, 1)
            }
        }
    }
}
