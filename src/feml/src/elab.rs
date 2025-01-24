use crate::domain::{self, Lvl, Term, Val};
use crate::gc::{self, Gc, Hndl};
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
    pub stash: gc::RootSet,
    intern_pool: intern::Pool,
    constants: HashMap<Symbol, usize>,
    constants_stash: gc::RootSet,
    scope: Vec<Option<Symbol>>,
    scope_stash: gc::RootSet,
}

impl Context {
    pub fn new(gc: &mut Gc) -> Self {
        let intern_pool = intern::Pool::new();
        let stash = gc::RootSet::new(gc);

        // initialize constants
        let sym_type = intern_pool.intern("type");
        let sym_nat = intern_pool.intern("nat");
        let sym_s = intern_pool.intern("S");
        let sym_z = intern_pool.intern("Z");
        let mut constants = HashMap::new();
        let constants_stash = gc::RootSet::new(gc);
        let idx_type = constants_stash.save(domain::con_val(gc, sym_type));
        assert_eq!(idx_type, 0);
        // type : type
        constants.insert(sym_type, idx_type);
        // nat : type
        constants.insert(sym_nat, idx_type);
        // Z : nat
        let idx_nat = constants_stash.save(domain::con_val(gc, sym_nat));
        constants.insert(sym_z, idx_nat);
        // S : nat -> nat
        let idx_arrow_nat_nat = {
            stash.save(constants_stash.get(gc, idx_nat));
            stash.save(constants_stash.get(gc, idx_nat));
            constants_stash.save(domain::arrow_val(gc, &stash))
        };
        constants.insert(sym_s, idx_arrow_nat_nat);

        assert!(stash.is_empty());

        Self {
            intern_pool,
            stash,
            constants,
            constants_stash,
            scope: vec![],
            scope_stash: gc::RootSet::new(gc),
        }
    }

    fn type_type<'gc>(&self, gc: &'gc Gc) {
        let idx_type = 0;
        self.stash.save(self.constants_stash.get(gc, idx_type));
    }

    fn find(&self, name: Symbol) -> Option<(usize, Lvl)> {
        for (i, binding) in self.scope.iter().enumerate() {
            if *binding == Some(name) {
                return Some((i, (i + 1) as u32));
            }
        }
        None
    }

    fn level(&self) -> Lvl {
        self.scope.len() as u32
    }

    /* :: env */
    pub fn env(&self, gc: &mut Gc) {
        self.stash.save(domain::neu_env(gc, self.level()));
    }

    /* term :: val */
    pub fn eval(&self, gc: &mut Gc) {
        self.env(gc);
        nbe::eval(gc, &self.stash);
    }

    /* val :: term */
    pub fn reify(&self, gc: &mut Gc) {
        nbe::reify(gc, self.level(), &self.stash);
    }
}

/* :: term ty */
pub fn elab_term_syn(gc: &mut Gc, cx: &mut Context, exp: &ast::Exp<'_, '_>) -> Result<()> {
    match exp {
        ast::Exp::Var(x) => syn_var(gc, cx, x),
        ast::Exp::App(fun, arg) => syn_app(gc, cx, fun, arg),
        ast::Exp::Arr(arr) => syn_arrow(gc, cx, arr),
        ast::Exp::Lam(lam) => syn_lambda(gc, cx, lam),
        ast::Exp::Mat(_) => unimplemented!("elab match expression"),
    }
}

/* goal_ty :: term */
pub fn elab_term_chk(gc: &mut Gc, cx: &mut Context, exp: &ast::Exp<'_, '_>) -> Result<()> {
    // some expressions can exploit bidir checking type
    #[allow(clippy::single_match)]
    match exp {
        ast::Exp::Lam(lambda) => return chk_lambda(gc, cx, lambda),
        _ => {}
    }

    elab_term_syn(gc, cx, exp)?;
    let inf_ty = cx.stash.restore(gc);
    let tm = cx.stash.restore(gc);
    let goal_ty = cx.stash.restore(gc);
    cx.stash.save(tm);

    // check if inferred type is compatible with goal type
    cx.stash.save(goal_ty);
    cx.stash.save(inf_ty);
    cx.reify(gc);
    cx.stash.swap();
    cx.reify(gc);
    let goal_ty_re = cx.stash.restore(gc);
    let inf_ty_re = cx.stash.restore(gc);
    if !is_alpha_eq(goal_ty_re, inf_ty_re) {
        return Err(Error::TypeMismatch(
            exp.loc(),
            cx.display(goal_ty_re).to_string(),
            cx.display(inf_ty_re).to_string(),
        ));
    }

    Ok(())
}

/* :: ty */
pub fn elab_type(gc: &mut Gc, cx: &mut Context, exp: &ast::Exp<'_, '_>) -> Result<()> {
    // check exp : 'type'
    cx.type_type(gc);
    elab_term_chk(gc, cx, exp)?;
    // evaluate 'type'-typed-term into type-value
    cx.eval(gc);
    Ok(())
}

fn is_alpha_eq(lhs: Hndl<'_>, rhs: Hndl<'_>) -> bool {
    // FIMXE: make tail recursive
    match (lhs.into(), rhs.into()) {
        (Term::Con(lhs), Term::Con(rhs)) => lhs.con() == rhs.con(),
        (Term::Var(lhs), Term::Var(rhs)) => lhs.idx() == rhs.idx(),
        (Term::App(lhs), Term::App(rhs)) => {
            is_alpha_eq(lhs.arg(), rhs.arg()) && is_alpha_eq(lhs.fun(), rhs.fun())
        }
        (Term::Fn(lhs), Term::Fn(rhs)) => is_alpha_eq(lhs.body(), rhs.body()),
        (Term::Pi(lhs), Term::Pi(rhs)) => {
            is_alpha_eq(rhs.dom(), lhs.dom()) && is_alpha_eq(lhs.rng(), rhs.rng())
        }
        (_, _) => false,
    }
}

fn syn_var(gc: &mut Gc, cx: &mut Context, x: &ast::Name<'_>) -> Result<()> {
    let sym = x.intern(&cx.intern_pool);
    if let Some((ty, lvl)) = cx.find(sym) {
        // Γ ⊢ x ⇒ i : Γ(i)
        let idx = cx.level() - lvl;
        cx.stash.save(domain::var_term(gc, idx));
        cx.stash.save(cx.scope_stash.get(gc, ty));
        return Ok(());
    }
    if let Some(&ty) = cx.constants.get(&sym) {
        // ⊢ c ⇒ c : T
        cx.stash.save(domain::con_term(gc, sym));
        cx.stash.save(cx.constants_stash.get(gc, ty));
        return Ok(());
    }
    Err(Error::NotDefined(x.loc, x.to_string()))
}

fn syn_app(
    gc: &mut Gc,
    cx: &mut Context,
    fun: &ast::Exp<'_, '_>,
    arg: &ast::Exp<'_, '_>,
) -> Result<()> {
    // ⊢ f ⇒ f' : Π(x:T).S
    elab_term_syn(gc, cx, fun)?;
    let fun_ty = cx.stash.restore(gc);
    let fun_tm = cx.stash.restore(gc);
    let (dom_ty, rng_ty_tm, env) = match fun_ty.into() {
        Val::Pi(t) => (t.dom(), t.rng(), t.env()),
        _ => {
            cx.stash.save(fun_ty);
            cx.reify(gc);
            let fun_ty_r = cx.stash.restore(gc);
            return Err(Error::NotFunction(
                fun.loc(),
                cx.display(fun_ty_r).to_string(),
            ));
        }
    };
    cx.stash.save(env);
    cx.stash.save(rng_ty_tm);
    cx.stash.save(fun_tm);

    // ⊢ a ⇐ a' : T
    cx.stash.save(dom_ty);
    elab_term_chk(gc, cx, arg)?;
    // [[a']] = A
    cx.stash.duplicate();
    cx.eval(gc);
    let arg = cx.stash.restore(gc);
    let arg_tm = cx.stash.restore(gc);

    // S' = S[A/x]
    let fun_tm = cx.stash.restore(gc);
    let rng_ty_tm = cx.stash.restore(gc);
    let env = cx.stash.restore(gc);
    cx.stash.save(fun_tm);
    cx.stash.save(arg_tm);
    cx.stash.save(rng_ty_tm);
    cx.stash.save(env);
    cx.stash.save(arg);
    nbe::close(gc, &cx.stash);

    // ⊢ f a ⇒ f' a' : S'
    let rng_ty = cx.stash.restore(gc);
    let arg_tm = cx.stash.restore(gc);
    let fun_tm = cx.stash.restore(gc);
    cx.stash.save(rng_ty);
    cx.stash.save(fun_tm);
    cx.stash.save(arg_tm);
    cx.stash.save(domain::app_term(gc, &cx.stash));
    cx.stash.swap(); // :: app_tm rng_ty
    Ok(())
}

fn syn_lambda(gc: &mut Gc, cx: &mut Context, lambda: &ast::Lambda<'_, '_>) -> Result<()> {
    let dom_ty = match lambda.param {
        Some(param) => {
            elab_type(gc, cx, param.ty)?;
            cx.stash.restore(gc)
        }
        None => {
            return Err(Error::ParamRequiresAnnot(
                lambda.name.loc,
                lambda.name.to_string(),
            ))
        }
    };

    let param_sym = lambda.name.intern(&cx.intern_pool);
    cx.scope.push(Some(param_sym));
    cx.scope_stash.save(dom_ty);

    elab_term_syn(gc, cx, lambda.body)?;
    // :: body_tm body_ty
    cx.reify(gc);
    let rng_ty_re = cx.stash.restore(gc);
    // :: body_tm

    let dom_ty = cx.scope_stash.restore(gc);
    cx.scope.pop();

    cx.stash.save(dom_ty);
    cx.stash.save(rng_ty_re);
    cx.env(gc);
    cx.stash
        .save(domain::pi_val(gc, Some(param_sym), &cx.stash));
    // :: body_tm lambda_ty

    cx.stash.swap();
    cx.stash
        .save(domain::fn_term(gc, Some(param_sym), &cx.stash));
    cx.stash.swap();
    Ok(())
}

fn chk_lambda(gc: &mut Gc, cx: &mut Context, lambda: &ast::Lambda<'_, '_>) -> Result<()> {
    let goal_ty = cx.stash.restore(gc);
    let (goal_dom_ty, goal_rng_ty_tm, goal_rng_env) = match goal_ty.into() {
        Val::Pi(t) => (t.dom(), t.rng(), t.env()),
        _ => {
            cx.stash.save(goal_ty);
            cx.reify(gc);
            let goal_ty_re = cx.stash.restore(gc);
            return Err(Error::NotFunction(
                lambda.loc(),
                cx.display(goal_ty_re).to_string(),
            ));
        }
    };
    cx.stash.save(goal_rng_ty_tm);
    cx.stash.save(goal_rng_env);

    let dom_ty = match lambda.param {
        Some(param) => {
            // if the lambda has a parameter type annotation then check it against the
            // goal type's domain
            cx.stash.save(goal_dom_ty);
            elab_type(gc, cx, param.ty)?;
            let param_ann_ty = cx.stash.restore(gc);
            let goal_dom_ty = cx.stash.restore(gc);
            cx.stash.save(param_ann_ty); // this is returned at the end of the block
            cx.stash.duplicate();
            cx.stash.save(goal_dom_ty);
            cx.reify(gc);
            cx.stash.swap();
            cx.reify(gc);
            let param_ann_ty_re = cx.stash.restore(gc);
            let goal_dom_ty_re = cx.stash.restore(gc);
            if !is_alpha_eq(param_ann_ty_re, goal_dom_ty_re) {
                return Err(Error::ParamTypeMismatch(
                    param.loc(),
                    cx.display(param_ann_ty_re).to_string(),
                    cx.display(goal_dom_ty_re).to_string(),
                ));
            }

            // use the provided type rather than the bidir inferred type. this improves
            // clarity of error messages even though the types are checked to be
            // compatible
            cx.stash.restore(gc)
        }
        None => goal_dom_ty,
    };

    let param_sym = lambda.name.intern(&cx.intern_pool);
    cx.scope.push(Some(param_sym));
    cx.scope_stash.save(dom_ty);

    // get the expected body type by evaluating the goal type's range with a neutral
    // variable as argument
    let goal_rng_env = cx.stash.restore(gc);
    let goal_rng_ty_tm = cx.stash.restore(gc);
    cx.stash.save(goal_rng_ty_tm);
    cx.stash.save(goal_rng_env);
    cx.stash.save(domain::neu_val(gc, cx.level()));
    nbe::close(gc, &cx.stash);
    elab_term_chk(gc, cx, lambda.body)?;

    cx.scope_stash.forget();
    cx.scope.pop();

    cx.stash
        .save(domain::fn_term(gc, Some(param_sym), &cx.stash));
    Ok(())
}

fn syn_arrow(gc: &mut Gc, cx: &mut Context, arrow: &ast::Arrow<'_, '_>) -> Result<()> {
    // ⊢ t ⇒ t' : TYPE
    cx.type_type(gc);
    elab_term_chk(gc, cx, arrow.dom)?;

    // [[t']] = T
    cx.stash.duplicate();
    cx.eval(gc);
    let dom_ty = cx.stash.restore(gc);

    let param_sym = arrow.param.map(|p| p.name.intern(&cx.intern_pool));
    cx.scope.push(param_sym);
    cx.scope_stash.save(dom_ty);

    // x:T ⊢ s ⇒ s' : TYPE
    cx.type_type(gc);
    elab_term_chk(gc, cx, arrow.rng)?;

    cx.scope_stash.forget();
    cx.scope.pop();

    // ⊢ (x:t) -> s ⇒ Π(x:t').s' : TYPE
    cx.stash.save(domain::pi_term(gc, param_sym, &cx.stash));
    cx.type_type(gc);
    Ok(())
}

// == Pretty printing ==

pub struct DisplayTerm<'c, 'gc> {
    cx: &'c Context,
    term: Hndl<'gc>,
}

impl Context {
    pub fn display<'gc>(&self, term: Hndl<'gc>) -> DisplayTerm<'_, 'gc> {
        DisplayTerm { cx: self, term }
    }
}

impl fmt::Display for DisplayTerm<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tf = TermFormatter::new(&self.cx.intern_pool);
        for binding in self.cx.scope.iter() {
            let name = binding.map_or(BLANK, |n| tf.fresh(n));
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

    fn fmt(&mut self, f: &mut fmt::Formatter<'_>, term: Hndl<'_>, prec: u32) -> fmt::Result {
        use crate::pretty_print_utils::{close, open};
        match term.into() {
            Term::Con(t) => write!(f, "{}", self.intern_pool.get(t.con())),
            Term::Var(t) => {
                assert!((t.idx() as usize) < self.names.len());
                let i = self.names.len() - (t.idx() as usize) - 1;
                write!(f, "{}", self.names[i])
            }
            Term::App(t) => {
                open(f, prec, 2)?;
                self.fmt(f, t.fun(), 2)?;
                write!(f, " ")?;
                self.fmt(f, t.arg(), 3)?;
                close(f, prec, 2)
            }
            Term::Fn(t) => {
                let name = t.var().map_or(BLANK, |n| self.fresh(n));
                open(f, prec, 0)?;
                write!(f, "fn {name} => ")?;
                self.names.push(name);
                let result = self.fmt(f, t.body(), 0);
                self.names.pop();
                result?;
                close(f, prec, 0)
            }
            Term::Pi(t) => {
                open(f, prec, 1)?;
                match t.var() {
                    Some(n) => {
                        let name = self.fresh(n);
                        write!(f, "({name} : ")?;
                        self.fmt(f, t.dom(), 0)?;
                        write!(f, ") -> ")?;
                        self.names.push(name);
                        let result = self.fmt(f, t.rng(), 1);
                        self.names.pop();
                        result?;
                    }
                    None => {
                        self.fmt(f, t.dom(), 2)?;
                        write!(f, " -> ")?;
                        self.names.push(BLANK);
                        let result = self.fmt(f, t.rng(), 1);
                        self.names.pop();
                        result?;
                    }
                }
                close(f, prec, 1)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parse::Parser;
    use crate::token::Tokenizer;

    fn parse<'a, 'i>(al: &'a ast::Allocator, input: &'i str) -> Vec<&'a ast::Decl<'a, 'i>> {
        let mut prs = Parser::new(al);
        let mut tkz = Tokenizer::new(input);
        for r in &mut tkz {
            let (loc, t) = r.unwrap();
            prs.feed(loc, t).unwrap();
        }
        prs.end_of_file(tkz.loc()).unwrap()
    }

    fn parse_assert<'a, 'i>(
        al: &'a ast::Allocator,
        input: &'i str,
    ) -> (&'a ast::Exp<'a, 'i>, &'a ast::Ty<'a, 'i>) {
        match parse(al, input)[0] {
            ast::Decl::Assert { exp, ty, .. } => (exp, ty),
            _ => panic!(),
        }
    }

    #[test]
    fn test_elab_con() {
        let ref al = ast::allocator();
        let ref mut gc = Gc::new();
        let ref mut cx = Context::new(gc);
        let nat = cx.intern_pool.intern("nat");
        let z = cx.intern_pool.intern("Z");

        let (exp_ast, ty_ast) = parse_assert(al, "assert Z : nat;");

        elab_type(gc, cx, ty_ast).unwrap();
        let ty = cx.stash.restore(gc);
        match ty.into() {
            Val::Con(v) => assert_eq!(v.con(), nat),
            _ => panic!(),
        }

        elab_term_syn(gc, cx, exp_ast).unwrap();
        let ty = cx.stash.restore(gc);
        let tm = cx.stash.restore(gc);
        match tm.into() {
            Term::Con(t) => assert_eq!(t.con(), z),
            _ => panic!(),
        }
        match ty.into() {
            Val::Con(v) => assert_eq!(v.con(), nat),
            _ => panic!(),
        }
        cx.stash.save(ty);
        cx.reify(gc);
        let ty = cx.stash.restore(gc);
        match ty.into() {
            Term::Con(v) => assert_eq!(v.con(), nat),
            _ => panic!(),
        }

        elab_type(gc, cx, ty_ast).unwrap();
        elab_term_chk(gc, cx, exp_ast).unwrap();
        let tm = cx.stash.restore(gc);
        match tm.into() {
            Term::Con(t) => assert_eq!(t.con(), z),
            _ => panic!(),
        }
    }

    #[test]
    fn test_elab_app() {
        let ref al = ast::allocator();
        let ref mut gc = Gc::new();
        let ref mut cx = Context::new(gc);
        let nat = cx.intern_pool.intern("nat");
        let z = cx.intern_pool.intern("Z");
        let s = cx.intern_pool.intern("S");

        let (exp_ast, ty_ast) = parse_assert(al, "assert S Z : nat;");
        elab_type(gc, cx, ty_ast).unwrap();
        cx.stash.duplicate();
        elab_term_chk(gc, cx, exp_ast).unwrap();
        cx.stash.swap();
        cx.reify(gc);
        let ty = cx.stash.restore(gc);
        let tm = cx.stash.restore(gc);
        match ty.into() {
            Term::Con(t) => assert_eq!(t.con(), nat),
            _ => panic!(),
        }
        match tm.into() {
            Term::App(t) => match (t.fun().into(), t.arg().into()) {
                (Term::Con(f), Term::Con(a)) => {
                    assert_eq!(f.con(), s, "{}", cx.intern_pool.get(f.con()));
                    assert_eq!(a.con(), z, "{}", cx.intern_pool.get(a.con()));
                }
                _ => panic!(),
            },
            _ => panic!(),
        }

        let (exp_ast, ty_ast) = parse_assert(al, "assert S (S Z) : nat;");
        elab_type(gc, cx, ty_ast).unwrap();
        cx.stash.duplicate();
        elab_term_chk(gc, cx, exp_ast).unwrap();
        cx.stash.swap();
        cx.reify(gc);
        let ty = cx.stash.restore(gc);
        let tm = cx.stash.restore(gc);
        assert_eq!(cx.display(tm).to_string(), "S (S Z)");
        assert_eq!(cx.display(ty).to_string(), "nat");
    }

    #[test]
    fn test_elab_pi() {
        let ref al = ast::allocator();
        let ref mut gc = Gc::new();
        let ref mut cx = Context::new(gc);

        let (exp_ast, _) = parse_assert(al, "assert (A : type) -> A : type;");
        elab_term_syn(gc, cx, exp_ast).unwrap();
        cx.reify(gc);
        let ty = cx.stash.restore(gc);
        let tm = cx.stash.restore(gc);
        assert_eq!(cx.display(tm).to_string(), "(A : type) -> A");
        assert_eq!(cx.display(ty).to_string(), "type");
    }

    #[test]
    fn test_elab_lam() {
        let ref al = ast::allocator();
        let ref mut gc = Gc::new();
        let ref mut cx = Context::new(gc);

        let (exp_ast, _) = parse_assert(al, "assert (fn (A : type) => fn (x : A) => x) : Z;");
        elab_term_syn(gc, cx, exp_ast).unwrap();
        cx.reify(gc);
        let ty = cx.stash.restore(gc);
        let tm = cx.stash.restore(gc);
        assert_eq!(cx.display(tm).to_string(), "fn A => fn x => x");
        assert_eq!(cx.display(ty).to_string(), "(A : type) -> (x : A) -> A");

        let (exp_ast, ty_ast) =
            parse_assert(al, "assert (fn A => fn x => x) : (A : type) -> A -> A;");
        elab_type(gc, cx, ty_ast).unwrap();
        cx.stash.duplicate();
        elab_term_chk(gc, cx, exp_ast).unwrap();
        cx.stash.swap();
        cx.reify(gc);
        let ty = cx.stash.restore(gc);
        let tm = cx.stash.restore(gc);
        assert_eq!(cx.display(tm).to_string(), "fn A => fn x => x");
        assert_eq!(cx.display(ty).to_string(), "(A : type) -> A -> A");

        let (exp_ast, ty_ast) =
            parse_assert(al, "assert (fn A => fn x => x) : (A : type) -> A -> nat;");
        elab_type(gc, cx, ty_ast).unwrap();
        cx.stash.duplicate();
        assert!(elab_term_chk(gc, cx, exp_ast).is_err());
    }

    #[test]
    fn test_elab_dep_app() {
        let ref al = ast::allocator();
        let ref mut gc = Gc::new();
        let ref mut cx = Context::new(gc);

        let (exp_ast, ty_ast) = parse_assert(al, "assert (fn (A : type) => fn (f : A -> A) => fn (x : A) => f (f x)) nat S : nat -> nat;");
        elab_type(gc, cx, ty_ast).unwrap();
        cx.stash.duplicate();
        elab_term_chk(gc, cx, exp_ast).unwrap();
        cx.stash.swap();
        cx.reify(gc);
        let ty = cx.stash.restore(gc);
        let tm = cx.stash.restore(gc);
        assert_eq!(
            cx.display(tm).to_string(),
            "(fn A => fn f => fn x => f (f x)) nat S"
        );
        assert_eq!(cx.display(ty).to_string(), "nat -> nat");

        cx.stash.save(tm);
        cx.eval(gc);
        cx.reify(gc);
        let val = cx.stash.restore(gc);
        assert_eq!(cx.display(val).to_string(), "fn x => S (S x)");

        let (exp_ast, ty_ast) = parse_assert(al, "assert (fn (A : type) => fn (f : A -> A) => fn (x : A) => f (f Z)) nat S : nat -> nat;");
        elab_type(gc, cx, ty_ast).unwrap();
        cx.stash.duplicate();
        assert!(elab_term_chk(gc, cx, exp_ast).is_err());
    }
}
