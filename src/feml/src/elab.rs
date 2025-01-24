use crate::domain::{self, Lvl, Term, Val};
use crate::format::{display_term, DisplayTerm};
use crate::gc::{self, Gc, Hndl};
use crate::intern::Symbol;
use crate::interpreter::Interpreter;
use crate::nbe;
use crate::parse_tree as ast;
use crate::token::Loc;

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

pub struct Context<'i> {
    interp: &'i Interpreter,
    stash: gc::RootSet,
    scope: Vec<Option<Symbol>>,
    scope_stash: gc::RootSet,
}

impl<'i> Context<'i> {
    pub fn new(interp: &'i Interpreter, gc: &Gc) -> Self {
        let stash = gc::RootSet::new(gc);
        let type_type = interp.constant(gc, Symbol::TYPE).unwrap();
        let idx_type = stash.save(type_type);
        assert_eq!(idx_type, 0);

        Self {
            interp,
            stash,
            scope: vec![],
            scope_stash: gc::RootSet::new(gc),
        }
    }

    /// Display a term in this context. This properly pretty prints free variables in the
    /// term which refer to bindings currently in scope.
    pub fn display<'gc>(&self, term: Hndl<'gc>) -> DisplayTerm<'i, '_, 'gc> {
        display_term(self.interp.intern_pool(), &self.scope, term)
    }

    fn type_type<'gc>(&self, gc: &'gc Gc) {
        // 'type' is always instash[0]
        self.stash.save(self.stash.get(gc, 0));
    }

    /* val :: */
    pub fn bind(&mut self, name: Option<ast::Name<'_>>) -> Option<Symbol> {
        let sym = name.map(|name| name.intern(self.interp.intern_pool()));
        self.scope.push(sym);
        self.stash.transfer(&self.scope_stash);
        sym
    }

    pub fn unbind(&mut self) {
        let name = self.scope.pop();
        assert!(name.is_some());
        self.scope_stash.forget();
    }

    fn find(&self, sym: Symbol) -> Option<(usize, Lvl)> {
        for (i, binding) in self.scope.iter().enumerate() {
            if *binding == Some(sym) {
                return Some((i, (i + 1) as u32));
            }
        }
        None
    }

    fn level(&self) -> Lvl {
        self.scope.len() as u32
    }

    pub fn stash(&self) -> &gc::RootSet {
        &self.stash
    }

    fn env(&self, gc: &mut Gc) {
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
        ast::Exp::Var(x) => syn_var(gc, cx, *x),
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

fn syn_var(gc: &mut Gc, cx: &mut Context, name: ast::Name<'_>) -> Result<()> {
    let sym = name.intern(cx.interp.intern_pool());
    if let Some((ty_stash_idx, lvl)) = cx.find(sym) {
        // Γ ⊢ x ⇒ i : Γ(i)
        let idx = cx.level() - lvl;
        cx.stash.save(domain::var_term(gc, idx));
        cx.stash.save(cx.scope_stash.get(gc, ty_stash_idx));
        return Ok(());
    }
    if let Some(ty) = cx.interp.constant(&gc, sym) {
        // ⊢ c ⇒ c : T
        cx.stash.save(ty);
        cx.stash.save(domain::con_term(gc, sym));
        cx.stash.swap();
        return Ok(());
    }
    Err(Error::NotDefined(name.loc, name.to_string()))
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
    let app_tm = domain::app_term(gc, &cx.stash);
    cx.stash.save(app_tm);
    cx.stash.swap(); // :: app_tm rng_ty
    Ok(())
}

fn syn_lambda(gc: &mut Gc, cx: &mut Context, lambda: &ast::Lambda<'_, '_>) -> Result<()> {
    match lambda.param {
        Some(param) => {
            elab_type(gc, cx, param.ty)?;
        }
        None => {
            return Err(Error::ParamRequiresAnnot(
                lambda.name.loc,
                lambda.name.to_string(),
            ))
        }
    };

    cx.stash.duplicate();
    let param_sym = cx.bind(Some(lambda.name));

    elab_term_syn(gc, cx, lambda.body)?;
    cx.reify(gc);
    // :: dom_ty body_tm rng_ty_re

    cx.unbind();

    let rng_ty_re = cx.stash.restore(gc);
    cx.stash.swap();
    cx.stash.save(rng_ty_re);
    cx.env(gc);
    // :: body_ty dom rng env
    let lambda_ty = domain::pi_val(gc, param_sym, &cx.stash);
    cx.stash.save(lambda_ty);
    // :: body_tm lambda_ty

    cx.stash.swap();
    let lambda_tm = domain::fn_term(gc, param_sym, &cx.stash);
    cx.stash.save(lambda_tm);
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

    match lambda.param {
        Some(param) => {
            // if the lambda has a parameter type annotation then check it against the
            // goal type's domain
            cx.stash.save(goal_dom_ty);
            elab_type(gc, cx, param.ty)?;
            let param_ann_ty = cx.stash.restore(gc);
            let goal_dom_ty = cx.stash.restore(gc);

            // leave param_ann_ty on the stack if the check below succeeds. this improves
            // clarity of error messages even though the types are checked to be
            // compatible
            cx.stash.save(param_ann_ty);
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
        }
        None => {
            // infer domain type from the goal
            cx.stash.save(goal_dom_ty);
        }
    };

    let param_sym = cx.bind(Some(lambda.name));

    // get the expected body type by evaluating the goal type's range with a neutral
    // variable as argument
    let goal_rng_env = cx.stash.restore(gc);
    let goal_rng_ty_tm = cx.stash.restore(gc);
    cx.stash.save(goal_rng_ty_tm);
    cx.stash.save(goal_rng_env);
    cx.stash.save(domain::neu_val(gc, cx.level()));
    nbe::close(gc, &cx.stash);
    elab_term_chk(gc, cx, lambda.body)?;

    cx.unbind();

    let lambda_tm = domain::fn_term(gc, param_sym, &cx.stash);
    cx.stash.save(lambda_tm);
    Ok(())
}

fn syn_arrow(gc: &mut Gc, cx: &mut Context, arrow: &ast::Arrow<'_, '_>) -> Result<()> {
    // ⊢ t ⇒ t' : TYPE
    cx.type_type(gc);
    elab_term_chk(gc, cx, arrow.dom)?;

    // [[t']] = T
    cx.stash.duplicate();
    cx.eval(gc);
    // :: dom_ty_tm dom_ty

    let param_sym = cx.bind(arrow.name());

    // x:T ⊢ s ⇒ s' : TYPE
    cx.type_type(gc);
    elab_term_chk(gc, cx, arrow.rng)?;
    // :: dom_ty_tm rng_ty_tm

    cx.unbind();

    // ⊢ (x:t) -> s ⇒ Π(x:t').s' : TYPE
    let arrow_tm = domain::pi_term(gc, param_sym, &cx.stash);
    cx.stash.save(arrow_tm);
    cx.type_type(gc);
    Ok(())
}

// == Pretty printing ==

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
            ast::Decl::Assert(d) => (d.exp, d.ty),
            _ => panic!(),
        }
    }

    #[test]
    fn test_elab_con() {
        let ref al = ast::allocator();
        let ref mut gc = Gc::new();
        let ref interp = Interpreter::new(gc);
        let ref mut cx = Context::new(interp, gc);
        let nat = interp.intern_pool().intern("nat");
        let z = interp.intern_pool().intern("Z");

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
        let ref interp = Interpreter::new(gc);
        let ref mut cx = Context::new(interp, gc);
        let nat = interp.intern_pool().intern("nat");
        let z = interp.intern_pool().intern("Z");
        let s = interp.intern_pool().intern("S");

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
                    assert_eq!(f.con(), s);
                    assert_eq!(a.con(), z);
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
        let ref interp = Interpreter::new(gc);
        let ref mut cx = Context::new(interp, gc);

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
        let ref interp = Interpreter::new(gc);
        let ref mut cx = Context::new(interp, gc);

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
        let ref interp = Interpreter::new(gc);
        let ref mut cx = Context::new(interp, gc);

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
