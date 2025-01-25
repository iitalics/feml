use crate::domain;
use crate::elab;
use crate::format::{display_term, DisplayTerm};
use crate::gc::{self, Gc, Hndl};
use crate::intern::{self, Symbol};
use crate::nbe;
use crate::parse_tree;

use std::collections::HashMap;

pub struct Interpreter {
    intern_pool: intern::Pool,
    defs: HashMap<Symbol, Def>,
    defs_stash: gc::RootSet,
}

enum Def {
    Constant { ty: usize },
    Expression { tm: usize, ty: usize },
}

pub enum Definition<'gc> {
    Constant { ty: Hndl<'gc> },
    Expression { tm: Hndl<'gc>, ty: Hndl<'gc> },
}

impl Interpreter {
    pub fn new(gc: &mut Gc) -> Self {
        let intern_pool = intern::Pool::new();
        let sym_type = intern_pool.intern("type");
        let sym_nat = intern_pool.intern("nat");
        let sym_s = intern_pool.intern("S");
        let sym_z = intern_pool.intern("Z");

        /* initialize constants */

        let mut defs = HashMap::new();
        let defs_stash = gc::RootSet::new(gc);
        let idx_type = defs_stash.save(domain::con_val(gc, sym_type));

        // type : type
        defs.insert(sym_type, Def::Constant { ty: idx_type });

        // nat : type
        defs.insert(sym_nat, Def::Constant { ty: idx_type });

        // Z : nat
        let idx_nat = defs_stash.save(domain::con_val(gc, sym_nat));
        defs.insert(sym_z, Def::Constant { ty: idx_nat });

        // S : nat -> nat
        let idx_arrow_nat_nat = {
            defs_stash.save(defs_stash.get(gc, idx_nat));
            defs_stash.save(defs_stash.get(gc, idx_nat));
            defs_stash.save(domain::arrow_val(gc, &defs_stash))
        };
        defs.insert(
            sym_s,
            Def::Constant {
                ty: idx_arrow_nat_nat,
            },
        );

        Self {
            intern_pool,
            defs,
            defs_stash,
        }
    }

    pub fn intern_pool(&self) -> &intern::Pool {
        &self.intern_pool
    }

    /// Display a term with no free variables.
    pub fn display<'gc>(&self, term: Hndl<'gc>) -> DisplayTerm<'_, 'static, 'gc> {
        display_term(&self.intern_pool, &[], term)
    }

    /// Get the type of a constant by the given symbol name.
    pub fn definition<'gc>(&self, gc: &'gc Gc, name: Symbol) -> Option<Definition<'gc>> {
        match *self.defs.get(&name)? {
            Def::Constant { ty } => Some(Definition::Constant {
                ty: self.defs_stash.get(gc, ty),
            }),
            Def::Expression { tm, ty } => Some(Definition::Expression {
                tm: self.defs_stash.get(gc, tm),
                ty: self.defs_stash.get(gc, ty),
            }),
        }
    }

    /// Normalize a term with no free variables.
    /* term :: term */
    pub fn normalize(&self, gc: &mut Gc, stash: &gc::RootSet) {
        stash.save(domain::empty_env());
        nbe::eval(gc, stash);
        nbe::reify(gc, 0, stash);
    }

    /* :: elab_term elab_type */
    pub fn elab_chk_assert(
        &self,
        gc: &mut Gc,
        ast: &parse_tree::Assert<'_, '_>,
        stash: &gc::RootSet,
    ) -> elab::Result<()> {
        let ref mut cx = elab::Context::new(self, gc);
        elab::elab_type(gc, cx, ast.ty)?;
        cx.stash().duplicate();
        elab::elab_term_chk(gc, cx, ast.exp)?;
        // :: ty tm
        cx.stash().transfer(stash);
        cx.reify(gc);
        cx.stash().transfer(stash);
        Ok(())
    }

    /* :: elab_type */
    pub fn elab_chk_def(
        &mut self,
        gc: &mut Gc,
        def: &parse_tree::Def<'_, '_>,
        stash: &gc::RootSet,
    ) -> elab::Result<()> {
        let ref mut cx = elab::Context::new(self, gc);
        let mut param_vars = Vec::with_capacity(def.sig.params.len());

        // introduce parameters into scope
        for param in def.sig.params {
            elab::elab_type(gc, cx, param.ty)?;
            cx.stash().duplicate();
            cx.bind(Some(param.name));
            param_vars.push(Some(param.name.intern(&self.intern_pool)));
        }

        // typecheck the body
        elab::elab_type(gc, cx, def.sig.ret_ty)?;
        cx.stash().duplicate();
        elab::elab_term_chk(gc, cx, def.body)?;
        // :: param_tys ... ret_ty body_tm

        // turn definition into expression by wrapping in lambdas
        // def f (x : t) ... : u = e  -->  fn x => ... => e
        for &var in param_vars.iter().rev() {
            cx.stash().save(domain::fn_term(gc, var, cx.stash()));
        }
        let def_tm_idx = cx.stash().transfer(&self.defs_stash);

        // reconstruct full function type from each parameter
        // def f (x : t) ... : u  -->  (x : t) ... -> u
        for &var in param_vars.iter().rev() {
            // :: param_tys ... param_ty ret_ty
            cx.reify(gc);
            cx.unbind();
            cx.env(gc);
            cx.stash().save(domain::pi_val(gc, var, cx.stash()));
            // :: param_tys ... pi_ty
        }
        // :: pi_ty
        cx.stash().duplicate();
        let def_ty_idx = cx.stash().transfer(&self.defs_stash);

        // reify type before returning
        nbe::reify(gc, 0, cx.stash());
        cx.stash().transfer(stash);

        // add as a definition
        let def_sym = def.sig.name.intern(&self.intern_pool);
        self.defs.insert(
            def_sym,
            Def::Expression {
                tm: def_tm_idx,
                ty: def_ty_idx,
            },
        );

        Ok(())
    }
}
