use feml::intern::Intern;
use feml::token::Loc;

#[allow(non_snake_case)]
#[rustfmt::skip]
fn main() {
    use feml::parse_tree::*;

    let int = Intern::new();
    let mut pt = ParseTree::new();

    let loc = Loc {
        byte: 0,
        col: 0,
        line: 0,
    };

    let id_f = int.intern("f");
    let id_x = int.intern("x");
    let id_A = int.intern("A");
    let nm_f = Name { loc, id: id_f, is_oper: false };
    let nm_x = Name { loc, id: id_x, is_oper: false };
    let nm_A = Name { loc, id: id_A, is_oper: false };
    let var_x = pt.alloc_exp(Exp::Var(nm_x));
    let var_A = pt.alloc_exp(Exp::Var(nm_A));
    let param_x = Param { loc, id: id_x, ty: var_A };
    let sig_f = pt.alloc_sig(Sig {
        name: nm_f,
        params: vec![param_x],
        ret_ty: var_A,
    });
    let decl_f = pt.alloc_decl(Decl::Def {
        loc,
        sig: sig_f,
        body: var_x,
    });

    println!("{}", pt.display_decl(&int, decl_f));

    let id_eq = int.intern("==");
    let id_refl = int.intern("refl");
    let id_type = int.intern("type");
    let nm_eq = Name { loc, id: id_eq, is_oper: true };
    let nm_refl = Name { loc, id: id_refl, is_oper: false };
    let nm_type = Name { loc, id: id_type, is_oper: false };
    let var_type = pt.alloc_exp(Exp::Var(nm_type));
    let param_A = Param { loc, id: id_A, ty: var_type };
    let exp_arr_A_type = pt.alloc_exp(Exp::Arr(Arr {
        dom: var_A,
        rng: var_type,
    }));
    let exp_x_eq_x = pt.alloc_exp(Exp::App(App {
        head: nm_eq,
        args: vec![var_x, var_x],
    }));
    let sig_eq = pt.alloc_sig(Sig {
        name: nm_eq,
        params: vec![param_A, param_x],
        ret_ty: exp_arr_A_type,
    });
    let sig_refl = pt.alloc_sig(Sig {
        name: nm_refl,
        params: vec![],
        ret_ty: exp_x_eq_x,
    });
    let decl_eq = pt.alloc_decl(Decl::Data {
        loc,
        sig: sig_eq,
        ctors: vec![sig_refl],
    });

    println!("{}", pt.display_decl(&int, decl_eq));
}

