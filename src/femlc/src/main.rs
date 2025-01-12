use feml::intern::Intern;
use feml::token::Loc;

#[allow(non_snake_case)]
#[rustfmt::skip]
fn main() {
    use feml::parse_tree::*;

    let int = Intern::new();
    let mut pt = ParseTree::new();
    let loc = Loc::default();

    let str_id = int.intern("id");
    let str_x = int.intern("x");
    let str_A = int.intern("A");
    let nm_id = Name { loc, id: str_id, is_operator: false };
    let nm_x = Name { loc, id: str_x, is_operator: false };
    let nm_A = Name { loc, id: str_A, is_operator: false };
    let var_x = pt.alloc_exp(Exp::Var(nm_x));
    let var_A = pt.alloc_exp(Exp::Var(nm_A));
    let param_x = Param { loc, id: str_x, ty: var_A };
    let sig_id = pt.alloc_sig(Sig {
        name: nm_id,
        params: vec![param_x],
        ret_ty: var_A,
    });
    let decl_id = pt.alloc_decl(Decl::Def {
        loc,
        sig: sig_id,
        body: var_x,
    });

    println!("{}", pt.display_decl(&int, decl_id));
}
