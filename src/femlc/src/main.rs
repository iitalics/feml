use feml::elaborate::Context;
use feml::intern::Intern;
use feml::parse::Parser;
use feml::parse_tree::{Decl, ParseTree};
use feml::token::Tokenizer;
use std::process::ExitCode;

fn parse<'i>(intern: &'i Intern, input: &str) -> Result<ParseTree<'i>, String> {
    let mut prs = Parser::new(intern);
    let mut tkz = Tokenizer::new(input);
    for result in &mut tkz {
        let (loc, tk) = match result {
            Ok(x) => x,
            Err(e) => return Err(format!("input:{}: {}", e.loc(), e)),
        };
        match prs.feed(loc, tk) {
            Ok(()) => {}
            Err(e) => return Err(format!("input:{}: {}", e.loc(), e)),
        };
    }
    match prs.end_of_file(tkz.loc()) {
        Ok(x) => Ok(x),
        Err(e) => Err(format!("input:{}: {}", e.loc(), e)),
    }
}

fn main() -> ExitCode {
    let int = Intern::new();
    let tree = match parse(
        &int,
        "
assert (fn x => S x (fn y => x) x) : A -> A -> A;
",
    ) {
        Ok(t) => t,
        Err(msg) => {
            eprint!("error: {msg}");
            return ExitCode::FAILURE;
        }
    };

    for decl in tree.decls() {
        if let Decl::Assert { exp, .. } = tree.view_decl(decl) {
            let mut ctx = Context::new(&int, &tree);
            match ctx.elab_exp(*exp) {
                Ok(stx) => {
                    println!("{}", tree.display_exp(&int, *exp));
                    println!("--> {:?}", stx);
                }
                Err(feml::elaborate::Error::NotDefined(loc, x)) => {
                    println!("error: input:{loc}: {} not defined", int.get(x));
                }
            }
        }
    }

    ExitCode::SUCCESS
}
