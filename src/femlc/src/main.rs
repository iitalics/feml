use feml::elaborate;
use feml::evaluate::evaluate;
use feml::parse::Parser;
use feml::parse_tree;
use feml::token::Tokenizer;
use feml::value;
use std::process::ExitCode;

fn parse<'a, 'i>(
    al: &'a parse_tree::Allocator,
    input: &'i str,
) -> Result<Vec<&'a parse_tree::Decl<'a, 'i>>, String> {
    let mut prs = Parser::new(al);
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
    let al = parse_tree::allocator();
    let decls = match parse(
        &al,
        "
assert S (S Z) : nat;
",
    ) {
        Ok(t) => t,
        Err(msg) => {
            eprint!("error: {msg}");
            return ExitCode::FAILURE;
        }
    };

    for decl in decls {
        if let parse_tree::Decl::Assert { exp, .. } = decl {
            let mut ctx = elaborate::Context::new();
            let (stx, ty) = match ctx.elab_exp_infer(exp) {
                Ok(result) => result,
                Err(e) => {
                    println!("error: input:{}: {}", e.loc(), e);
                    continue;
                }
            };
            println!("{stx}");
            let env = value::Environ::new(value::Env::Empty);
            let val = evaluate(env, &stx);
            println!("= {val} : {ty}");
        }
    }

    ExitCode::SUCCESS
}
