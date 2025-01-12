use feml::intern::Intern;
use feml::parse::Parser;
use feml::token::Tokenizer;
use std::process::ExitCode;

static INPUT: &str = "
def f : (P : A -> type) -> (Q : A -> type) -> (x : A) -> P x == Q x =
  todo;
";

fn main() -> ExitCode {
    let int = Intern::new();
    let mut prs = Parser::new(&int);
    let mut tkz = Tokenizer::new(INPUT);
    for result in &mut tkz {
        let (loc, tk) = match result {
            Ok(x) => x,
            Err(e) => {
                eprint!("error: input:{}: {}", e.loc(), e);
                return ExitCode::FAILURE;
            }
        };
        match prs.feed(loc, tk) {
            Ok(()) => {}
            Err(e) => {
                eprint!("error: input:{}: {}", e.loc(), e);
                return ExitCode::FAILURE;
            }
        };
    }
    let tree = match prs.end_of_file(tkz.loc()) {
        Ok(x) => x,
        Err(e) => {
            eprint!("error: input:{}: {}", e.loc(), e);
            return ExitCode::FAILURE;
        }
    };
    let decl = tree.decls()[0];
    println!("{}", tree.display_decl(&int, decl));
    ExitCode::SUCCESS
}
