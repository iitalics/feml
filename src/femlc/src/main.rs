use feml::elaborate;
use feml::evaluate::evaluate;
use feml::parse::{self, Parser};
use feml::parse_tree;
use feml::token::{self, Loc, Tokenizer};
use feml::value;

use std::fmt;
use std::process::ExitCode;

#[derive(Debug, thiserror::Error)]
#[error(transparent)]
enum Error {
    Token(#[from] token::Error),
    Parse(#[from] parse::Error),
    Elab(#[from] elaborate::Error),
}

impl Error {
    fn loc(&self) -> Loc {
        match self {
            Error::Token(e) => e.loc(),
            Error::Parse(e) => e.loc(),
            Error::Elab(e) => e.loc(),
        }
    }
}

struct Long<'a>(&'a Error);

impl Error {
    fn long(&self) -> Long<'_> {
        Long(self)
    }
}

impl fmt::Display for Long<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "input:{}: error: {}", self.0.loc(), self.0)
    }
}

fn parse<'a, 'i>(
    al: &'a parse_tree::Allocator,
    input: &'i str,
) -> Result<Vec<&'a parse_tree::Decl<'a, 'i>>, Error> {
    let mut prs = Parser::new(al);
    let mut tkz = Tokenizer::new(input);
    for result in &mut tkz {
        let (loc, tk) = result?;
        prs.feed(loc, tk)?;
    }
    prs.end_of_file(tkz.loc()).map_err(Error::from)
}

static INPUT: &str = "
assert (fn (A : type) => fn (x : A) => A) nat : nat -> nat;
";

fn main() -> ExitCode {
    let al = parse_tree::allocator();
    let decls = match parse(&al, INPUT) {
        Ok(res) => res,
        Err(e) => {
            eprintln!("{}", e.long());
            return ExitCode::FAILURE;
        }
    };

    for decl in decls {
        fn handle_decl(decl: &parse_tree::Decl<'_, '_>) -> Result<(), Error> {
            if let parse_tree::Decl::Assert { exp, ty, .. } = decl {
                let mut ctx = elaborate::Context::new();
                let ty = ctx.elab_type(&ty)?;
                let exp = ctx.elab_exp_check(exp, ty.clone())?;

                println!("{exp}");
                let val = evaluate(value::empty(), exp);
                println!("= {val} : {ty}");
            }

            Ok(())
        }

        if let Err(e) = handle_decl(decl) {
            eprintln!("{}", e.long());
        }
    }

    ExitCode::SUCCESS
}
