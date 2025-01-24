use feml::elab;
use feml::gc::{self, Gc};
use feml::interpreter::Interpreter;
use feml::parse::{self, Parser};
use feml::parse_tree;
use feml::token::{self, Loc, Tokenizer};

use std::fmt;
use std::process::ExitCode;

#[derive(Debug, thiserror::Error)]
#[error(transparent)]
enum Error {
    Token(#[from] token::Error),
    Parse(#[from] parse::Error),
    Elab(#[from] elab::Error),
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
assert (fn (f : nat -> nat) => fn (x : nat) => f (f x)) S : nat -> nat;

def two_plus (n : nat) : nat = S (S n);
#assert two_plus (two_plus Z) : nat;
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
            match decl {
                parse_tree::Decl::Assert(assert) => {
                    let ref mut gc = Gc::new();
                    let stash = gc::RootSet::new(gc);
                    let interp = Interpreter::new(gc);
                    interp.elab_chk_assert(gc, assert, &stash)?;
                    stash.swap();
                    stash.duplicate();
                    interp.normalize(gc, &stash);
                    let val = stash.restore(gc);
                    let tm = stash.restore(gc);
                    let ty = stash.restore(gc);
                    println!(
                        "ok {} : {} = {}",
                        interp.display(tm),
                        interp.display(ty),
                        interp.display(val)
                    );
                    Ok(())
                }
                parse_tree::Decl::Data(data) => {
                    println!("... skipping 'data {}' ...", data.sig.name);
                    return Ok(());
                }
                parse_tree::Decl::Def(def) => {
                    println!("... skipping 'def {}' ...", def.sig.name);
                    return Ok(());
                }
            }
        }

        if let Err(e) = handle_decl(decl) {
            eprintln!("{}", e.long());
        }
    }

    ExitCode::SUCCESS
}
