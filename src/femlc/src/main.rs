use feml::elab2::{self as elab, elab_term_chk, elab_type};
use feml::gc::Gc;
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
                let ref mut gc = Gc::new();
                let ref mut cx = elab::Context::new(gc);
                elab_type(gc, cx, ty)?;
                cx.stash.duplicate();
                elab_term_chk(gc, cx, exp)?; // :: ty tm
                cx.stash.swap();
                cx.reify(gc);
                let ty_re = cx.stash.restore(gc);
                let tm = cx.stash.restore(gc);
                println!("> {} : {}", cx.display(tm), cx.display(ty_re));
                cx.stash.save(tm);
                cx.eval(gc);
                cx.reify(gc);
                let val_re = cx.stash.restore(gc);
                println!("= {}", cx.display(val_re));
            }

            Ok(())
        }

        if let Err(e) = handle_decl(decl) {
            eprintln!("{}", e.long());
        }
    }

    ExitCode::SUCCESS
}
