use feml::elab;
use feml::gc::{self, Gc};
use feml::interpreter::Interpreter;
use feml::parse::{self, Parser};
use feml::parse_tree;
use feml::token::{self, Loc, Tokenizer};

use std::fs::File;
use std::io::Read;
use std::process::ExitCode;
use std::{env, fmt, io};

#[derive(Debug, thiserror::Error)]
enum Error {
    #[error("{1}")]
    Parse(String, ParseError),
    #[error("{1}")]
    Elab(String, elab::Error),
}

#[derive(Debug, thiserror::Error)]
#[error(transparent)]
enum ParseError {
    Token(#[from] token::Error),
    Parse(#[from] parse::Error),
}

impl Error {
    fn name(&self) -> &str {
        match self {
            Error::Parse(n, _) | Error::Elab(n, _) => n,
        }
    }

    fn loc(&self) -> Loc {
        match self {
            Error::Parse(_, ParseError::Token(e)) => e.loc(),
            Error::Parse(_, ParseError::Parse(e)) => e.loc(),
            Error::Elab(_, e) => e.loc(),
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
        write!(f, "{}:{}: error: {}", self.0.name(), self.0.loc(), self.0)
    }
}

fn parse<'a, 'i>(
    al: &'a parse_tree::Allocator,
    input: &'i str,
) -> Result<Vec<&'a parse_tree::Decl<'a, 'i>>, ParseError> {
    let mut prs = Parser::new(al);
    let mut tkz = Tokenizer::new(input);
    for result in &mut tkz {
        let (loc, tk) = result?;
        prs.feed(loc, tk)?;
    }
    prs.end_of_file(tkz.loc()).map_err(ParseError::from)
}

fn main() -> ExitCode {
    let input_name: String;
    let mut input_rdr: Box<dyn Read>;
    let mut input = String::new();

    if let Some(path) = env::args_os().nth(1) {
        let path_str = path.to_string_lossy();
        match File::open(&path) {
            Ok(file) => {
                input_name = path_str.into_owned();
                input_rdr = Box::new(file);
            }
            Err(e) => {
                eprintln!("error opening file {:?}: {e}", path_str);
                return ExitCode::FAILURE;
            }
        }
    } else {
        println!("reading from stdin");
        input_name = "<stdin>".to_string();
        input_rdr = Box::new(io::stdin());
    }

    if let Err(e) = input_rdr.read_to_string(&mut input) {
        eprintln!("IO error: {e}");
        return ExitCode::FAILURE;
    }

    let al = parse_tree::allocator();
    let decls = match parse(&al, &input) {
        Ok(res) => res,
        Err(e) => {
            let e = Error::Parse(input_name, e);
            eprintln!("{}", e.long());
            return ExitCode::FAILURE;
        }
    };

    let ref mut gc = Gc::new();
    let mut interp = Interpreter::new(gc);

    for decl in decls {
        fn elab_decl(
            interp: &mut Interpreter,
            gc: &mut Gc,
            decl: &parse_tree::Decl<'_, '_>,
        ) -> Result<(), elab::Error> {
            match decl {
                parse_tree::Decl::Assert(assert) => {
                    let stash = gc::RootSet::new(gc);
                    interp.elab_chk_assert(gc, assert, &stash)?;
                    stash.swap();
                    stash.duplicate();
                    interp.normalize(gc, &stash);
                    let val = stash.restore(gc);
                    let tm = stash.restore(gc);
                    let ty = stash.restore(gc);
                    println!(
                        "assert {} : {} = {}",
                        interp.display(tm),
                        interp.display(ty),
                        interp.display(val)
                    );
                    Ok(())
                }
                parse_tree::Decl::Data(data) => {
                    println!("... skipping 'data {}' ...", data.sig.name);
                    Ok(())
                }
                parse_tree::Decl::Def(def) => {
                    let stash = gc::RootSet::new(gc);
                    interp.elab_chk_def(gc, def, &stash)?;
                    let ty = stash.restore(gc);
                    println!("def {} : {}", def.sig.name, interp.display(ty));
                    Ok(())
                }
            }
        }

        if let Err(e) = elab_decl(&mut interp, gc, decl) {
            let e = Error::Elab(input_name, e);
            eprintln!("{}", e.long());
            return ExitCode::FAILURE;
        }
    }

    ExitCode::SUCCESS
}
