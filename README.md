# FeML

FeML is my attempt to implement dependent typechecking in Rust in a couple of weeks. The
main purpose of this was to see what it would be like, to learn more about NbE, and
because writing a garbage collector in Rust sounded fun.

## Features

FeML can do dependent typechecking for very simple terms such as lambdas and natural
numbers. Pattern matching and eliminators are currently not implemented although they
would be next if I spent more time on this.

## Usage

```
$ cat example.feml
def id (A : type) (x : A) : A = x;
assert id : (A : type) -> A -> A;
assert id nat : nat -> nat;
assert id nat Z : nat;
assert S (S Z) : nat;

$ cargo run --release -- example.feml 
   Compiling femlc v0.1.0 (/home/iitalics/code/feml/src/femlc)
    Finished `release` profile [optimized] target(s) in 0.19s
     Running `target/release/femlc example.feml`
def id : (A : type) -> (x : A) -> A
assert fn A => fn x => x : (A : type) -> A -> A = fn A => fn x => x
assert (fn A => fn x => x) nat : nat -> nat = fn x => x
assert (fn A => fn x => x) nat Z : nat = Z
assert S (S Z) : nat = S (S Z)
```

## Language syntax

The following EBNF is roughly parsed.

```
<file> ::=
  (<decl>)*

<decl> ::= 
  <def> | <assert>

<def> ::=
  "def" <sig> "=" <exp> ";"

<assert> ::=
  "assert" <exp> ":" <ty> ";"

<sig> ::=
  <name> (<param>)* ":" <ty>

<name> ::=
  <id> | "(" <operator> ")"

<param> ::=
  "(" <id> ":" <ty> ")"

<ty> ::=
  <exp>

<exp> ::=
  <name> |
  "(" <exp> ")" |
  <exp> <exp> |
  <exp> <operator> <exp> |
  "fn" <id> "=>" <exp> |
  "fn" <param> "=>" <exp> |
  <ty> "->" <ty> |
  <param> "->" <ty>
```

There is also some other syntax (like pattern matching) that is either partially parsed or
not actually interpreted correctly so I won't list it here.
