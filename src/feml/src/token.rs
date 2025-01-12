//! Tokens, source locations, tokenization.

use core::fmt;

/// Errors that might occur during tokenization.
#[derive(Debug)]
pub enum Error {
    InvalidChar(Loc, char),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::InvalidChar(loc, chr) => write!(f, "invalid char {chr:?} at {loc}"),
        }
    }
}

/// Indicates a position in the source text. All offets are stored 0-based, but line and
/// column will be `Display`'d 1-based.
#[derive(Eq, PartialEq, Debug, Copy, Clone, Default)]
pub struct Loc {
    /// Offset from start of input.
    pub byte: usize,
    /// Lines from start of input (first line will be `0`).
    pub line: usize,
    /// Column from start of line (beginning of line will be `0`).
    pub col: usize,
}

impl fmt::Display for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line + 1, self.col + 1)
    }
}

/// A syntactic token.
#[repr(u8)]
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum Token<'a> {
    LP = b'(',
    RP = b')',
    LB = b'[',
    RB = b']',
    LC = b'{',
    RC = b'}',
    Sm = b';',
    Cm = b',',
    Cl = b':',
    Eq = b'=',
    Ar = b'>', // "=>"
    Oper(&'a str),
    Ident(&'a str),
    Kw(Keyword),
}

impl Token<'_> {
    fn to_static_str(self) -> Option<&'static str> {
        match self {
            Token::LP => Some("("),
            Token::RP => Some(")"),
            Token::LB => Some("["),
            Token::RB => Some("]"),
            Token::LC => Some("{"),
            Token::RC => Some("}"),
            Token::Sm => Some(";"),
            Token::Cm => Some(","),
            Token::Cl => Some(":"),
            Token::Eq => Some("="),
            Token::Ar => Some("=>"),
            Token::Oper { .. } => None,
            Token::Ident { .. } => None,
            Token::Kw(kw) => Some(kw.name()),
        }
    }
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(s) = self.to_static_str() {
            write!(f, "'{s}'")
        } else if matches!(self, Token::Ident { .. }) {
            write!(f, "<identifier>")
        } else {
            write!(f, "<operator>")
        }
    }
}

/// A keyword token.
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum Keyword {
    Data,
    Def,
    Fn,
    Let,
    Match,
    Wildcard,
}

impl Keyword {
    pub fn name(self) -> &'static str {
        match self {
            Keyword::Data => "data",
            Keyword::Def => "def",
            Keyword::Fn => "fn",
            Keyword::Let => "let",
            Keyword::Match => "match",
            Keyword::Wildcard => "_",
        }
    }
}

fn char_is_delimiter(ch: char) -> bool {
    matches!(ch, '(' | ')' | '[' | ']' | '{' | '}' | ';' | ',')
}

fn char_to_delimiter_token(ch: char) -> Option<Token<'static>> {
    match ch {
        '(' => Some(Token::LP),
        ')' => Some(Token::RP),
        '[' => Some(Token::LB),
        ']' => Some(Token::RB),
        '{' => Some(Token::LC),
        '}' => Some(Token::RC),
        ';' => Some(Token::Sm),
        ',' => Some(Token::Cm),
        _ => None,
    }
}

fn char_is_operator(ch: char) -> bool {
    matches!(
        ch,
        '+' | '-' | '*' | '/' | '%' | '=' | '&' | '<' | '>' | '!' | '?' | ':'
    )
}

fn operator_to_token(op: &str) -> Token<'_> {
    match op {
        ":" => Token::Cl,
        "=" => Token::Eq,
        "=>" => Token::Ar,
        _ => Token::Oper(op),
    }
}

fn char_is_identifier(ch: char) -> bool {
    !char_is_delimiter(ch) && !ch.is_whitespace() && ch != '#'
}

fn ident_to_token(id: &str) -> Token<'_> {
    match id {
        "data" => Token::Kw(Keyword::Data),
        "def" => Token::Kw(Keyword::Def),
        "fn" => Token::Kw(Keyword::Fn),
        "let" => Token::Kw(Keyword::Let),
        "match" => Token::Kw(Keyword::Match),
        "_" => Token::Kw(Keyword::Wildcard),
        _ => Token::Ident(id),
    }
}

/// Drives tokenization over an underlying string.
pub struct Tokenizer<'a> {
    input: &'a str,
    byte: usize,
    line: usize,
    bol: usize,
}

impl<'a> Tokenizer<'a> {
    /// Start tokenizing the given string. The beginning of the string will be designated
    /// first line and column.
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            byte: 0,
            line: 0,
            bol: 0,
        }
    }

    fn loc(&self) -> Loc {
        Loc {
            byte: self.byte,
            line: self.line,
            col: self.byte - self.bol,
        }
    }

    /// Parse chars while the predicate `f` returns true. Starts at `ofs` and returns the
    /// final offset of the first char where the predicate fails (or the input ends).
    fn offset_while(&self, ofs: usize, f: impl Fn(char) -> bool) -> usize {
        for (i, ch) in self.input[ofs..].char_indices() {
            if !f(ch) {
                return ofs + i;
            }
        }
        self.input.len()
    }

    /// Move the input forward by `ofs` bytes. Updates the line and column info.
    fn forward(&mut self, ofs: usize) {
        for (i, b) in self.input[..ofs].bytes().enumerate() {
            if b == b'\n' {
                self.line += 1;
                self.bol = self.byte + i + 1;
            }
        }
        self.input = &self.input[ofs..];
        self.byte += ofs;
    }

    /// Skips over whitespace and comment chars. Automatically moves the input forward.
    fn skip_whitespace_and_comments(&mut self) {
        let mut ofs = 0;
        loop {
            ofs = self.offset_while(ofs, |ch| ch.is_whitespace());
            if self.input[ofs..].starts_with("#") {
                ofs = self.offset_while(ofs, |ch| ch != '\n');
            } else {
                break;
            }
        }
        self.forward(ofs);
    }

    /// Reads the next token.
    fn read_next(&mut self) -> Result<Option<(Loc, Token<'a>)>, Error> {
        self.skip_whitespace_and_comments();

        // get loc of token before we advance the input
        let loc = self.loc();

        // peek at immediate char in input
        let (ch, ch_end) = {
            let mut char_iter = self.input[0..].char_indices();
            let Some((_, ch)) = char_iter.next() else {
                // end of file
                return Ok(None);
            };
            (ch, char_iter.offset())
        };

        let (tk, end) = {
            if let Some(delim) = char_to_delimiter_token(ch) {
                (delim, ch_end)
            } else if char_is_operator(ch) {
                let end = self.offset_while(0, char_is_operator);
                let op = &self.input[..end];
                (operator_to_token(op), end)
            } else if char_is_identifier(ch) {
                let end = self.offset_while(0, char_is_identifier);
                let id = &self.input[..end];
                (ident_to_token(id), end)
            } else {
                return Err(Error::InvalidChar(loc, ch));
            }
        };

        self.forward(end);
        Ok(Some((loc, tk)))
    }
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = Result<(Loc, Token<'a>), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        self.read_next().transpose()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_tokenizer() {
        static INPUT: &str = "
data (==) [A : type] (a : A) : A -> type {
  refl : a == a;
};

def sym (p : x == y) : y == x = match p {
  relf => refl;
};

let _ = sym refl;
";
        let mut tkz = Tokenizer::new(INPUT);
        let mut next = || {
            let (loc, tk) = tkz.next().unwrap().unwrap();
            (loc.line, loc.col, tk)
        };
        use Keyword::*;
        use Token::*;

        assert_eq!(next(), (1, 0, Kw(Data)));
        assert_eq!(next(), (1, 5, LP));
        assert_eq!(next(), (1, 6, Oper("==")));
        assert_eq!(next(), (1, 8, RP));
        assert_eq!(next(), (1, 10, LB));
        assert_eq!(next(), (1, 11, Ident("A")));
        assert_eq!(next(), (1, 13, Cl));
        assert_eq!(next(), (1, 15, Ident("type")));
        assert_eq!(next(), (1, 19, RB));
        assert_eq!(next(), (1, 21, LP));
        assert_eq!(next(), (1, 22, Ident("a")));
        assert_eq!(next(), (1, 24, Cl));
        assert_eq!(next(), (1, 26, Ident("A")));
        assert_eq!(next(), (1, 27, RP));
        assert_eq!(next(), (1, 29, Cl));
        assert_eq!(next(), (1, 31, Ident("A")));
        assert_eq!(next(), (1, 33, Oper("->")));
        assert_eq!(next(), (1, 36, Ident("type")));
        assert_eq!(next(), (1, 41, LC));
        assert_eq!(next(), (2, 2, Ident("refl")));
        assert_eq!(next(), (2, 7, Cl));
        assert_eq!(next(), (2, 9, Ident("a")));
        assert_eq!(next(), (2, 11, Oper("==")));
        assert_eq!(next(), (2, 14, Ident("a")));
        assert_eq!(next(), (2, 15, Sm));
        assert_eq!(next(), (3, 0, RC));
        assert_eq!(next(), (3, 1, Sm));
        assert_eq!(next(), (5, 0, Kw(Def)));
        assert_eq!(next(), (5, 4, Ident("sym")));
        assert_eq!(next(), (5, 8, LP));
        assert_eq!(next(), (5, 9, Ident("p")));
        assert_eq!(next(), (5, 11, Cl));
        assert_eq!(next(), (5, 13, Ident("x")));
        assert_eq!(next(), (5, 15, Oper("==")));
        assert_eq!(next(), (5, 18, Ident("y")));
        assert_eq!(next(), (5, 19, RP));
        assert_eq!(next(), (5, 21, Cl));
        assert_eq!(next(), (5, 23, Ident("y")));
        assert_eq!(next(), (5, 25, Oper("==")));
        assert_eq!(next(), (5, 28, Ident("x")));
        assert_eq!(next(), (5, 30, Eq));
        assert_eq!(next(), (5, 32, Kw(Match)));
        assert_eq!(next(), (5, 38, Ident("p")));
        assert_eq!(next(), (5, 40, LC));
        assert_eq!(next(), (6, 2, Ident("relf")));
        assert_eq!(next(), (6, 7, Ar));
        assert_eq!(next(), (6, 10, Ident("refl")));
        assert_eq!(next(), (6, 14, Sm));
        assert_eq!(next(), (7, 0, RC));
        assert_eq!(next(), (7, 1, Sm));
        assert_eq!(next(), (9, 0, Kw(Let)));
        assert_eq!(next(), (9, 4, Kw(Wildcard)));
        assert_eq!(next(), (9, 6, Eq));
        assert_eq!(next(), (9, 8, Ident("sym")));
        assert_eq!(next(), (9, 12, Ident("refl")));
        assert_eq!(next(), (9, 16, Sm));
        assert!(tkz.next().is_none());
    }
}
