#![allow(clippy::new_without_default)]

pub mod parse;
pub mod parse_tree;
pub mod token;

pub mod domain;
pub mod gc;
pub mod intern;

pub mod elab;
pub mod nbe;

pub(crate) mod pretty_print_utils {
    use std::fmt;

    pub fn open(f: &mut fmt::Formatter<'_>, prec: u32, min_prec: u32) -> fmt::Result {
        if prec > min_prec {
            write!(f, "(")?;
        }
        Ok(())
    }

    pub fn close(f: &mut fmt::Formatter<'_>, prec: u32, min_prec: u32) -> fmt::Result {
        if prec > min_prec {
            write!(f, ")")?;
        }
        Ok(())
    }
}
