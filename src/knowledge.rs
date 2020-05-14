use std::fmt;

use super::*;

/// Represents knowledge about symbols.
pub enum Knowledge {
    /// A symbol has some definition.
    Def(Symbol, Expr),
    /// A reduction from a more complex expression into another by normalization.
    Red(Expr, Expr),
    /// Two expressions that are equivalent but neither normalizes the other.
    Eqv(Expr, Expr),
}

impl fmt::Display for Knowledge {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> std::result::Result<(), fmt::Error> {
        use Knowledge::*;

        match self {
            Def(a, b) => write!(w, "{} := {}", a, b)?,
            Red(a, b) => write!(w, "{} => {}", a, b)?,
            Eqv(a, b) => write!(w, "{} <=> {}", a, b)?,
        }
        Ok(())
    }
}
