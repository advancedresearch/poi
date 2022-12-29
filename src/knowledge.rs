use std::fmt;

use super::*;

/// Represents knowledge about symbols.
#[derive(Clone, Debug)]
pub enum Knowledge {
    /// A symbol has some definition.
    Def(Symbol, Expr),
    /// A reduction from a more complex expression into another by normalization.
    Red(Expr, Expr),
    /// Two expressions that are equivalent but neither normalizes the other.
    Eqv(Expr, Expr),
    /// Two expressions that are equivalent but evaluates from left to right.
    EqvEval(Expr, Expr),
}

impl fmt::Display for Knowledge {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> std::result::Result<(), fmt::Error> {
        use Knowledge::*;

        let mut display = |op: &str, a: &Expr, b: &Expr| -> std::result::Result<(), fmt::Error> {
            let rule = true;
            let parens = false;
            a.display(w, parens, rule)?;
            write!(w, " {} ", op)?;
            b.display(w, parens, rule)?;
            Ok(())
        };
        match self {
            Def(a, b) => {
                let rule = true;
                let parens = false;
                a.display(w, rule)?;
                write!(w, " := ")?;
                b.display(w, parens, rule)?;
            }
            Red(a, b) => display("=>", a, b)?,
            Eqv(a, b) => display("<=>", a, b)?,
            EqvEval(a, b) => display("<=>>", a, b)?,
        }
        Ok(())
    }
}

impl<'a> From<&'a str> for Knowledge {
    fn from(val: &'a str) -> Knowledge {
        match parse_data_str(val, &[]) {
            Ok(ParseData::Knowledge(k)) => k[0].clone(),
            Ok(ParseData::Expr(_)) => panic!("Expected knowledge, found expression"),
            Err(err) => panic!("ERROR:\n{}", err),
        }
    }
}
