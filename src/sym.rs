use std::sync::Arc;
use std::fmt;
use super::Expr;

/// Contains symbols and operators on symbols.
#[derive(Clone, PartialEq, Debug)]
pub enum Symbol {
    /// The wildcard symbol `_`.
    Any,
    /// A variable bound from context.
    ///
    /// This can be anything.
    Var(Arc<String>),
    /// A head-tail pattern match on a tuple.
    ///
    /// This requires the tuple to have at least length 2.
    /// It is to avoid cycles between reductions.
    HeadTail(Box<Expr>, Box<Expr>),
    /// A value variable.
    ///
    /// This requires the expression to be `Ret` variant.
    /// It is used in special rules such as `(\k)(x) => \k`.
    RetVar(Arc<String>),
    /// Compute a binary function.
    ///
    /// This is used when the right side of the rule computes something from two left side expressions.
    BinopRetVar(Arc<String>, Arc<String>, Box<Symbol>),
    /// Compute a unary function.
    ///
    /// This is used when the right side of the rule computes something from a left side expression.
    UnopRetVar(Arc<String>, Box<Symbol>),
    /// A function without domain constraints.
    NoConstrVar(Arc<String>),
    /// `\false`.
    False1,
    /// `not`.
    Not,
    /// `id` for booleans.
    Idb,
    /// `\true`.
    True1,
    /// `and`.
    And,
    /// `or`.
    Or,
    /// `eq` for booleans.
    Eqb,
    /// `xor`.
    Xor,
    /// `nand`.
    Nand,
    /// `nor`.
    Nor,
    /// `exc`.
    Exc,
    /// `imply`.
    Imply,
    /// `fst` for booleans.
    Fstb,
    /// `snd` for booleans.
    Sndb,
    /// `even`.
    Even,
    /// `odd`.
    Odd,
    /// `add`.
    Add,
    /// `sub`.
    Sub,
    /// `mul`.
    Mul,
    /// `div`.
    Div,
    /// `ln`.
    Ln,
    /// `exp`.
    Exp,
    /// `len`.
    Len,
    /// `concat`.
    Concat,
    /// `sum`.
    Sum,
    /// `min2`.
    Min2,
    /// `max2`.
    Max2,
    /// `min`.
    Min,
    /// `max`.
    Max,
    /// `mul_mat`.
    MulMat,
    /// `det`.
    Det,
    /// `dim`.
    Dim,
    /// `fst`.
    Fst,
    /// `snd`.
    Snd,
    /// Generic `id`.
    Id,
    /// Generic `eq`.
    Eq,
    /// `if`.
    ///
    /// This is used in Boolean functions.
    If,
}

impl fmt::Display for Symbol {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> std::result::Result<(), fmt::Error> {
        use Symbol::*;

        match self {
            False1 => write!(w, "false1")?,
            Not => write!(w, "not")?,
            Idb => write!(w, "idb")?,
            True1 => write!(w, "true1")?,
            And => write!(w, "and")?,
            Or => write!(w, "or")?,
            Eqb => write!(w, "eqb")?,
            Xor => write!(w, "xor")?,
            Nand => write!(w, "nand")?,
            Nor => write!(w, "nor")?,
            Exc => write!(w, "exc")?,
            Imply => write!(w, "imply")?,
            Fstb => write!(w, "fstb")?,
            Sndb => write!(w, "sndb")?,
            Even => write!(w, "even")?,
            Odd => write!(w, "odd")?,
            Add => write!(w, "add")?,
            Sub => write!(w, "sub")?,
            Mul => write!(w, "mul")?,
            Div => write!(w, "div")?,
            Ln => write!(w, "ln")?,
            Exp => write!(w, "exp")?,
            Len => write!(w, "len")?,
            Concat => write!(w, "concat")?,
            Sum => write!(w, "sum")?,
            Min2 => write!(w, "min2")?,
            Max2 => write!(w, "max2")?,
            Min => write!(w, "min")?,
            Max => write!(w, "max")?,
            MulMat => write!(w, "mul_mat")?,
            Det => write!(w, "det")?,
            Dim => write!(w, "dim")?,
            Fst => write!(w, "fst")?,
            Snd => write!(w, "snd")?,
            Id => write!(w, "id")?,
            Eq => write!(w, "eq")?,
            If => write!(w, "if")?,
            Any => write!(w, "_")?,
            Var(x) | NoConstrVar(x) => write!(w, "{}", x)?,
            RetVar(x) => write!(w, "\\{}", x)?,
            HeadTail(x, y) => write!(w, "[{}, {}..]", x, y)?,
            BinopRetVar(x, y, f) => {
                match **f {
                    Add => write!(w, "{} + {}", x, y)?,
                    Sub => write!(w, "{} - {}", x, y)?,
                    Mul => write!(w, "{} * {}", x, y)?,
                    Eq => write!(w, "{} == {}", x, y)?,
                    Concat => write!(w, "{} ++ {}", x, y)?,
                    _ => write!(w, "{:?}", self)?,
                }
            }
            UnopRetVar(x, f) => {
                match **f {
                    Len => write!(w, "compute::len({})", x)?,
                    _ => write!(w, "{:?}", self)?,
                }
            }
            // _ => write!(w, "{:?}", self)?,
        }
        Ok(())
    }
}
