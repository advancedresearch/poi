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
    /// A list variable.
    ListVar(Arc<String>),
    /// A list variable of length 1.
    ///
    /// Lifts the value out of the list at binding.
    Singleton(Arc<String>),
    /// A head-tail pattern match on a tuple.
    ///
    /// This requires the tuple to have at least length 2.
    /// It is to avoid cycles between reductions.
    HeadTailTup(Box<Expr>, Box<Expr>),
    /// A head-tail pattern match on a list.
    ///
    /// This requires the list to have at least length 2.
    /// It is to avoid cycles between reductions.
    HeadTailList(Box<Expr>, Box<Expr>),
    /// A value variable.
    ///
    /// This requires the expression to be `Ret` variant.
    /// It is used in special rules such as `(\k)(x) => \k`.
    RetVar(Arc<String>),
    /// A variable that is not a value variable.
    NotRetVar(Arc<String>),
    /// Compute a binary function.
    ///
    /// This is used when the right side of the rule computes something from two left side expressions.
    BinopRetVar(Arc<String>, Arc<String>, Box<Symbol>),
    /// Compute a ternary function.
    ///
    /// This is used when the right side of the rule computes something from three left side expressions.
    TernopRetVar(Arc<String>, Arc<String>, Arc<String>, Box<Symbol>),
    /// Compute a unary function.
    ///
    /// This is used when the right side of the rule computes something from a left side expression.
    UnopRetVar(Arc<String>, Box<Symbol>),
    /// A function without domain constraints.
    NoConstrVar(Arc<String>),
    /// `\false` for one argument.
    False1,
    /// `not`.
    Not,
    /// `id` for booleans.
    Idb,
    /// `\true` for one argument.
    True1,
    /// `\false` for two arguments.
    False2,
    /// `\true` for two arguments.
    True2,
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
    /// `abs`.
    Abs,
    /// `lt`.
    Lt,
    /// `(< _)(_)`.
    Rlt,
    /// `le`.
    Le,
    /// `(<= _)(_)`.
    Rle,
    /// `gt`.
    Gt,
    /// `(> _)(_)`.
    Rgt,
    /// `ge`.
    Ge,
    /// `(>= _)(_)`.
    Rge,
    /// `neg`.
    Neg,
    /// `conj` (complex conjugate).
    Conj,
    /// `norm` (vector norm).
    Norm,
    /// `sqnorm` (vector square norm).
    Sqnorm,
    /// `add`.
    Add,
    /// `sub`.
    Sub,
    /// `mul`.
    Mul,
    /// `mulc` (complex multiplication).
    Mulc,
    /// `div`.
    Div,
    /// `rem`.
    Rem,
    /// `pow`.
    Pow,
    /// `rpow`.
    Rpow,
    /// `sqrt`.
    Sqrt,
    /// `ln`.
    Ln,
    /// `log2`.
    Log2,
    /// `log10`.
    Log10,
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
    /// `range` [a, b].
    Range,
    /// `rangel` [a, b).
    Rangel,
    /// `ranger` (a, b].
    Ranger,
    /// `rangem` (a, b).
    Rangem,
    /// `prob` [0, 1].
    Prob,
    /// `probl` [0, 1).
    Probl,
    /// `probr` (0, 1].
    Probr,
    /// `probm` (0, 1).
    Probm,
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
    /// `sin`.
    Sin,
    /// `asin`.
    Asin,
    /// `cos`.
    Cos,
    /// `acos`.
    Acos,
    /// `tan`.
    Tan,
    /// `atan`.
    Atan,
    /// `atan2`.
    Atan2,
    /// `dot`.
    Dot,
    /// `push`.
    Push,
    /// `push_front`.
    PushFront,
    /// `item` (index, list).
    Item,
    /// `el`.
    El,
    /// `re`.
    Re,
    /// `im`.
    Im,
    /// Generic `id`.
    Id,
    /// Generic `eq`.
    Eq,
    /// Generic `neq`.
    Neq,
    /// Derivative.
    D,
    /// `if`.
    ///
    /// This is used in Boolean functions.
    If,
    /// Existential path `∃`.
    Ex,
    /// Trivial path `∀`.
    Triv,
    /// `\`, the type of `\x`.
    RetType,
    /// The type of lists.
    VecType,
    /// The judgement `(: a)(b)`.
    Rty,
    /// Applies a binary function component-wise to lists.
    VecOp,
    /// Applies a unary function component-wise to lists.
    VecUop,
}

impl fmt::Display for Symbol {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> std::result::Result<(), fmt::Error> {
        use Symbol::*;

        match self {
            False1 => write!(w, "false1")?,
            Not => write!(w, "not")?,
            Idb => write!(w, "idb")?,
            True1 => write!(w, "true1")?,
            False2 => write!(w, "false2")?,
            True2 => write!(w, "true2")?,
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
            Abs => write!(w, "abs")?,
            Lt => write!(w, "lt")?,
            Rlt => write!(w, "rlt")?,
            Le => write!(w, "le")?,
            Rle => write!(w, "rle")?,
            Gt => write!(w, "gt")?,
            Rgt => write!(w, "rgt")?,
            Ge => write!(w, "ge")?,
            Rge => write!(w, "rge")?,
            Neg => write!(w, "neg")?,
            Conj => write!(w, "conj")?,
            Norm => write!(w, "norm")?,
            Sqnorm => write!(w, "sqnorm")?,
            Add => write!(w, "add")?,
            Sub => write!(w, "sub")?,
            Mul => write!(w, "mul")?,
            Mulc => write!(w, "mulc")?,
            Div => write!(w, "div")?,
            Rem => write!(w, "rem")?,
            Pow => write!(w, "pow")?,
            Rpow => write!(w, "rpow")?,
            Sqrt => write!(w, "sqrt")?,
            Ln => write!(w, "ln")?,
            Log2 => write!(w, "log2")?,
            Log10 => write!(w, "log10")?,
            Exp => write!(w, "exp")?,
            Len => write!(w, "len")?,
            Concat => write!(w, "concat")?,
            Sum => write!(w, "sum")?,
            Min2 => write!(w, "min2")?,
            Max2 => write!(w, "max2")?,
            Min => write!(w, "min")?,
            Max => write!(w, "max")?,
            Range => write!(w, "range")?,
            Rangel => write!(w, "rangel")?,
            Ranger => write!(w, "ranger")?,
            Rangem => write!(w, "rangem")?,
            Prob => write!(w, "prob")?,
            Probl => write!(w, "probl")?,
            Probr => write!(w, "probr")?,
            Probm => write!(w, "probm")?,
            MulMat => write!(w, "mul_mat")?,
            Det => write!(w, "det")?,
            Dim => write!(w, "dim")?,
            Fst => write!(w, "fst")?,
            Snd => write!(w, "snd")?,
            Sin => write!(w, "sin")?,
            Asin => write!(w, "asin")?,
            Cos => write!(w, "cos")?,
            Acos => write!(w, "acos")?,
            Tan => write!(w, "tan")?,
            Atan => write!(w, "atan")?,
            Atan2 => write!(w, "atan2")?,
            Dot => write!(w, "dot")?,
            Push => write!(w, "push")?,
            PushFront => write!(w, "push_front")?,
            Item => write!(w, "item")?,
            El => write!(w, "el")?,
            Re => write!(w, "re")?,
            Im => write!(w, "im")?,
            Id => write!(w, "id")?,
            Eq => write!(w, "eq")?,
            Neq => write!(w, "neq")?,
            If => write!(w, "if")?,
            Any => write!(w, "_")?,
            Ex => write!(w, "∃")?,
            Triv => write!(w, "∀")?,
            RetType => write!(w, "\\")?,
            VecType => write!(w, "vec")?,
            Rty => write!(w, "rty")?,
            VecOp => write!(w, "vec_op")?,
            VecUop => write!(w, "vec_uop")?,
            D => write!(w, "d")?,
            Var(x) | NoConstrVar(x) => write!(w, "{}", x)?,
            RetVar(x) => write!(w, "\\{}", x)?,
            NotRetVar(x) => write!(w, "!\\{}", x)?,
            ListVar(x) => write!(w, "[{}..]", x)?,
            Singleton(x) => write!(w, "[{}]", x)?,
            HeadTailTup(x, y) => write!(w, "({}, {}..)", x, y)?,
            HeadTailList(x, y) => write!(w, "[{}, {}..]", x, y)?,
            BinopRetVar(x, y, f) => {
                match **f {
                    Lt => write!(w, "{} < {}", x, y)?,
                    Le => write!(w, "{} <= {}", x, y)?,
                    Gt => write!(w, "{} > {}", x, y)?,
                    Ge => write!(w, "{} >= {}", x, y)?,
                    Add => write!(w, "{} + {}", x, y)?,
                    Sub => write!(w, "{} - {}", x, y)?,
                    Mul => write!(w, "{} * {}", x, y)?,
                    Div => write!(w, "{} / {}", x, y)?,
                    Pow => write!(w, "{} ^ {}", x, y)?,
                    Rem => write!(w, "{} % {}", x, y)?,
                    Eq => write!(w, "{} == {}", x, y)?,
                    Concat => write!(w, "{} ++ {}", x, y)?,
                    Push => write!(w, "compute::push({}, {})", x, y)?,
                    PushFront => write!(w, "compute::push_front({}, {})", x, y)?,
                    Max2 => write!(w, "compute::max2({}, {})", x, y)?,
                    Min2 => write!(w, "compute::min2({}, {})", x, y)?,
                    Item => write!(w, "{}[{}]", y, x)?,
                    _ => write!(w, "{:?}", self)?,
                }
            }
            TernopRetVar(x, y, z, f) => {
                match **f {
                    Range => write!(w, "compute::range({}, {}, {})", x, y, z)?,
                    Rangel => write!(w, "compute::rangel({}, {}, {})", x, y, z)?,
                    Ranger => write!(w, "compute::ranger({}, {}, {})", x, y, z)?,
                    Rangem => write!(w, "compute::rangem({}, {}, {})", x, y, z)?,
                    _ => write!(w, "{:?}", self)?,
                }
            }
            UnopRetVar(x, f) => {
                match **f {
                    Neg => write!(w, "-{}", x)?,
                    Len => write!(w, "compute::len({})", x)?,
                    Prob => write!(w, "compute::prob({})", x)?,
                    Probl => write!(w, "compute::probl({})", x)?,
                    Probr => write!(w, "compute::probr({})", x)?,
                    Probm => write!(w, "compute::probm({})", x)?,
                    _ => write!(w, "{:?}", self)?,
                }
            }
            // _ => write!(w, "{:?}", self)?,
        }
        Ok(())
    }
}
