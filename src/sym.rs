use std::sync::Arc;
use std::fmt;
use super::Expr;

/// Contains symbols and operators on symbols.
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum Symbol {
    /// A custom symbol.
    Custom(Arc<String>),
    /// The wildcard symbol `_`.
    Any,
    /// A variable bound from context.
    ///
    /// This can be anything.
    Var(Arc<String>),
    /// A function variable with specified arity (number of arguments).
    ArityVar(Arc<String>, usize),
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
    /// A value variable that is an integer.
    RetIntVar(Arc<String>),
    /// A value variable that is positive or zero.
    RetPosVar(Arc<String>),
    /// A value that is strictly positive (non-zero).
    RetStrictPosVar(Arc<String>),
    /// A value variable that is negative and non-zero.
    ///
    /// Binds to its positive value.
    RetNegVar(Arc<String>),
    /// A variable that is not a value variable.
    NotRetVar(Arc<String>),
    /// Binds to left variable name that does not occur in expression
    /// bound to the right variable.
    NotInVarName(Arc<String>, Arc<String>),
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
    /// `inc`.
    Inc,
    /// `reci` (reciprocal).
    Reci,
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
    /// `(- _)(_)`
    Rsub,
    /// `mul`.
    Mul,
    /// `mulc` (complex multiplication).
    Mulc,
    /// `div`.
    Div,
    /// `(/ _)(_)`
    Rdiv,
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
    /// `arg_max`.
    ArgMax,
    /// `arg_min`.
    ArgMin,
    /// `soft_max`.
    SoftMax,
    /// `soft_min`.
    SoftMin,
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
    /// `col` (index, matrix).
    ///
    /// Looks up column vector by index in a matrix.
    Col,
    /// `det`.
    Det,
    /// `dim`.
    Dim,
    /// `transpose`.
    Transpose,
    /// `is_square_mat`,
    IsSquareMat,
    /// `base` (len, index).
    ///
    /// Constructs a list with zeroes of specified length,
    /// but with `1` at the index.
    Base,
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
    /// Function inverse `inv`.
    Inv,
    /// Derivative.
    Deriv,
    /// Integral.
    Integ,
    /// Partial derivative.
    Pariv,
    /// `if`.
    ///
    /// This is used in Boolean functions.
    If,
    /// Existential path `∃`.
    Ex,
    /// Trivial path `∀`.
    Triv,
    /// `any`, any type.
    AnyType,
    /// `\`, the type of `\x`.
    RetType,
    /// The type of lists.
    VecType,
    /// The judgement `(: a)(b)`.
    Rty,
    /// `vec_op`.
    ///
    /// Applies a binary function component-wise to lists.
    VecOp,
    /// `vec_uop`.
    ///
    /// Applies a unary function component-wise to lists.
    VecUop,
    /// `arity`.
    Arity,
    /// `pi` or `π`.
    Pi,
    /// `tau` or `τ`.
    Tau,
    /// `eps` or `ε`.
    Eps,
    /// `imag` (complex imaginary base).
    Imag,
    /// `imag2` (second complex imaginary base for quaternions).
    Imag2,
    /// `imag3` (third complex imaginary base for quaternions).
    Imag3,
    /// `type_of`.
    TypeOf,
    /// `bool`.
    BoolType,
    /// `f64`.
    F64Type,
    /// `quat` (type of quaternions).
    QuatType,
    /// `inf` (infinity).
    Inf,
}

impl Symbol {
    /// Returns the operator presedence of symbol.
    pub fn precedence(&self) -> Option<u8> {
        use Symbol::*;

        Some(match self {
            Pow => 3,
            Mul | Div | Rem | And => 4,
            Add | Sub | Or => 5,
            Eq => 6,
            _ => return None,
        })
    }
}

impl From<Arc<String>> for Symbol {
    fn from(val: Arc<String>) -> Symbol {
        use Symbol::*;

        match &**val {
            "_" => Any,
            "triv" | "∀" | "dom" => Triv,
            "ex" | "∃" | "codom" => Ex,
            "false1" => False1,
            "idb" => Idb,
            "not" => Not,
            "true1" => True1,
            "false2" => False2,
            "true2" => True2,
            "and" => And,
            "or" => Or,
            "eqb" => Eqb,
            "xor" => Xor,
            "nand" => Nand,
            "nor" => Nor,
            "exc" => Exc,
            "imply" => Imply,
            "fstb" => Fstb,
            "sndb" => Sndb,
            "neqb" => Xor,
            "id" => Id,
            "inv" => Inv,
            "lt" => Lt,
            "rlt" => Rlt,
            "le" => Le,
            "rle" => Rle,
            "gt" => Gt,
            "rgt" => Rgt,
            "ge" => Ge,
            "rge" => Rge,
            "mul" => Mul,
            "mulc" => Mulc,
            "div" => Div,
            "rem" => Rem,
            "pow" => Pow,
            "rpow" => Rpow,
            "sqrt" => Sqrt,
            "even" => Even,
            "odd" => Odd,
            "abs" => Abs,
            "neg" => Neg,
            "inc" => Inc,
            "reci" => Reci,
            "conj" => Conj,
            "norm" => Norm,
            "sqnorm" => Sqnorm,
            "add" => Add,
            "sub" => Sub,
            "len" => Len,
            "concat" => Concat,
            "sum" => Sum,
            "mul_mat" => MulMat,
            "col" => Col,
            "det" => Det,
            "dim" => Dim,
            "transpose" => Transpose,
            "is_square_mat" => IsSquareMat,
            "base" => Base,
            "fst" => Fst,
            "snd" => Snd,
            "ln" => Ln,
            "log2" => Log2,
            "log10" => Log10,
            "exp" => Exp,
            "min2" => Min2,
            "max2" => Max2,
            "min" => Min,
            "max" => Max,
            "arg_max" => ArgMax,
            "arg_min" => ArgMin,
            "soft_max" => SoftMax,
            "soft_min" => SoftMin,
            "range" => Range,
            "rangel" => Rangel,
            "ranger" => Ranger,
            "rangem" => Rangem,
            "prob" => Prob,
            "probl" => Probl,
            "probr" => Probr,
            "probm" => Probm,
            "eq" => Eq,
            "neq" => Neq,
            "if" => If,
            "sin" => Sin,
            "asin" => Asin,
            "cos" => Cos,
            "acos" => Acos,
            "tan" => Tan,
            "atan" => Atan,
            "atan2" => Atan2,
            "dot" => Dot,
            "item" => Item,
            "el" => El,
            "re" => Re,
            "im" => Im,
            "push" => Push,
            "push_front" => PushFront,
            "any" => AnyType,
            "\\" => RetType,
            "vec" => VecType,
            "rty" => Rty,
            "vec_op" => VecOp,
            "vec_uop" => VecUop,
            "arity" => Arity,
            "deriv" | "𝐝" => Deriv,
            "integ" | "∫" => Integ,
            "pariv" | "∂" => Pariv,
            "pi" | "π" => Pi,
            "tau" | "τ" => Tau,
            "eps" | "ε" => Eps,
            "imag" | "𝐢" => Imag,
            "imag2" | "𝐢₂" => Imag2,
            "imag3" | "𝐢₃" => Imag3,
            "type_of" => TypeOf,
            "bool" => BoolType,
            "f64" => F64Type,
            "quat" => QuatType,
            "inf" | "∞" => Inf,
            _ => {
                // Custom symbols start with two lowercase alphabetic letters.
                let custom_symbol = {
                    let mut chars = val.chars();
                    if let Some(ch) = chars.next() {
                        ch.is_lowercase() && ch.is_alphabetic() &&
                        if let Some(ch) = chars.next() {
                            ch.is_lowercase() && ch.is_alphabetic()
                        } else {false}
                    } else {false}
                };
                if custom_symbol {
                    Custom(val)
                } else {
                    Var(val)
                }
            }
        }
    }
}

impl Symbol {
    /// Used to display format with additional options.
    pub fn display(
        &self,
        w: &mut fmt::Formatter<'_>,
        rule: bool,
    ) -> std::result::Result<(), fmt::Error> {
        use Symbol::*;

        match self {
            Custom(sym) => write!(w, "{}", sym)?,
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
            Inc => write!(w, "inc")?,
            Reci => write!(w, "reci")?,
            Conj => write!(w, "conj")?,
            Norm => write!(w, "norm")?,
            Sqnorm => write!(w, "sqnorm")?,
            Add => write!(w, "add")?,
            Sub => write!(w, "sub")?,
            Rsub => write!(w, "rsub")?,
            Mul => write!(w, "mul")?,
            Mulc => write!(w, "mulc")?,
            Div => write!(w, "div")?,
            Rdiv => write!(w, "rdiv")?,
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
            ArgMax => write!(w, "arg_max")?,
            ArgMin => write!(w, "arg_min")?,
            SoftMax => write!(w, "soft_max")?,
            SoftMin => write!(w, "soft_min")?,
            Range => write!(w, "range")?,
            Rangel => write!(w, "rangel")?,
            Ranger => write!(w, "ranger")?,
            Rangem => write!(w, "rangem")?,
            Prob => write!(w, "prob")?,
            Probl => write!(w, "probl")?,
            Probr => write!(w, "probr")?,
            Probm => write!(w, "probm")?,
            MulMat => write!(w, "mul_mat")?,
            Col => write!(w, "col")?,
            Det => write!(w, "det")?,
            Dim => write!(w, "dim")?,
            Transpose => write!(w, "transpose")?,
            IsSquareMat => write!(w, "is_square_mat")?,
            Base => write!(w, "base")?,
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
            Inv => write!(w, "inv")?,
            If => write!(w, "if")?,
            Any => write!(w, "_")?,
            Ex => write!(w, "∃")?,
            Triv => write!(w, "∀")?,
            AnyType => write!(w, "any")?,
            RetType => write!(w, "\\")?,
            VecType => write!(w, "vec")?,
            Rty => write!(w, "rty")?,
            VecOp => write!(w, "vec_op")?,
            VecUop => write!(w, "vec_uop")?,
            Arity => write!(w, "arity")?,
            Deriv => write!(w, "𝐝")?,
            Integ => write!(w, "∫")?,
            Pariv => write!(w, "∂")?,
            Pi => write!(w, "π")?,
            Tau => write!(w, "τ")?,
            Eps => write!(w, "ε")?,
            Imag => write!(w, "𝐢")?,
            Imag2 => write!(w, "𝐢₂")?,
            Imag3 => write!(w, "𝐢₃")?,
            TypeOf => write!(w, "type_of")?,
            BoolType => write!(w, "bool")?,
            F64Type => write!(w, "f64")?,
            QuatType => write!(w, "quat")?,
            Inf => write!(w, "∞")?,
            Var(x) => write!(w, "{}", x)?,
            NoConstrVar(x) => if rule {
                write!(w, "{}!{{}}", x)?
            } else {
                write!(w, "{}", x)?
            },
            ArityVar(x, arg) => if rule {
                write!(w, "{}:[arity]{}", x, arg)?
            } else {
                write!(w, "{}", x)?
            },
            RetVar(x) => write!(w, "\\{}", x)?,
            RetIntVar(x) => write!(w, "\\{}:int", x)?,
            RetPosVar(x) => write!(w, "\\{}:(>= 0)", x)?,
            RetStrictPosVar(x) => write!(w, "\\{}:(> 0)", x)?,
            RetNegVar(x) => write!(w, "\\{}:(< 0)", x)?,
            NotRetVar(x) => write!(w, "!\\{}", x)?,
            NotInVarName(x, y) => write!(w, "{}!>{}", x, y)?,
            ListVar(x) => write!(w, "[{}..]", x)?,
            Singleton(x) => write!(w, "\\[{}]", x)?,
            HeadTailTup(x, y) => write!(w, "({}, {}..)", x, y)?,
            HeadTailList(x, y) => write!(w, "[{}, {}..]", x, y)?,
            BinopRetVar(x, y, f) => {
                match **f {
                    Lt => write!(w, "compute::lt({}, {})", x, y)?,
                    Le => write!(w, "compute::le({}, {})", x, y)?,
                    Gt => write!(w, "compute::gt({}, {})", x, y)?,
                    Ge => write!(w, "compute::ge({}, {})", x, y)?,
                    Add => write!(w, "compute::add({}, {})", x, y)?,
                    Sub => write!(w, "compute::sub({}, {})", x, y)?,
                    Mul => write!(w, "compute::mul({}, {})", x, y)?,
                    Div => write!(w, "compute::div({}, {})", x, y)?,
                    Pow => write!(w, "compute::pow({}, {})", x, y)?,
                    Rem => write!(w, "compute::rem({}, {})", x, y)?,
                    Eq => write!(w, "compute::eq({}, {})", x, y)?,
                    Concat => write!(w, "compute::concat({}, {})", x, y)?,
                    MulMat => write!(w, "compute::mul_mat({}, {})", x, y)?,
                    Push => write!(w, "compute::push({}, {})", x, y)?,
                    PushFront => write!(w, "compute::push_front({}, {})", x, y)?,
                    Max2 => write!(w, "compute::max2({}, {})", x, y)?,
                    Min2 => write!(w, "compute::min2({}, {})", x, y)?,
                    Item => write!(w, "compute::item({}, {})", x, y)?,
                    Col => write!(w, "compute::col({}, {})", x, y)?,
                    Base => write!(w, "compute::base({}, {})", x, y)?,
                    Atan2 => write!(w, "compute::atan2({}, {})", x, y)?,
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
                    Even => write!(w, "compute::even({})", x)?,
                    Odd => write!(w, "compute::odd({})", x)?,
                    Neg => write!(w, "compute::neg({})", x)?,
                    Inc => write!(w, "compute::inc({})", x)?,
                    Reci => write!(w, "compute::reci({})", x)?,
                    Abs => write!(w, "compute::abs({})", x)?,
                    Len => write!(w, "compute::len({})", x)?,
                    Prob => write!(w, "compute::prob({})", x)?,
                    Probl => write!(w, "compute::probl({})", x)?,
                    Probr => write!(w, "compute::probr({})", x)?,
                    Probm => write!(w, "compute::probm({})", x)?,
                    Sqrt => write!(w, "compute::sqrt({})", x)?,
                    Ln => write!(w, "compute::ln({})", x)?,
                    Log2 => write!(w, "compute::log2({})", x)?,
                    Log10 => write!(w, "compute::log10({})", x)?,
                    Exp => write!(w, "compute::exp({})", x)?,
                    Sin => write!(w, "compute::sin({})", x)?,
                    Asin => write!(w, "compute::asin({})", x)?,
                    Cos => write!(w, "compute::cos({})", x)?,
                    Acos => write!(w, "compute::acos({})", x)?,
                    Tan => write!(w, "compute::tan({})", x)?,
                    Atan => write!(w, "compute::atan({})", x)?,
                    Dim => write!(w, "compute::dim({})", x)?,
                    IsSquareMat => write!(w, "compute::is_square_mat({})", x)?,
                    Transpose => write!(w, "compute::transpose({})", x)?,
                    Arity => write!(w, "compute::arity({})", x)?,
                    TypeOf => write!(w, "compute::type_of({})", x)?,
                    _ => write!(w, "{:?}", self)?,
                }
            }
            // _ => write!(w, "{:?}", self)?,
        }
        Ok(())
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> std::result::Result<(), fmt::Error> {
        let rule = false;
        self.display(w, rule)
    }
}
