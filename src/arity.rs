use super::*;

impl Symbol {
    /// Returns the arity of a symbol.
    pub fn arity(&self) -> Option<usize> {
        match self {
            VecType | AnyType | RetType | Pi | Tau | Eps | Imag | Imag2 | Imag3 |
            BoolType | F64Type | QuatType | Inf => Some(0),

            Not | Idb | Id | Inv | Neg | Inc | Reci | Arity |
            False1 | True1 | Even | Odd | Abs | Conj |
            Norm | Sqnorm | Sqrt | Ln | Log2 | Log10 | Exp | Len |
            Sum | Min | Max | ArgMax | ArgMin | SoftMax | SoftMin | Prob | Probl | Probr | Probm |
            Det | Transpose | Dim | IsSquareMat | Sin | Asin | Cos | Acos | Tan | Atan |
            Re | Im | Ex | Triv | TypeOf | Pariv => Some(1),

            Eq | Eqb | And | Or | Nand | Nor | Xor | Exc |
            Add | Mul | Div | Rdiv | Sub | Rsub | Rem | False2 | True2 |
            Imply | Fstb | Sndb | Lt | Rlt | Le | Rle | Gt | Rgt |
            Ge | Rge | Mulc | Pow | Rpow | Concat | Min2 | Max2 |
            MulMat | Base | Fst | Snd | Atan2 | Dot | Push | PushFront |
            Item | Col | Neq | Deriv | Rty | VecUop | SoftArgMax | SoftArgMin => Some(2),

            Range | Rangel | Ranger | Rangem | El | If | VecOp | Integ => Some(3),

            Any | Var(_) | ArityVar(_, _) | ListVar(_) |
            Singleton(_) | HeadTailTup(_, _) | HeadTailList(_, _) |
            RetVar(_) | RetIntVar(_) | RetPosVar(_) | RetStrictPosVar(_) | RetNegVar(_) |
            NotRetVar(_) | NotInVarName(_, _) |
            BinopRetVar(_, _, _) | TernopRetVar(_, _, _, _) | UnopRetVar(_, _) |
            NoConstrVar(_) => None,

            Custom(_) => None,

            // _ => None
        }
    }
}

impl Expr {
    /// Returns the arity of an expression.
    ///
    /// Unfinished: This function requires analysis and unit testing.
    pub fn arity(&self) -> Option<usize> {
        match self {
            Sym(s) => s.arity(),
            Op(Apply, x, y) => {
                match (&**x, &**y) {
                    (Sym(Rty), Sym(VecType)) => Some(1),
                    (Sym(s), Ret(_)) => {
                        if let Some(arity) = s.arity() {
                            if arity >= 1 {Some(arity - 1)}
                            else {Some(0)}
                        } else {
                            None
                        }
                    }
                    _ => None
                }
            }
            _ => None,
        }
    }
}
