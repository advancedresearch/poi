use super::*;

impl Symbol {
    /// Returns the arity of a symbol.
    pub fn arity(&self) -> Option<usize> {
        match self {
            VecType | RetType | Pi | Tau | Eps | BoolType | F64Type => Some(0),

            Not | Idb | Id | Neg | Arity |
            False1 | True1 | Even | Odd | Abs | Conj |
            Norm | Sqnorm | Sqrt | Ln | Log2 | Log10 | Exp | Len |
            Sum | Min | Max | Prob | Probl | Probr | Probm | Det |
            Dim | IsSquareMat | Sin | Asin | Cos | Acos | Tan | Atan |
            Re | Im | Ex | Triv | TypeOf => Some(1),

            Eq | Eqb | And | Or | Nand | Nor | Xor | Exc |
            Add | Mul | Div | Sub | Rem | False2 | True2 |
            Imply | Fstb | Sndb | Lt | Rlt | Le | Rle | Gt | Rgt |
            Ge | Rge | Mulc | Pow | Rpow | Concat | Min2 | Max2 |
            MulMat | Base | Fst | Snd | Atan2 | Dot | Push | PushFront |
            Item | Neq | D | Rty | VecUop => Some(2),

            Range | Rangel | Ranger | Rangem | El | If | VecOp => Some(3),

            Any | Var(_) | ArityVar(_, _) | ListVar(_) |
            Singleton(_) | HeadTailTup(_, _) | HeadTailList(_, _) |
            RetVar(_) | RetIntVar(_) | NotRetVar(_) | BinopRetVar(_, _, _) |
            TernopRetVar(_, _, _, _) | UnopRetVar(_, _) | NoConstrVar(_) => None,

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
