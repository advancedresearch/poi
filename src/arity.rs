use super::*;

impl Symbol {
    /// Returns the arity of a symbol.
    pub fn arity(&self) -> Option<usize> {
        match self {
            VecType | Not | Idb | Id | Neg => Some(1),
            Eq | Eqb | And | Or | Nand | Nor | Xor | Exc => Some(2),
            _ => None
        }
    }
}
