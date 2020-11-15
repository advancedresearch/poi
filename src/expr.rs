use std::fmt;
use std::ops::{Add, Sub, Mul};

use super::*;

/// Function expression.
#[derive(Clone, PartialEq, Debug)]
pub enum Expr {
    /// A symbol that is used together with symbolic knowledge.
    Sym(Symbol),
    /// Some function that returns a value, ignoring the argument.
    ///
    /// This can also be used to store values, since zero arguments is a value.
    Ret(Value),
    /// A binary operation on functions.
    Op(Op, Box<Expr>, Box<Expr>),
    /// A tuple for more than one argument.
    Tup(Vec<Expr>),
    /// A list.
    List(Vec<Expr>),
}

impl Add for Expr {
    type Output = Expr;
    fn add(self, other: Expr) -> Expr {app2(Add, self, other)}
}

impl Sub for Expr {
    type Output = Expr;
    fn sub(self, other: Expr) -> Expr {app2(Sub, self, other)}
}

impl Mul for Expr {
    type Output = Expr;
    fn mul(self, other: Expr) -> Expr {app2(Mul, self, other)}
}

impl Expr {
    /// Used to display format with additional options.
    pub fn display(
        &self,
        w: &mut fmt::Formatter<'_>,
        parens: bool,
    ) -> std::result::Result<(), fmt::Error> {
        match self {
            Sym(s) => write!(w, "{}", s)?,
            Ret(v) => write!(w, "{}", v)?,
            Op(Path, a, b) => {
                if let Sym(b) = &**b {
                    if let Op(Compose, _, _) = **a {
                        write!(w, "({})[{}]", a, b)?;
                    } else {
                        write!(w, "{}[{}]", a, b)?;
                    }
                } else if let Tup(b) = &**b {
                    if let Op(Compose, _, _) = **a {
                        write!(w, "({})[", a)?;
                    } else {
                        write!(w, "{}[", a)?;
                    }
                    for i in 0..b.len() {
                        if i > 0 {
                            if i + 1 < b.len() {
                                write!(w, " ⨯ ")?
                            } else {
                                write!(w, " → ")?
                            }
                        }
                        if let Op(Compose, _, _) = b[i] {
                            write!(w, "(")?;
                        }
                        write!(w, "{}", &b[i])?;
                        if let Op(Compose, _, _) = b[i] {
                            write!(w, ")")?;
                        }
                    }
                    write!(w, "]")?
                } else {
                    write!(w, "{}[{}]", a, b)?
                }
            }
            Op(Apply, a, b) => {
                if let Sym(Neg) = **a {
                    write!(w, "-{}", b)?;
                } else if let Sym(Not) = **a {
                    write!(w, "!{}", b)?;
                } else if let Sym(Rty) = **a {
                    if let Sym(_) = **b {
                        write!(w, "(: {})", b)?;
                    }
                } else if let Sym(Rlt) = **a {
                    write!(w, "(< {})", b)?;
                } else if let Sym(Rle) = **a {
                    write!(w, "(<= {})", b)?;
                } else if let Sym(Eq) = **a {
                    write!(w, "(= {})", b)?;
                } else if let Sym(Rgt) = **a {
                    write!(w, "(> {})", b)?;
                } else if let Sym(Rge) = **a {
                    write!(w, "(>= {})", b)?;
                } else if let Sym(Mul) = **a {
                    write!(w, "(* {})", b)?;
                } else if let Sym(Add) = **a {
                    write!(w, "(+ {})", b)?;
                } else if let Sym(Rsub) = **a {
                    write!(w, "(- {})", b)?;
                } else if let Sym(Rdiv) = **a {
                    write!(w, "(/ {})", b)?;
                } else if let Sym(Rpow) = **a {
                    write!(w, "(^ {})", b)?;
                } else {
                    if let (Op(Apply, f, a), Sym(Pi)) = (&**a, &**b) {
                        if let (Sym(Mul), Ret(F64(a))) = (&**f, &**a) {
                            write!(w, "{}π", a)?;
                            return Ok(())
                        }
                    }
                    if let (Op(Apply, f, a), Sym(Tau)) = (&**a, &**b) {
                        if let (Sym(Mul), Ret(F64(a))) = (&**f, &**a) {
                            write!(w, "{}τ", a)?;
                            return Ok(())
                        }
                    }
                    if let (Op(Apply, f, a), Sym(Eps)) = (&**a, &**b) {
                        if let (Sym(Mul), Ret(F64(a))) = (&**f, &**a) {
                            write!(w, "{}ε", a)?;
                            return Ok(())
                        }
                    }
                    if let (Op(Apply, f, a), Sym(Imag)) = (&**a, &**b) {
                        if let (Sym(Mul), Ret(F64(a))) = (&**f, &**a) {
                            write!(w, "{}𝐢", a)?;
                            return Ok(())
                        }
                    }
                    if let (Op(Apply, f, a), Sym(Imag2)) = (&**a, &**b) {
                        if let (Sym(Mul), Ret(F64(a))) = (&**f, &**a) {
                            write!(w, "{}𝐢₂", a)?;
                            return Ok(())
                        }
                    }
                    if let (Op(Apply, f, a), Sym(Imag3)) = (&**a, &**b) {
                        if let (Sym(Mul), Ret(F64(a))) = (&**f, &**a) {
                            write!(w, "{}𝐢₃", a)?;
                            return Ok(())
                        }
                    }
                    if let Op(Apply, f, a) = &**a {
                        let mut pr = |
                            op_txt: &str,
                            op_sym: &Symbol
                        | -> std::result::Result<(), fmt::Error> {
                            if parens {write!(w, "(")?};
                            let left = true;
                            a.display(w, a.needs_parens(op_sym, left))?;
                            write!(w, " {} ", op_txt)?;
                            let right = false;
                            b.display(w, b.needs_parens(op_sym, right))?;
                            if parens {write!(w, ")")?};
                            Ok(())
                        };

                        match **f {
                            Sym(Add) => {
                                if parens {
                                    write!(w, "({} + {})", a, b)?;
                                } else {
                                    write!(w, "{} + {}", a, b)?;
                                }
                                return Ok(())
                            }
                            Sym(Sub) => {
                                write!(w, "({} - {})", a, b)?;
                                return Ok(())
                            }
                            Sym(Mul) => {
                                pr("*", &Mul)?;
                                return Ok(())
                            }
                            Sym(Div) => {
                                write!(w, "({} / {})", a, b)?;
                                return Ok(())
                            }
                            Sym(Rem) => {
                                write!(w, "({} % {})", a, b)?;
                                return Ok(())
                            }
                            Sym(Pow) => {
                                write!(w, "({} ^ ", a)?;
                                let parens = true;
                                b.display(w, parens)?;
                                write!(w, ")")?;
                                return Ok(())
                            }
                            Sym(And) => {
                                write!(w, "({} & {})", a, b)?;
                                return Ok(())
                            }
                            Sym(Or) => {
                                write!(w, "({} | {})", a, b)?;
                                return Ok(())
                            }
                            Sym(Concat) => {
                                write!(w, "({} ++ {})", a, b)?;
                                return Ok(())
                            }
                            Sym(Lt) => {
                                write!(w, "({} < {})", a, b)?;
                                return Ok(())
                            }
                            Sym(Le) => {
                                write!(w, "({} <= {})", a, b)?;
                                return Ok(())
                            }
                            Sym(Eq) => {
                                write!(w, "({} = {})", a, b)?;
                                return Ok(())
                            }
                            Sym(Gt) => {
                                write!(w, "({} > {})", a, b)?;
                                return Ok(())
                            }
                            Sym(Ge) => {
                                write!(w, "({} >= {})", a, b)?;
                                return Ok(())
                            }
                            _ => {}
                        }
                    }
                    if let Op(Compose, _, _) = **a {
                        write!(w, "({})", a)?;
                    } else {
                        if let Ret(_) = **a {
                            write!(w, "\\")?;
                        }
                        write!(w, "{}", a)?;
                    }
                    if let Tup(b) = &**b {
                        write!(w, "(")?;
                        for i in 0..b.len() {
                            if i > 0 {write!(w, ", ")?}
                            write!(w, "{}", &b[i])?;
                        }
                        write!(w, ")")?;
                    } else {
                        write!(w, "({})", b)?;
                    }
                }
            }
            Op(Constrain, a, b) => {
                if let Op(Compose, _, _) = **a {
                    write!(w, "({})", a)?;
                } else {
                    if let Ret(_) = **a {
                        write!(w, "\\")?;
                    }
                    write!(w, "{}", a)?;
                }
                if let Tup(b) = &**b {
                    write!(w, "{{")?;
                    for i in 0..b.len() {
                        if i > 0 {write!(w, ", ")?}
                        write!(w, "{}", &b[i])?;
                    }
                    write!(w, "}}")?;
                } else {
                    write!(w, "{{{}}}", b)?;
                }
            }
            Op(Compose, a, b) => {
                if let Op(Compose, _, _) = **a {
                    write!(w, "({})", a)?;
                } else {
                    write!(w, "{}", a)?;
                }
                write!(w, " · ")?;
                if let Op(Compose, _, _) = **b {
                    write!(w, "({})", b)?;
                } else {
                    write!(w, "{}", b)?;
                }
            }
            Op(Type, a, b) => {
                if let Op(Type, _, _) = **a {
                    write!(w, "({}) : {}", a, b)?
                } else if let Op(Type, _, _) = **b {
                    write!(w, "{} : ({})", a, b)?
                } else {
                    write!(w, "{} : {}", a, b)?
                }
            }
            Tup(b) => {
                write!(w, "(")?;
                for i in 0..b.len() {
                    if i > 0 {write!(w, ", ")?}
                    write!(w, "{}", &b[i])?;
                }
                write!(w, ")")?;
            }
            List(b) => {
                write!(w, "[")?;
                for i in 0..b.len() {
                    if i > 0 {write!(w, ", ")?}
                    write!(w, "{}", &b[i])?;
                }
                write!(w, "]")?;
            }
            // _ => write!(w, "{:?}", self)?,
        }
        Ok(())
    }

    /// Returns `true` if the expression needs parentheses, given parent operation and side.
    pub fn needs_parens(&self, parent_op: &Symbol, left: bool) -> bool {
        if left {
            if let Op(Apply, f, _) = self {
                if let Op(Apply, f, _) = &**f {
                    match &**f {
                        Sym(Mul) => if let Mul = parent_op {false} else {true},
                        _ => true
                    }
                } else {
                    true
                }
            } else {
                true
            }
        } else {
            true
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> std::result::Result<(), fmt::Error> {
        let parens = false;
        self.display(w, parens)
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn parens() {
        let expr = app2(Mul, app2(Mul, "a", "b"), "c");
        assert_eq!(format!("{}", expr), "a * b * c");
        let expr = app2(Mul, "a", app2(Mul, "b", "c"));
        assert_eq!(format!("{}", expr), "a * (b * c)");
        let expr = app2(Add, "a", "b");
        assert_eq!(format!("{}", expr), "a + b");
        let expr = app2(Mul, app2(Add, "a", "b"), "c");
        assert_eq!(format!("{}", expr), "(a + b) * c");
    }
}
