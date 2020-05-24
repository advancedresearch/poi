use std::fmt;

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

impl fmt::Display for Expr {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> std::result::Result<(), fmt::Error> {
        match self {
            Sym(s) => write!(w, "{}", s)?,
            Ret(v) => write!(w, "\\{}", v)?,
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
                if let Sym(Rty) = **a {
                    if let Sym(_) = **b {
                        write!(w, "(: {})", b)?;
                    }
                } else if let Sym(Rlt) = **a {
                    write!(w, "(< {})", b)?;
                } else if let Sym(Rle) = **a {
                    write!(w, "(<= {})", b)?;
                } else if let Sym(Rgt) = **a {
                    write!(w, "(> {})", b)?;
                } else if let Sym(Rge) = **a {
                    write!(w, "(>= {})", b)?;
                } else if let Sym(Rpow) = **a {
                    write!(w, "(pow {})", b)?;
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
                    if let Op(Apply, f, a) = &**a {
                        match **f {
                            Sym(Add) => {
                                write!(w, "({} + {})", a, b)?;
                                return Ok(())
                            }
                            Sym(Sub) => {
                                write!(w, "({} - {})", a, b)?;
                                return Ok(())
                            }
                            Sym(Mul) => {
                                write!(w, "({} * {})", a, b)?;
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
                                write!(w, "({} ^ {})", a, b)?;
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
                            _ => {}
                        }
                    }
                    if let Op(Compose, _, _) = **a {
                        write!(w, "({})", a)?;
                    } else {
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
}
