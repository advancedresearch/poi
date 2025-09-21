#![deny(missing_docs)]
#![doc = include_str!("../README.md")]

use std::sync::Arc;

use self::Expr::*;
use self::Op::*;
use self::Value::*;
use self::Knowledge::*;
use self::Symbol::*;

pub use val::*;
pub use expr::*;
pub use op::Op;
pub use sym::*;
pub use standard_library::*;
pub use parsing::*;
pub use knowledge::*;

mod val;
mod expr;
mod op;
mod sym;
mod knowledge;
mod standard_library;
mod parsing;
mod arity;
mod matrix;

/// Used to global import enum variants.
pub mod prelude {
    pub use super::*;
    pub use super::Expr::*;
    pub use super::Op::*;
    pub use super::Value::*;
    pub use super::Knowledge::*;
    pub use super::Symbol::*;
}

impl Into<Expr> for bool {
    fn into(self) -> Expr {Ret(Bool(self))}
}

impl Into<Expr> for f64 {
    fn into(self) -> Expr {Ret(F64(self))}
}

impl<T, U> Into<Expr> for (T, U)
    where T: Into<Expr>, U: Into<Expr>
{
    fn into(self) -> Expr {Tup(vec![self.0.into(), self.1.into()])}
}

impl<T0, T1, T2> Into<Expr> for (T0, T1, T2)
    where T0: Into<Expr>, T1: Into<Expr>, T2: Into<Expr>
{
    fn into(self) -> Expr {Tup(vec![self.0.into(), self.1.into(), self.2.into()])}
}

impl Expr {
    /// Returns available equivalences of the expression, using a knowledge base.
    pub fn equivalences(&self, knowledge: &[Knowledge]) -> Vec<(Expr, usize)> {
        let mut ctx = Context {vars: vec![]};
        let mut res = vec![];
        for i in 0..knowledge.len() {
            if let Eqv(a, b) | EqvEval(a, b) = &knowledge[i] {
                if ctx.bind(a, self) {
                    let expr = match ctx.substitute(b) {
                        Ok(expr) => expr,
                        Err(_) => {
                            // Silence errors since the equivalence might not be relevant.
                            // This should probably be handled better.
                            ctx.vars.clear();
                            continue;
                        }
                    };
                    res.push((expr, i));
                    ctx.vars.clear();
                } else if ctx.bind(b, self) {
                    let expr = match ctx.substitute(a) {
                        Ok(expr) => expr,
                        Err(_) => {
                            // Silence errors since not all variables can be bound.
                            // This should probably be handled better.
                            ctx.vars.clear();
                            continue;
                        }
                    };
                    res.push((expr, i));
                    ctx.vars.clear();
                }
            }
        }

        match self {
            Sym(_) | Ret(_) => {}
            EOp(op, a, b) => {
                for (ea, i) in a.equivalences(knowledge).into_iter() {
                    res.push((EOp(*op, Box::new(ea), b.clone()), i));
                }
                for (eb, i) in b.equivalences(knowledge).into_iter() {
                    res.push((EOp(*op, a.clone(), Box::new(eb)), i));
                }
            }
            Tup(items) | List(items) => {
                for i in 0..items.len() {
                    for (expr, j) in items[i].equivalences(knowledge).into_iter() {
                        let mut new_items: Vec<Expr> = items[0..i].into();
                        new_items.push(expr);
                        new_items.extend(items[i+1..].iter().map(|n| n.clone()));
                        if let Tup(_) = self {
                            res.push((Tup(new_items), j));
                        } else if let List(_) = self {
                            res.push((List(new_items), j));
                        }
                    }
                }
            }
        }

        res
    }

    /// Returns `true` if expressions contains NaN (not a number).
    pub fn contains_nan(&self) -> bool {
        match self {
            Sym(_) => false,
            Ret(F64(v)) => v.is_nan(),
            Ret(_) => false,
            EOp(_, a, b) => a.contains_nan() || b.contains_nan(),
            Tup(items) | List(items) => items.iter().any(|n| n.contains_nan()),
        }
    }

    /// Evaluate an expression using a knowledge base.
    ///
    /// This combines reductions and inlining of all symbols.
    pub fn eval(&self, knowledge: &[Knowledge]) -> Result<Expr, Error> {
        let mut me = self.clone();
        while !me.contains_nan() {
            let expr = me.reduce_eval_all(knowledge, true).inline_all(knowledge)?;
            if expr == me {break};
            me = expr;
        }
        Ok(me)
    }

    /// Reduces an expression using a knowledge base, until it can not be reduces further.
    pub fn reduce_all(&self, knowledge: &[Knowledge]) -> Expr {
        self.reduce_eval_all(knowledge, false)
    }

    /// Reduces an expression using a knowledge base, until it can not be reduces further.
    pub fn reduce_eval_all(&self, knowledge: &[Knowledge], eval: bool) -> Expr {
        let mut me = self.clone();
        while let Ok((expr, _)) = me.reduce_eval(knowledge, eval) {me = expr}
        me
    }

    /// Reduces expression one step using a knowledge base.
    pub fn reduce(&self, knowledge: &[Knowledge]) -> Result<(Expr, usize), Error> {
        self.reduce_eval(knowledge, false)
    }

    /// Reduces expression one step using a knowledge base.
    ///
    /// When `eval` is set to `true`, the `EqvEval` variants are reduced.
    pub fn reduce_eval(&self, knowledge: &[Knowledge], eval: bool) -> Result<(Expr, usize), Error> {
        let mut ctx = Context {vars: vec![]};
        let mut me: Result<(Expr, usize), Error> = Err(Error::NoReductionRule);
        for i in 0..knowledge.len() {
            if eval {
                if let Red(a, b) | EqvEval(a, b) = &knowledge[i] {
                    if ctx.bind(a, self) {
                        me = match ctx.substitute(b) {
                            Ok(expr) => Ok((expr, i)),
                            Err(err) => Err(err),
                        };
                        break;
                    }
                }
            } else {
                if let Red(a, b) = &knowledge[i] {
                    if ctx.bind(a, self) {
                        me = match ctx.substitute(b) {
                            Ok(expr) => Ok((expr, i)),
                            Err(err) => Err(err),
                        };
                        break;
                    }
                }
            }
        }

        match self {
            EOp(op, a, b) => {
                // Do not reduce sub-expressions containing type judgements in the parent,
                // to avoid infinite expansion in rules introducing type judgements.
                //
                // Type judgements might still be used in pattern matching and binding of variables.
                //
                // For example, `a : T => ...` is still valid.
                if let Type = op {
                    // Make an exception for lists, in order to evaluate items of the list.
                    if let List(_) = **a {} else {return me}
                }

                if let Ok((a, i)) = a.reduce_eval(knowledge, eval) {
                    // Prefer the reduction that matches the first rule.
                    if let Ok((expr, j)) = me {if j < i {return Ok((expr, j))}};
                    return Ok((EOp(*op, Box::new(a), b.clone()), i));
                }
                if let Ok((b, i)) = b.reduce_eval(knowledge, eval) {
                    // Prefer the reduction that matches the first rule.
                    if let Ok((expr, j)) = me {if j < i {return Ok((expr, j))}};
                    return Ok((EOp(*op, a.clone(), Box::new(b)), i));
                }
            }
            Tup(a) | List(a) => {
                let mut res = vec![];
                for i in 0..a.len() {
                    if let Ok((n, j)) = a[i].reduce_eval(knowledge, eval) {
                        // Prefer the reduction that matches the first rule.
                        if let Ok((expr, k)) = me {if k < j {return Ok((expr, k))}};
                        res.push(n);
                        res.extend(a[i+1..].iter().map(|n| n.clone()));
                        if let Tup(_) = self {
                            return Ok((Tup(res), j));
                        } else if let List(_) = self {
                            return Ok((List(res), j));
                        } else {
                            unreachable!();
                        }
                    } else {
                        res.push(a[i].clone());
                    }
                }
            }
            _ => {}
        }

        me
    }

    /// Inlines all symbols using a knowledge base.
    ///
    /// Ignores missing definitions in domain constraints.
    pub fn inline_all(&self, knowledge: &[Knowledge]) -> Result<Expr, Error> {
        match self {
            Sym(a) => {
                for i in 0..knowledge.len() {
                    if let Def(b, c) = &knowledge[i] {
                        if b == a {
                            return Ok(c.clone());
                        }
                    }
                }
                Err(Error::NoDefinition)
            }
            Ret(_) => Ok(self.clone()),
            EOp(op, a, b) => {
                if let Constrain = op {
                    let a = a.inline_all(knowledge)?;
                    match b.inline_all(knowledge) {
                        Err(Error::NoDefinition) => Ok(a),
                        Err(err) => Err(err),
                        Ok(b) => Ok(constr(a, b)),
                    }
                } else {
                    match (a.inline_all(knowledge), b.inline_all(knowledge)) {
                        (Ok(a), Ok(b)) => Ok(EOp(
                            *op,
                            Box::new(a),
                            Box::new(b)
                        )),
                        (Ok(a), Err(_)) => Ok(EOp(
                            *op,
                            Box::new(a),
                            b.clone()
                        )),
                        (Err(_), Ok(b)) => Ok(EOp(
                            *op,
                            a.clone(),
                            Box::new(b)
                        )),
                        (err, _) => err,
                    }
                }
            }
            Tup(a) => {
                let mut res = vec![];
                for i in 0..a.len() {
                    res.push(a[i].inline_all(knowledge)?);
                }
                Ok(Tup(res))
            }
            List(a) => {
                let mut res = vec![];
                for i in 0..a.len() {
                    res.push(a[i].inline_all(knowledge)?);
                }
                Ok(List(res))
            }
        }
    }

    /// Inline a symbol using a knowledge base.
    pub fn inline(&self, sym: &Symbol, knowledge: &[Knowledge]) -> Result<Expr, Error> {
        match self {
            Sym(a) if a == sym => {
                for i in 0..knowledge.len() {
                    if let Def(b, c) = &knowledge[i] {
                        if b == a {
                            return Ok(c.clone());
                        }
                    }
                }
                Err(Error::NoDefinition)
            }
            Sym(_) | Ret(_) => Ok(self.clone()),
            EOp(op, a, b) => {
                Ok(EOp(
                    *op,
                    Box::new(a.inline(sym, knowledge)?),
                    Box::new(b.inline(sym, knowledge)?)
                ))
            }
            Tup(a) => {
                let mut res = vec![];
                for i in 0..a.len() {
                    res.push(a[i].inline(sym, knowledge)?);
                }
                Ok(Tup(res))
            }
            List(a) => {
                let mut res = vec![];
                for i in 0..a.len() {
                    res.push(a[i].inline(sym, knowledge)?);
                }
                Ok(List(res))
            }
        }
    }

    /// Returns `true` if a function has any constraints, `false` if there are none constraints.
    ///
    /// This is used in the following rules in the standard library, using `no_constr`:
    ///
    /// - `∀(f:!{}) => \true`
    /// - `f:!{}([x..]) => f{(: vec)}(x)`
    /// - `f:!{}(a)(a) <=> f{eq}(a)(a)`
    ///
    /// For example, to detect whether it is safe to insert a new constraint.
    /// This check is important because a constraint refers to one or more arguments.
    /// By introducing a new constraint that refers incorrectly to its argument,
    /// it leads to unsoundness.
    ///
    /// A function has none constraints if it is applied enough times to cover existing constraints.
    /// This means the total arity of constraints is less or equal than the total arity of arguments.
    ///
    /// To avoid unsoundness under uncertain edge cases, this function should return `true`.
    /// This is because the `no_constr` check fails to pattern match, which is safe,
    /// since inactive rules do not introduce unsoundness.
    ///
    /// Unfinished: This function requires analysis and unit testing.
    pub fn has_constraint(&self, arity_args: usize) -> bool {
        match self {
            EOp(Constrain, f, a) => {
                if let Some(arity) = a.arity() {
                    if arity > arity_args {true}
                    else {f.has_constraint(arity_args - arity)}
                } else {
                    true
                }
            }
            EOp(Compose, a, b) => b.has_constraint(arity_args) || a.has_constraint(0),
            EOp(Apply, f, _) => f.has_constraint(arity_args + 1),
            Sym(_) => false,
            Ret(_) => false,
            _ => true
        }
    }

    /// Returns `true` if expression is substitution.
    pub fn is_substitution(&self) -> bool {
        self.sub_is_substitution(3)
    }

    fn sub_is_substitution(&self, args: usize) -> bool {
        match self {
            EOp(Apply, f, _) if args > 0 => f.sub_is_substitution(args - 1),
            Sym(Subst) if args == 0 => true,
            _ => false,
        }
    }

    /// Returns `true` if expression has non-constant type judgement.
    pub fn has_non_constant_type_judgement(&self) -> bool {
        match self {
            EOp(Type, _, b) if **b == Sym(RetType) => false,
            EOp(Type, _, _) => true,
            _ => false
        }
    }
}

/// Stores variables bound by context.
pub struct Context {
    /// Contains the variables in the context.
    pub vars: Vec<(Arc<String>, Expr)>,
}

impl Context {
    /// Binds patterns of a `name` expression to a `value` expression.
    pub fn bind(&mut self, name: &Expr, value: &Expr) -> bool {
        match (name, value) {
            (Sym(NoSubstVar(_)), v) if v.is_substitution() => {
                self.vars.clear();
                false
            }
            (Sym(NoConstrVar(_)), v) if v.has_constraint(0) => {
                self.vars.clear();
                false
            }
            (Sym(Var(_)), Tup(_)) | (Sym(NoConstrVar(_)), Tup(_)) => {
                self.vars.clear();
                false
            }
            // Do not pattern match variables to type judgements,
            // since the type judgements might imply exceptions to default rules.
            // Constant type judgements are treated as normal.
            (Sym(Var(_)), v) if v.has_non_constant_type_judgement() => {
                self.vars.clear();
                false
            }
            (Sym(Var(name)), x) |
            (Sym(NoConstrVar(name)), x) |
            (Sym(NoSubstVar(name)), x) => {
                for i in (0..self.vars.len()).rev() {
                    if &self.vars[i].0 == name {
                        if &self.vars[i].1 == x {
                            break
                        } else {
                            self.vars.clear();
                            return false;
                        }
                    }
                }
                self.vars.push((name.clone(), x.clone()));
                true
            }
            (Sym(ArityVar(name, n)), x) if x.arity() == Some(*n) => {
                for i in (0..self.vars.len()).rev() {
                    if &self.vars[i].0 == name {
                        if &self.vars[i].1 == x {
                            break
                        } else {
                            self.vars.clear();
                            return false;
                        }
                    }
                }
                self.vars.push((name.clone(), x.clone()));
                true
            }
            // `x!>y` means `x` does not occur in expression `y`.
            // This is used by rules for partial derivatives.
            (Sym(NotInVarName(name, y)), x) => {
                // Returns a list of names in expression.
                fn get_names(expr: &Expr, ret: &mut Vec<Arc<String>>) {
                    match expr {
                        Sym(Var(y)) => ret.push(y.clone()),
                        Sym(y) if y.arity().is_some() => {}
                        Ret(_) => {}
                        Tup(list) | List(list) => {
                            for x in list {
                                get_names(x, ret);
                            }
                        }
                        EOp(Apply, a, b) => {
                            get_names(a, ret);
                            get_names(b, ret);
                        }
                        // TODO: Handle other cases.
                        _ => {}
                        // x => panic!("not-in-var: {:?}", x),
                    }
                }
                // Returns `true` if expression contains some variable `x`.
                fn contains(expr: &Expr, x: &Arc<String>) -> bool {
                    match expr {
                        Sym(Var(y)) => return x == y,
                        Sym(y) if y.arity().is_some() => return false,
                        Ret(_) => return false,
                        Tup(list) | List(list) => return list.iter().any(|expr| contains(expr, x)),
                        EOp(Apply, a, b) => return contains(a, x) || contains(b, x),
                        // TODO: Handle other cases.
                        _ => {}
                        // x => panic!("not-in-var: {:?}", x),
                    }
                    true
                }

                let mut names = vec![];
                get_names(x, &mut names);
                for i in (0..self.vars.len()).rev() {
                    // Match against previous occurences of same variable.
                    if &self.vars[i].0 == name {
                        if &self.vars[i].1 == x {continue}
                        else {
                            self.vars.clear();
                            return false;
                        }
                    } else if &self.vars[i].0 == y {
                        // It is sufficient that at least one name is missing,
                        // to prove that no term can be constructed that matches the derivative.
                        if names.iter().any(|name| {
                            !contains(&self.vars[i].1, name)
                        }) {continue}
                        else {
                            self.vars.clear();
                            return false;
                        }
                    }
                }
                self.vars.push((name.clone(), x.clone()));
                true
            }
            (Sym(NotRetVar(_)), Ret(_)) | (Sym(NotRetVar(_)), Tup(_)) => {
                self.vars.clear();
                false
            }
            (Sym(NotRetVar(name)), _) => {
                for i in (0..self.vars.len()).rev() {
                    if &self.vars[i].0 == name {
                        if &self.vars[i].1 == value {
                            break
                        } else {
                            self.vars.clear();
                            return false;
                        }
                    }
                }
                self.vars.push((name.clone(), value.clone()));
                true
            }
            (Sym(RetVar(name)), Ret(_)) => {
                for i in (0..self.vars.len()).rev() {
                    if &self.vars[i].0 == name {
                        if &self.vars[i].1 == value {
                            break
                        } else {
                            self.vars.clear();
                            return false;
                        }
                    }
                }
                self.vars.push((name.clone(), value.clone()));
                true
            }
            (Sym(RetIntVar(name)), Ret(F64(x))) if x % 1.0 == 0.0 => {
                for i in (0..self.vars.len()).rev() {
                    if &self.vars[i].0 == name {
                        if &self.vars[i].1 == value {
                            break
                        } else {
                            self.vars.clear();
                            return false;
                        }
                    }
                }
                self.vars.push((name.clone(), value.clone()));
                true
            }
            (Sym(RetPosVar(name)), Ret(F64(x))) if *x >= 0.0 => {
                for i in (0..self.vars.len()).rev() {
                    if &self.vars[i].0 == name {
                        if &self.vars[i].1 == value {
                            break
                        } else {
                            self.vars.clear();
                            return false;
                        }
                    }
                }
                self.vars.push((name.clone(), value.clone()));
                true
            }
            (Sym(RetStrictPosVar(name)), Ret(F64(x))) if *x > 0.0 => {
                for i in (0..self.vars.len()).rev() {
                    if &self.vars[i].0 == name {
                        if &self.vars[i].1 == value {
                            break
                        } else {
                            self.vars.clear();
                            return false;
                        }
                    }
                }
                self.vars.push((name.clone(), value.clone()));
                true
            }
            (Sym(RetNegVar(name)), Ret(F64(x))) if *x < 0.0 => {
                for i in (0..self.vars.len()).rev() {
                    if &self.vars[i].0 == name {
                        if &self.vars[i].1 == value {
                            break
                        } else {
                            self.vars.clear();
                            return false;
                        }
                    }
                }
                self.vars.push((name.clone(), Ret(F64(x.abs()))));
                true
            }
            (Sym(Singleton(name)), List(x)) if x.len() == 1 => {
                self.vars.push((name.clone(), x[0].clone()));
                true
            }
            (Sym(ListVar(name)), List(_)) => {
                self.vars.push((name.clone(), value.clone()));
                true
            }
            (Sym(HeadTailTup(head, tail)), Tup(list)) |
            (Sym(HeadTailList(head, tail)), List(list)) => {
                if list.len() < 2 {return false};

                let r = self.bind(head, &list[0]);
                let b: Expr = if let (Sym(HeadTailTup(_, _)), Tup(_)) = (name, value) {
                    if list[1..].len() == 1 {
                        list[1].clone()
                    } else {
                        Tup(list[1..].into())
                    }
                } else {
                    List(list[1..].into())
                };

                if r {
                    if let Sym(Var(tail)) = &**tail {
                        for i in (0..self.vars.len()).rev() {
                            if &self.vars[i].0 == tail {
                                if &self.vars[i].1 == &b {
                                    break
                                } else {
                                    self.vars.clear();
                                    return false;
                                }
                            }
                        }
                        self.vars.push((tail.clone(), b));
                        true
                    } else {
                        self.vars.clear();
                        false
                    }
                } else {
                    self.vars.clear();
                    false
                }
            }
            (Sym(Any), _) => true,
            (Sym(a), Sym(b)) if a == b => true,
            (Ret(a), Ret(b)) if a == b => true,
            (EOp(op1, a1, b1), EOp(op2, a2, b2)) if op1 == op2 => {
                let r = self.bind(a1, a2) && self.bind(b1, b2);
                if !r {self.vars.clear()};
                r
            }
            (Tup(a), Tup(b)) if a.len() == b.len() => {
                let mut all = true;
                for i in 0..a.len() {
                    let r = self.bind(&a[i], &b[i]);
                    if !r {
                        all = false;
                        break;
                    }
                }
                if !all {self.vars.clear()};
                all
            }
            (List(a), List(b)) if a.len() == b.len() => {
                let mut all = true;
                for i in 0..a.len() {
                    let r = self.bind(&a[i], &b[i]);
                    if !r {
                        all = false;
                        break;
                    }
                }
                if !all {self.vars.clear()};
                all
            }
            _ => {
                self.vars.clear();
                false
            }
        }
    }

    /// Substitute free occurences of variables in context.
    ///
    /// This is used on the right side in a reduction rule.
    pub fn substitute(&self, x: &Expr) -> Result<Expr, Error> {
        match x {
            // Don't synthesize `_`.
            Sym(Any) => Err(Error::InvalidComputation),
            Sym(NoSubstVar(_)) => Err(Error::InvalidComputation),
            Sym(RetNegVar(_)) => Err(Error::InvalidComputation),
            Sym(Var(name)) | Sym(ArityVar(name, _)) => {
                for i in (0..self.vars.len()).rev() {
                    if &self.vars[i].0 == name {
                        return Ok(self.vars[i].1.clone())
                    }
                }
                Err(Error::CouldNotFind(name.clone()))
            }
            Sym(UnopRetVar(a, f)) => {
                let mut av: Option<Expr> = None;
                for i in (0..self.vars.len()).rev() {
                    if &self.vars[i].0 == a {
                        av = Some(self.vars[i].1.clone());
                    }
                }
                match av {
                    Some(Ret(F64(a))) => {
                        Ok(match **f {
                            Even => Ret(Bool(a.round() % 2.0 == 0.0)),
                            Odd => Ret(Bool(a.round() % 2.0 == 1.0)),
                            Neg => Ret(F64(-a)),
                            Inc => Ret(F64(a + 1.0)),
                            Reci => if a == 0.0 {
                                return Err(Error::InvalidComputation)
                            } else {
                                Ret(F64(a.recip()))
                            },
                            Abs => Ret(F64(a.abs())),
                            Prob => Ret(Bool(a >= 0.0 && a <= 1.0)),
                            Probl => Ret(Bool(a >= 0.0 && a < 1.0)),
                            Probr => Ret(Bool(a > 0.0 && a <= 1.0)),
                            Probm => Ret(Bool(a > 0.0 && a < 1.0)),
                            Sqrt => Ret(F64(a.sqrt())),
                            Ln => Ret(F64(a.ln())),
                            Log2 => Ret(F64(a.log2())),
                            Log10 => Ret(F64(a.log10())),
                            Exp => Ret(F64(a.exp())),
                            Sin => Ret(F64(a.sin())),
                            Asin => Ret(F64(a.asin())),
                            Cos => Ret(F64(a.cos())),
                            Acos => Ret(F64(a.acos())),
                            Tan => Ret(F64(a.tan())),
                            Atan => Ret(F64(a.atan())),
                            TypeOf => Sym(F64Type),
                            _ => return Err(Error::InvalidComputation),
                        })
                    }
                    Some(List(a)) => {
                        Ok(match **f {
                            Len => Ret(F64(a.len() as f64)),
                            Dim => matrix::dim(&a)?,
                            Transpose => matrix::transpose(&a)?,
                            IsSquareMat => matrix::is_square_mat(&a)?,
                            _ => return Err(Error::InvalidComputation),
                        })
                    }
                    Some(a) => {
                        Ok(match **f {
                            Arity => {
                                if let Some(n) = a.arity() {Ret(F64(n as f64))}
                                else {return Err(Error::InvalidComputation)}
                            }
                            _ => return Err(Error::InvalidComputation),
                        })
                    }
                    _ => Err(Error::CouldNotFind(a.clone())),
                }
            }
            Sym(BinopRetVar(a, b, f)) => {
                let mut av: Option<Expr> = None;
                let mut bv: Option<Expr> = None;
                for i in (0..self.vars.len()).rev() {
                    if &self.vars[i].0 == a {
                        av = Some(self.vars[i].1.clone());
                    }
                    if &self.vars[i].0 == b {
                        bv = Some(self.vars[i].1.clone());
                    }
                }
                match (av, bv) {
                    (Some(Ret(a)), Some(Ret(b))) if **f == Eq => Ok(Ret(Bool(a == b))),
                    (Some(Ret(F64(a))), Some(Ret(F64(b)))) => {
                        Ok(Ret(F64(match **f {
                            Lt => return Ok(Ret(Bool(a < b))),
                            Le => return Ok(Ret(Bool(a <= b))),
                            Gt => return Ok(Ret(Bool(a > b))),
                            Ge => return Ok(Ret(Bool(a >= b))),
                            Add => a + b,
                            Sub => a - b,
                            Mul => a * b,
                            Pow => a.powf(b),
                            Rem => if b == 0.0 {
                                return Err(Error::InvalidComputation)
                            } else {
                                a % b
                            }
                            Div => if b == 0.0 {
                                return Err(Error::InvalidComputation)
                            } else {
                                a / b
                            }
                            Max2 => if a >= b {a} else {b},
                            Min2 => if a <= b {a} else {b},
                            Base if b >= 0.0 && b < a => {
                                let mut r = vec![Ret(F64(0.0)); a as usize];
                                r[b as usize] = Ret(F64(1.0));
                                return Ok(List(r))
                            }
                            Atan2 => return Ok(Ret(F64(a.atan2(b)))),
                            _ => return Err(Error::InvalidComputation),
                        })))
                    }
                    (Some(Ret(F64(a))), Some(List(b))) => {
                        Ok(match **f {
                            Item if a >= 0.0 && a < b.len() as f64 =>
                                b[a as usize].clone(),
                            Col if a >= 0.0 => matrix::col(a, &b)?,
                            _ => return Err(Error::InvalidComputation),
                        })
                    }
                    (Some(List(a)), Some(List(b))) => {
                        Ok(match **f {
                            Concat => {
                                let mut a = a.clone();
                                a.extend(b.iter().map(|n| n.clone()));
                                List(a)
                            }
                            MulMat => matrix::mul_mat(&a, &b)?,
                            _ => return Err(Error::InvalidComputation),
                        })
                    }
                    (Some(List(a)), Some(b)) => {
                        Ok(match **f {
                            Push => {
                                let mut a = a.clone();
                                a.push(b);
                                List(a)
                            }
                            PushFront => {
                                let mut a = a.clone();
                                a.insert(0, b);
                                List(a)
                            }
                            _ => return Err(Error::InvalidComputation),
                        })
                    }
                    (av, _) => {
                        if av.is_none() {
                            Err(Error::CouldNotFind(a.clone()))
                        } else {
                            Err(Error::CouldNotFind(b.clone()))
                        }
                    }
                }
            }
            Sym(TernopRetVar(a, b, c, f)) => {
                let mut av: Option<Expr> = None;
                let mut bv: Option<Expr> = None;
                let mut cv: Option<Expr> = None;
                for i in (0..self.vars.len()).rev() {
                    if &self.vars[i].0 == a {
                        av = Some(self.vars[i].1.clone());
                    }
                    if &self.vars[i].0 == b {
                        bv = Some(self.vars[i].1.clone());
                    }
                    if &self.vars[i].0 == c {
                        cv = Some(self.vars[i].1.clone());
                    }
                }
                match (av, bv, cv) {
                    (Some(Ret(F64(a))), Some(Ret(F64(b))), Some(Ret(F64(c)))) => {
                        Ok(match **f {
                            Range => if c >= a && c <= b {Ret(Bool(true))}
                                     else {Ret(Bool(false))},
                            Rangel => if c >= a && c < b {Ret(Bool(true))}
                                      else {Ret(Bool(false))},
                            Ranger => if c > a && c <= b {Ret(Bool(true))}
                                      else {Ret(Bool(false))},
                            Rangem => if c > a && c < b {Ret(Bool(true))}
                                      else {Ret(Bool(false))},
                            _ => return Err(Error::InvalidComputation)
                        })
                    }
                    (av, bv, _) => {
                        if av.is_none() {
                            Err(Error::CouldNotFind(a.clone()))
                        } else if bv.is_none() {
                            Err(Error::CouldNotFind(b.clone()))
                        } else {
                            Err(Error::CouldNotFind(c.clone()))
                        }
                    }
                }
            }
            Sym(_) | Ret(_) => Ok(x.clone()),
            EOp(op, a, b) => {
                Ok(EOp(*op, Box::new(self.substitute(a)?), Box::new(self.substitute(b)?)))
            }
            Tup(a) => {
                let mut res = vec![];
                for i in 0..a.len() {
                    res.push(self.substitute(&a[i])?);
                }
                Ok(Tup(res))
            }
            List(a) => {
                let mut res = vec![];
                for i in 0..a.len() {
                    res.push(self.substitute(&a[i])?);
                }
                Ok(List(res))
            }
        }
    }
}

/// Represents an error.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// Invalid function for computing something from left side of expression to right side.
    InvalidComputation,
    /// There was no defintion of the symbol.
    NoDefinition,
    /// There was no matching reduction rule.
    NoReductionRule,
    /// Could not find variable.
    CouldNotFind(Arc<String>),
}

impl Into<Expr> for Symbol {
    fn into(self) -> Expr {Sym(self)}
}

impl Into<Expr> for &'static str {
    fn into(self) -> Expr {Sym(self.into())}
}

impl Into<Symbol> for &'static str {
    fn into(self) -> Symbol {Symbol::from(Arc::new(self.into()))}
}

/// A function applied to one argument.
pub fn app<A: Into<Expr>, B: Into<Expr>>(a: A, b: B) -> Expr {
    EOp(Apply, Box::new(a.into()), Box::new(b.into()))
}

/// A function applied to two arguments.
pub fn app2<A: Into<Expr>, B: Into<Expr>, C: Into<Expr>>(a: A, b: B, c: C) -> Expr {
    app(app(a, b), c)
}

/// A function applied to three arguments.
pub fn app3<A: Into<Expr>, B: Into<Expr>, C: Into<Expr>, D: Into<Expr>>(
    a: A, b: B, c: C, d: D
) -> Expr {
    app2(app(a, b), c, d)
}

/// A function composition.
pub fn comp<A: Into<Expr>, B: Into<Expr>>(a: A, b: B) -> Expr {
    EOp(Compose, Box::new(a.into()), Box::new(b.into()))
}

/// A normal path expression.
pub fn path<A: Into<Expr>, B: Into<Expr>>(a: A, b: B) -> Expr {
    EOp(Path, Box::new(a.into()), Box::new(b.into()))
}

/// A function domain constraint.
pub fn constr<A: Into<Expr>, B: Into<Expr>>(a: A, b: B) -> Expr {
    EOp(Constrain, Box::new(a.into()), Box::new(b.into()))
}

/// A function domain constraint with two arguments.
pub fn constr2<A: Into<Expr>, B: Into<Expr>, C: Into<Expr>>(a: A, b: B, c: C) -> Expr {
    constr(constr(a, b), c)
}

/// A type judgement.
pub fn typ<A: Into<Expr>, B: Into<Expr>>(a: A, b: B) -> Expr {
    EOp(Type, Box::new(a.into()), Box::new(b.into()))
}

/// An `if` expression.
pub fn _if<A: Into<Expr>, B: Into<Expr>>(a: A, b: B) -> Expr {app(app(If, a), b)}

/// A head-tail pattern match on a tuple.
pub fn head_tail_tup<A: Into<Expr>, B: Into<Expr>>(a: A, b: B) -> Expr {
    HeadTailTup(Box::new(a.into()), Box::new(b.into())).into()
}

/// A head-tail pattern match on a list.
pub fn head_tail_list<A: Into<Expr>, B: Into<Expr>>(a: A, b: B) -> Expr {
    HeadTailList(Box::new(a.into()), Box::new(b.into())).into()
}

/// A function variable with arity (number of arguments).
pub fn arity_var<A: Into<String>>(a: A, n: usize) -> Expr {Sym(ArityVar(Arc::new(a.into()), n))}

/// A list variable.
pub fn list_var<A: Into<String>>(a: A) -> Expr {Sym(ListVar(Arc::new(a.into())))}

/// A list variable of length 1.
pub fn singleton<A: Into<String>>(a: A) -> Expr {Sym(Singleton(Arc::new(a.into())))}

/// A value variable.
pub fn ret_var<A: Into<String>>(a: A) -> Expr {Sym(RetVar(Arc::new(a.into())))}

/// A value variable that is an integer.
pub fn ret_int_var<A: Into<String>>(a: A) -> Expr {Sym(RetIntVar(Arc::new(a.into())))}

/// A value variable that is positive or zero.
pub fn ret_pos_var<A: Into<String>>(a: A) -> Expr {Sym(RetPosVar(Arc::new(a.into())))}

/// A value variable that is strictly positive (non-zero).
pub fn ret_strict_pos_var<A: Into<String>>(a: A) -> Expr {Sym(RetStrictPosVar(Arc::new(a.into())))}

/// A value variable that is negative and non-zero.
///
/// Binds to its positive value.
pub fn ret_neg_var<A: Into<String>>(a: A) -> Expr {Sym(RetNegVar(Arc::new(a.into())))}

/// A variable that is not a value variable.
pub fn not_ret_var<A: Into<String>>(a: A) -> Expr {Sym(NotRetVar(Arc::new(a.into())))}

/// A variable of the type value `a : \`.
pub fn ret_type_var<A: Into<String>>(a: A) -> Expr {
    EOp(Type, Box::new(Sym(Var(Arc::new(a.into())))), Box::new(Sym(RetType)))
}

/// Compute a binary function.
pub fn binop_ret_var<A: Into<String>, B: Into<String>, F: Into<Symbol>>(a: A, b: B, f: F) -> Expr {
    Sym(BinopRetVar(Arc::new(a.into()), Arc::new(b.into()), Box::new(f.into())))
}

/// Compute a ternary function.
pub fn ternop_ret_var<A: Into<String>, B: Into<String>, C: Into<String>, F: Into<Symbol>>(
    a: A, b: B, c: C, f: F
) -> Expr {
    Sym(TernopRetVar(Arc::new(a.into()), Arc::new(b.into()), Arc::new(c.into()), Box::new(f.into())))
}

/// Compute a unary function.
pub fn unop_ret_var<A: Into<String>, F: Into<Symbol>>(a: A, f: F) -> Expr {
    Sym(UnopRetVar(Arc::new(a.into()), Box::new(f.into())))
}

/// A function without domain constraints.
pub fn no_constr<A: Into<String>>(a: A) -> Expr {
    Sym(NoConstrVar(Arc::new(a.into())))
}

/// A 2D vector.
pub fn vec2<A: Into<Expr>, B: Into<Expr>>(a: A, b: B) -> Expr {List(vec![a.into(), b.into()])}

/// A 4D vector.
pub fn vec4<X: Into<Expr>, Y: Into<Expr>, Z: Into<Expr>, W: Into<Expr>>(
    x: X, y: Y, z: Z, w: W
) -> Expr {
    List(vec![x.into(), y.into(), z.into(), w.into()])
}

/// A quaternion.
pub fn quat<X: Into<Expr>, Y: Into<Expr>, Z: Into<Expr>, W: Into<Expr>>(
    x: X, y: Y, z: Z, w: W
) -> Expr {
    typ(List(vec![x.into(), y.into(), z.into(), w.into()]), QuatType)
}

/// Knowledge about a component-wise operation on vectors.
pub fn vec_op<S: Into<Symbol>>(s: S) -> Knowledge {
    let s = s.into();
    Red(app(constr(app(constr(s.clone(), app(Rty, VecType)), "x"), app(Rty, VecType)), "y"),
        app2(app(VecOp, s), "x", "y"))
}

/// Knowledge about a concrete binary operation `f(x : \, y : \) => f(x)(y) : \`.
pub fn concrete_op<S: Into<Symbol>>(s: S) -> Knowledge {
    let s = s.into();
    Red(app2(s.clone(), ret_type_var("x"), ret_type_var("y")), typ(app2(s, "x", "y"), RetType))
}

/// Knowledge about a commuative binary operator.
pub fn commutative<S: Into<Symbol>>(s: S) -> Knowledge {
    let s = s.into();
    let a: Expr = "a".into();
    let b: Expr = "b".into();
    Eqv(app(app(s.clone(), a.clone()), b.clone()), app(app(s, b), a))
}

/// Knowledge about an associative binary operator.
pub fn associative<S: Into<Symbol>>(s: S) -> Knowledge {
    let s = s.into();
    let a: Expr = "a".into();
    let b: Expr = "b".into();
    let c: Expr = "c".into();
    Eqv(app(app(s.clone(), a.clone()), app(app(s.clone(), b.clone()), c.clone())),
        app(app(s.clone(), app(app(s, a), b)), c))
}

/// Knowledge about a distributive relationship.
pub fn distributive<M: Into<Symbol>, A: Into<Symbol>>(mul: M, add: A) -> Knowledge {
    let mul = mul.into();
    let add = add.into();
    let a: Expr = "a".into();
    let b: Expr = "b".into();
    let c: Expr = "c".into();
    Eqv(app(app(mul.clone(), a.clone()), app(app(add.clone(), b.clone()), c.clone())),
        app(app(add, app(app(mul.clone(), a.clone()), b)), app(app(mul, a), c)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn apply_not() {
        let ref std = std();
        let a = app(Not, true);
        let a = a.inline(&Not, std).unwrap();
        let a = a.reduce(std).unwrap().0;
        assert_eq!(a, false.into());

        let a = app(Not, false);
        let a = a.inline(&Not, std).unwrap();
        let a = a.reduce(std).unwrap().0;
        assert_eq!(a, true.into());
    }

    #[test]
    fn comp_not_not() {
        let ref std = std();
        let a = comp(Not, Not);
        let a = a.reduce(std).unwrap().0;
        assert_eq!(a, Idb.into());
    }

    #[test]
    fn path_not_not() {
        let ref std = std();
        let a = path(Not, Not);
        let a = a.reduce(std).unwrap().0;
        assert_eq!(a, Not.into());
    }

    #[test]
    fn comp_id() {
        let ref std = std();

        let a = comp(Not, Id);
        let a = a.reduce(std).unwrap().0;
        assert_eq!(a, Not.into());

        let a = comp(Id, Not);
        let a = a.reduce(std).unwrap().0;
        assert_eq!(a, Not.into());
    }

    #[test]
    fn path_not_id() {
        let ref std = std();
        let a = path(Not, Id);
        let a = a.reduce(std).unwrap().0;
        assert_eq!(a, Not.into());
    }

    #[test]
    fn constraints() {
        let f: Expr = "f".into();
        assert_eq!(f.has_constraint(0), false);
        let f: Expr = app(Not, false);
        assert_eq!(f.has_constraint(0), false);
        let f: Expr = constr(Not, true);
        assert_eq!(f.has_constraint(0), true);
        let f: Expr = And.into();
        assert_eq!(f.has_constraint(0), false);
        let f: Expr = constr(And, Eqb);
        assert_eq!(f.has_constraint(0), true);
        let f: Expr = constr(And, Not);
        assert_eq!(f.has_constraint(0), true);
        let f: Expr = app(constr(And, Not), "x");
        assert_eq!(f.has_constraint(0), false);
        let f: Expr = app(constr(And, Eqb), "x");
        assert_eq!(f.has_constraint(0), true);
        let f: Expr = app(And, false);
        assert_eq!(f.has_constraint(0), false);
        // `sum{(: vec)}`
        let f: Expr = constr(Sum, app(Rty, VecType));
        assert_eq!(f.has_constraint(0), true);
        // `add{(>= 0)}`
        let f: Expr = constr(Add, app(Rge, 0.0));
        assert_eq!(f.has_constraint(0), true);
        let f: Expr = comp(Not, Not);
        assert_eq!(f.has_constraint(0), false);
        // `(not . not){not}`
        let f: Expr = constr(comp(Not, Not), true);
        assert_eq!(f.has_constraint(0), true);
        // `not{not} . not`
        let f: Expr = comp(constr(Not, Not), Not);
        assert_eq!(f.has_constraint(0), true);
        // `not . not{not}`
        let f: Expr = comp(Not, constr(Not, Not));
        assert_eq!(f.has_constraint(0), true);
        let f: Expr = true.into();
        assert_eq!(f.has_constraint(0), false);
    }

    #[test]
    fn eval_var() {
        let def = &[Def("x".into(), 0.0.into())];
        let f: Expr = "x".into();
        assert_eq!(f.eval(def).unwrap(), Ret(F64(0.0)));

        let mut def = std();
        def.push(Def("x".into(), 2.0.into()));
        let f: Expr = app2(Add, 1.0, "x");
        assert_eq!(f.eval(&def).unwrap(), Ret(F64(3.0)));

        let mut def = std();
        def.push(Def("x".into(), 0.0.into()));
        let f: Expr = app("sin", "x");
        assert_eq!(f.eval(&def).unwrap(), Ret(F64(0.0)));
    }
}
