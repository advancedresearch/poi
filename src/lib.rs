#![deny(missing_docs)]

//! # Poi
//! a pragmatic point-free theorem prover assistant
//!
//! ```text
//! === Poi Reduce 0.1 ===
//! Type `help` for more information.
//! > and[not]
//! and[not]
//! or			( and[not] => or )
//! ```
//!
//! To run Poi Reduce from your Terminal, type:
//!
//! ```text
//! cargo install --example poireduce poi
//! ```
//!
//! Then, to run:
//!
//! ```text
//! poireduce
//! ```
//!
//! ### Introduction to Poi and Path Semantics
//!
//! In "point-free" or "tacit" programming, functions do not identify the arguments
//! (or "points") on which they operate. See [Wikipedia article](https://en.wikipedia.org/wiki/Tacit_programming).
//!
//! Poi is an implementation of a small subset of [Path Semantics](https://github.com/advancedresearch/path_semantics).
//! In order to explain how Poi works, one needs to explain a bit about Path Semantics.
//!
//! [Path Semantics](https://github.com/advancedresearch/path_semantics) is an extremely expressive language for mathematical programming,
//! which has a "path-space" in addition to normal computation.
//! If normal programming is 2D, then Path Semantics is 3D.
//! Path Semantics is often used in combination with [Category Theory](https://en.wikipedia.org/wiki/Category_theory), [Logic](https://en.wikipedia.org/wiki/Logic), etc.
//!
//! A "path" (or "normal path") is a way of navigating between functions, for example:
//!
//! ```text
//! and[not] <=> or
//! ```
//!
//! Translated into words, this sentence means:
//!
//! ```text
//! If you flip the input and output bits of an `and` function,
//! then you can predict the output directly from the input bits
//! using the function `or`.
//! ```
//!
//! In normal programming, there is no way to express this idea directly,
//! but you can represent the logical relationship as an equation:
//!
//! ```text
//! not(and(a, b)) = or(not(a), not(b))
//! ```
//!
//! This is known as one of [De Morgan's laws](https://en.wikipedia.org/wiki/De_Morgan's_laws).
//!
//! When represented as a commutative diagram, one can visualize the dimensions:
//!
//! ```text
//!          not x not
//!       o ---------> o           o -------> path-space
//!       |            |           |
//!   and |            | or        |
//!       V            V           |
//!       o ---------> o           V
//!            not            computation
//! ```
//!
//! This is written in asymmetric path notation:
//!
//! ```text
//! and[not x not -> not] <=> or
//! ```
//!
//! In symmetric path notation:
//!
//! ```text
//! and[not] <=> or
//! ```
//!
//! Both computation and path-space are directional,
//! meaning that one can not always find the inverse.
//! Composition in path-space is just function composition:
//!
//! ```text
//! f[g][h] <=> f[h . g]
//! ```
//!
//! If one imagines `computation = 2D`, then `computation + path-space = 3D`.
//!
//! Path Semantics can be thought of as "point-free style" sub-set of equations.
//! This sub-set of equations is particularly helpful in programming.
//!
//! ### The Problem of Complexity
//!
//! Efficient mathematical knowledge useful for programming depends on knowing
//! the identity of functions. This means that the more knowledge you want to build,
//! the more functions you need to name and refer to symbolically.
//!
//! This means that mathematical theories using a "birds-eye view" are not as
//! useful to solve specific problems, except as a guide to find the solution.
//! The more general and expressive a theory is, the harder it is to do proof search.
//!
//! As a consequence, theorem proving along both `computation + path-space` is
//! much harder than just theorem proving for `computation`.
//!
//! For example, [Type Theory](https://en.wikipedia.org/wiki/Type_theory) is useful
//! to check that programs are correct, but for higher categories, it becomes
//! increasingly hard to ground the semantics while staying efficient and usable.
//!
//! [Path Semantics](https://github.com/advancedresearch/path_semantics) uses a
//! different approach, which is based on symbols.
//! When a symbol is created, the theory "commits" to preserving the "paths"
//! from the symbol, which is known in [Homotopy Type Theory](https://homotopytypetheory.org/) to correspond to "proofs".
//! Since the symbols themselves encode this relationship to proofs,
//! it means that proofs can be arbitrary complex without affecting complexity.
//!
//! This is different from a pure axiomatic system.
//! In a pure axiomatic system, the symbols do not have meaning except
//! the relationship to each other (the axioms).
//! As a result, you get non-standard interpretations of the Peano axioms.
//! In Path Semantics, if you say "the natural numbers", you *mean* the natural numbers, not the natural numbers as described by the Peano axioms.
//! The symbol "the natural numbers" *is the proof* of what you mean,
//! using the background of path semantical knowledge to interpret it.
//! This is what the "semantics" in Path Semantics means.
//!
//! It is possible to express ideas in Path Semantics which are believed to be true,
//! yet can not be proven to be true in any formal language. Someday, a formal
//! language might be invented to prove the sentence true, but programmers do not
//! wait for this to happen. Instead, they default to pragmatic strategies, such as
//! testing extensively. For example, the Goldebach conjecture has been tested up
//! to some limit, so it holds for all natural numbers below that limit.
//! A pragmatic strategy is what you do when you can not idealize the problem away.
//!
//! Poi uses a pragmatic approach in its design because a lot of proofs in
//! Path Semantics requires no or little type checking in the "point-free style".
//!
//! ### Design of Poi
//!
//! Poi is designed to be used as a Rust library.
//!
//! It means that anybody can create their own tools on top of Poi,
//! without needing a lot of dependencies.
//!
//! Poi uses primarily rewriting-rules for theorem proving.
//! This means that the core design is "stupid" and will do dumb things like running
//! in infinite loops when given the wrong rules.
//!
//! However, this design makes also Poi very flexible, because it can pattern match
//! in any way, independent of computational direction.
//! It is relatively easy to define such rules in Rust code.
//!
//! #### Syntax
//!
//! Poi uses [Piston-Meta](https://github.com/pistondevelopers/meta) to describe its syntax. Piston-Meta is a meta parsing language for human readable text documents.
//! It makes it possible to easily make changes to Poi's grammar,
//! and also preserve backward compatibility.
//!
//! Since Piston-Meta can describe its own grammar rules, it means that future
//! versions of Piston-Meta can parse grammars of old versions of Poi.
//! The old documents can then be transformed into new versions of Poi using synthesis.
//!
//! #### Core Design
//!
//! At the core of Poi, there is the `Expr` structure:
//!
//! ```rust(ignore)
//! /// Function expression.
//! #[derive(Clone, PartialEq, Debug)]
//! pub enum Expr {
//!     /// A symbol that is used together with symbolic knowledge.
//!     Sym(Symbol),
//!     /// Some function that returns a value, ignoring the argument.
//!     ///
//!     /// This can also be used to store values, since zero arguments is a value.
//!     Ret(Value),
//!     /// A binary operation on functions.
//!     Op(Op, Box<Expr>, Box<Expr>),
//!     /// A tuple for more than one argument.
//!     Tup(Vec<Expr>),
//!     /// A list.
//!     List(Vec<Expr>),
//! }
//! ```
//!
//! The simplicity of the `Expr` structure is important and heavily based on
//! advanced path semantical knowledge.
//!
//! A symbol contains every domain-specific symbol and "avatar extensions"
//! of symbols. An "avatar extension" is a technique of integrating information
//! processing from building blocks that have no relations for introspection.
//! This means, that even some variants of `Symbol` are not symbols in a direct sense,
//! they are put there because they "integrate information" of symbols.
//! For example, a variable is classified as a `1-avatar` since it "integrates information" of a single symbol or expression. "Avatar extensions" occur
//! frequently in Path Semantics for very sophisticated mathematical relations, but usually do not need to be represented explicitly.
//! Instead, they are used as a "guide" to design.
//! See the paper [Avatar Graphs](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/avatar-graphs.pdf) for more information.
//!
//! The `Ret` variant comes from the notation used in [Higher Order Operator Overloading](https://github.com/advancedresearch/path_semantics/blob/master/sequences.md#higher-order-operator-overloading). Instead of describing a value as value,
//! it is thought of as a function of some unknown input type, which returns a known value. For example, if a function returns `2` for all inputs, this is written `\2`.
//! This means that point-free transformations on functions sometimes can compute stuff, without explicitly needing to reference the concrete value directly.
//! See paper [Higher Order Operator Overloading and Existential Path Equations](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/higher-order-operator-overloading-and-existential-path-equations.pdf) for more information.
//!
//! The `Op` variant generalizes binary operators on functions,
//! such as `Composition`, `Path` (normal path),
//! `Apply` (call a function) and `Constrain` (partial functions).
//!
//! The `Tup` variant represents tuples of expressions, where a singleton (a tuple of one element) is
//! "lifted up" one level. This is used e.g. to transition from `and[not x not -> not]` to `and[not]` without having to write rules for asymmetric cases.
//!
//! The `List` variant represents lists of expressions, e.g. `[1, 2, 3]`.
//! This differs from `Tup` by the property that singletons are not "lifted up".
//!
//! #### Representing Knowledge
//!
//! In higher dimensions of functional programming, the definition of "normalization"
//! depends on the domain specific use of a theory. Intuitively, since there are
//! more directions, what counts as progression toward an answer is somewhat
//! chosen arbitrarily. Therefore, the subjectivity of this choice must be
//! reflected in the representation of knowledge.
//!
//! Poi's representation of knowledge is designed for multi-purposes.
//! Unlike in normal programming, you do not want to always do e.g. evaluation.
//! Instead, you design different tools for different purposes, using the same
//! knowledge.
//!
//! The `Knowledge` struct represents mathematical knowledge in form of rules:
//!
//! ```rust(ignore)
//! /// Represents knowledge about symbols.
//! pub enum Knowledge {
//!     /// A symbol has some definition.
//!     Def(Symbol, Expr),
//!     /// A reduction from a more complex expression into another by normalization.
//!     Red(Expr, Expr),
//!     /// Two expressions that are equivalent but neither normalizes the other.
//!     Eqv(Expr, Expr),
//! }
//! ```
//!
//! The `Def` variant represents a definition.
//! A definition is inlined when evaluating an expression.
//!
//! The `Red` variant represents what counts as "normalization" in a domain specific theory.
//! It can use computation in the sense of normal evaluation, or use path-space.
//! This rule is directional, which means it pattern matches on the first expression
//! and binds variables, which are synthesized using the second expression.
//!
//! The `Eqv` variant represents choices that one can make when traveling along a path.
//! Going in one direction might be as good as another.
//! This is used when it is not clear which direction one should go.
//! This rule is bi-directional, which means one can treat it as a reduction both ways.
//!

use std::sync::Arc;

use self::Expr::*;
use self::Op::*;
use self::Value::*;
use self::Knowledge::*;
use self::Symbol::*;

pub use val::*;
pub use expr::*;
pub use sym::*;
pub use standard_library::*;
pub use parsing::*;
pub use knowledge::*;

mod val;
mod expr;
mod sym;
mod knowledge;
mod standard_library;
mod parsing;

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
            if let Eqv(a, b) = &knowledge[i] {
                if ctx.bind(a, self) {
                    let expr = ctx.substitute(b).unwrap();
                    res.push((expr, i));
                    ctx.vars.clear();
                } else if ctx.bind(b, self) {
                    let expr = ctx.substitute(a).unwrap();
                    res.push((expr, i));
                    ctx.vars.clear();
                }
            }
        }
        res
    }

    /// Evaluate an expression using a knowledge base.
    ///
    /// This combines reductions and inlining of all symbols.
    pub fn eval(&self, knowledge: &[Knowledge]) -> Result<Expr, Error> {
        let mut me = self.clone();
        loop {
            let expr = me.reduce_all(knowledge).inline_all(knowledge)?;
            if expr == me {break};
            me = expr;
        }
        Ok(me)
    }

    /// Reduces an expression using a knowledge base, until it can not be reduces further.
    pub fn reduce_all(&self, knowledge: &[Knowledge]) -> Expr {
        let mut me = self.clone();
        while let Ok((expr, _)) = me.reduce(knowledge) {me = expr}
        me
    }

    /// Reduces expression one step using a knowledge base.
    pub fn reduce(&self, knowledge: &[Knowledge]) -> Result<(Expr, usize), Error> {
        let mut ctx = Context {vars: vec![]};
        let mut me: Option<(Expr, usize)> = None;
        for i in 0..knowledge.len() {
            if let Red(a, b) = &knowledge[i] {
                if ctx.bind(a, self) {
                    let expr = ctx.substitute(b)?;
                    me = Some((expr, i));
                    break;
                }
            }
        }

        match self {
            Op(op, a, b) => {
                if let Ok((a, i)) = a.reduce(knowledge) {
                    // Prefer the reduction that matches the first rule.
                    if let Some((expr, j)) = me {if j < i {return Ok((expr, j))}};
                    return Ok((Op(*op, Box::new(a), b.clone()), i));
                }
                if let Ok((b, i)) = b.reduce(knowledge) {
                    // Prefer the reduction that matches the first rule.
                    if let Some((expr, j)) = me {if j < i {return Ok((expr, j))}};
                    return Ok((Op(*op, a.clone(), Box::new(b)), i));
                }
            }
            Tup(a) => {
                let mut res = vec![];
                for i in 0..a.len() {
                    if let Ok((n, j)) = a[i].reduce(knowledge) {
                        // Prefer the reduction that matches the first rule.
                        if let Some((expr, k)) = me {if k < j {return Ok((expr, k))}};
                        res.push(n);
                        res.extend(a[i+1..].iter().map(|n| n.clone()));
                        return Ok((Tup(res), j));
                    } else {
                        res.push(a[i].clone());
                    }
                }
            }
            _ => {}
        }

        if let Some((expr, i)) = me {
            Ok((expr, i))
        } else {
            Err(Error::NoReductionRule)
        }
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
            Op(op, a, b) => {
                if let Constrain = op {
                    let a = a.inline_all(knowledge)?;
                    match b.inline_all(knowledge) {
                        Err(Error::NoDefinition) => Ok(a),
                        Err(err) => Err(err),
                        Ok(b) => Ok(constr(a, b)),
                    }
                } else {
                    Ok(Op(
                        *op,
                        Box::new(a.inline_all(knowledge)?),
                        Box::new(b.inline_all(knowledge)?)
                    ))
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
            Op(op, a, b) => {
                Ok(Op(
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
            (Sym(NoConstrVar(_)), Op(Constrain, _, _)) => {
                self.vars.clear();
                false
            }
            (Sym(Var(_)), Tup(_)) | (Sym(NoConstrVar(_)), Tup(_)) => {
                self.vars.clear();
                false
            }
            (Sym(Var(name)), x) | (Sym(NoConstrVar(name)), x) => {
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
            (Sym(HeadTail(head, tail)), Tup(list)) => {
                if list.len() < 2 {return false};

                let r = self.bind(head, &list[0]);
                let b: Expr = if list[1..].len() == 1 {
                    list[1].clone()
                } else {
                    Tup(list[1..].into())
                };
                let r = r && self.bind(tail, &b);
                if !r {self.vars.clear()};
                r
            }
            (Sym(Any), _) => true,
            (Sym(a), Sym(b)) if a == b => true,
            (Ret(a), Ret(b)) if a == b => true,
            (Op(op1, a1, b1), Op(op2, a2, b2)) if op1 == op2 => {
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
            Sym(Var(name)) => {
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
                            Neg => Ret(F64(-a)),
                            _ => return Err(Error::InvalidComputation),
                        })
                    }
                    Some(List(a)) => {
                        Ok(match **f {
                            Len => Ret(F64(a.len() as f64)),
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
                            Add => a + b,
                            Sub => a - b,
                            Mul => a * b,
                            Div => if b == 0.0 {
                                return Err(Error::InvalidComputation)
                            } else {
                                a / b
                            }
                            _ => return Err(Error::InvalidComputation),
                        })))
                    }
                    (Some(List(a)), Some(List(b))) => {
                        Ok(match **f {
                            Concat => {
                                let mut a = a.clone();
                                a.extend(b.iter().map(|n| n.clone()));
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
            Sym(_) | Ret(_) => Ok(x.clone()),
            Op(op, a, b) => {
                Ok(Op(*op, Box::new(self.substitute(a)?), Box::new(self.substitute(b)?)))
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

/// Binary operation on functions.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Op {
    /// Function composition `f . g`
    Compose,
    /// Path `f[g]`
    Path,
    /// Apply function to some argument.
    Apply,
    /// Constrain function input.
    Constrain,
}

impl Into<Expr> for Symbol {
    fn into(self) -> Expr {Sym(self)}
}

impl Into<Expr> for &'static str {
    fn into(self) -> Expr {Sym(Var(Arc::new(self.into())))}
}

impl Into<Symbol> for &'static str {
    fn into(self) -> Symbol {Var(Arc::new(self.into()))}
}

/// A function applied to some argument.
pub fn app<A: Into<Expr>, B: Into<Expr>>(a: A, b: B) -> Expr {
    Op(Apply, Box::new(a.into()), Box::new(b.into()))
}

/// A function composition.
pub fn comp<A: Into<Expr>, B: Into<Expr>>(a: A, b: B) -> Expr {
    Op(Compose, Box::new(a.into()), Box::new(b.into()))
}

/// A normal path expression.
pub fn path<A: Into<Expr>, B: Into<Expr>>(a: A, b: B) -> Expr {
    Op(Path, Box::new(a.into()), Box::new(b.into()))
}

/// A function domain constraint.
pub fn constr<A: Into<Expr>, B: Into<Expr>>(a: A, b: B) -> Expr {
    Op(Constrain, Box::new(a.into()), Box::new(b.into()))
}

/// An `if` expression.
pub fn _if<A: Into<Expr>, B: Into<Expr>>(a: A, b: B) -> Expr {app(app(If, a), b)}

/// A head-tail pattern match on a tuple.
pub fn head_tail<A: Into<Expr>, B: Into<Expr>>(a: A, b: B) -> Expr {
    HeadTail(Box::new(a.into()), Box::new(b.into())).into()
}

/// A value variable.
pub fn ret_var<A: Into<String>>(a: A) -> Expr {Sym(RetVar(Arc::new(a.into())))}

/// Compute a binary function.
pub fn binop_ret_var<A: Into<String>, B: Into<String>, F: Into<Symbol>>(a: A, b: B, f: F) -> Expr {
    Sym(BinopRetVar(Arc::new(a.into()), Arc::new(b.into()), Box::new(f.into())))
}

/// Compute a unary function.
pub fn unop_ret_var<A: Into<String>, F: Into<Symbol>>(a: A, f: F) -> Expr {
    Sym(UnopRetVar(Arc::new(a.into()), Box::new(f.into())))
}

/// A function without domain constraints.
pub fn no_constr<A: Into<String>>(a: A) -> Expr {
    Sym(NoConstrVar(Arc::new(a.into())))
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
    fn red_singleton() {
        let ref std = std();
        let a = Tup(vec![true.into()]);
        let a = a.reduce(std).unwrap().0;
        assert_eq!(a, true.into());
    }
}
