# Poi
a pragmatic point-free theorem prover assistant

[Standard Library](./assets/std.md)

```text
=== Poi 0.24 ===
Type `help` for more information.
> and[not]
and[not]
or
∵ and[not] => or
<=>  (not · and) · (not · fst, not · snd)
     ∵ (not · and) · (not · fst, not · snd) <=> or
<=>  not · nor
     ∵ not · nor <=> or
∴ or
```

Poi uses a mathematical knowledge base to do theorem proving
automatically, but also shows alternatives to you.

- `∵` means "because"
- `∴` means "therefore"
- `<=>` an alternative

To run Poi Reduce from your Terminal, type:

```text
cargo install --example poi poi
```

Then, to run:

```text
poi
```

You can use `help` to learn more about commands in Poi and the theory behind it.

Download and check it out! (Think about it as a tool to learn by doing)

Also, check out the FAQ on Path Semantics:

- [What is the overall problem?](https://github.com/advancedresearch/path_semantics/blob/master/faq.md#what-is-the-overall-problem)
- [Why normal paths?](https://github.com/advancedresearch/path_semantics/blob/master/faq.md#why-normal-paths)

### Example: Length of concatenated lists

Poi lets you specify a goal and automatically prove it.

For example, when computing the length of two concatenated lists,
there is a faster way, which is to compute the length of each list and add them together:

```text
> goal len(a)+len(b)
new goal: (len(a) + len(b))
> len(a++b)
len((a ++ b))
depth: 1 <=>  (len · concat)(a)(b)
     ∵ (f · g)(a)(b) <=> f(g(a)(b))
.
(len · concat)(a)(b)
(concat[len] · (len · fst, len · snd))(a)(b)
∵ len · concat => concat[len] · (len · fst, len · snd)
(add · (len · fst, len · snd))(a)(b)
∵ concat[len] => add
depth: 0 <=>  ((len · fst)(a)(b) + (len · snd)(a)(b))
     ∵ (f · (g0, g1))(a)(b) <=> f(g0(a)(b))(g1(a)(b))
((len · fst)(a)(b) + (len · snd)(a)(b))
(len(a) + (len · snd)(a)(b))
∵ (f · fst)(a)(_) => f(a)
(len(a) + len(b))
∵ (f · snd)(_)(a) => f(a)
∴ (len(a) + len(b))
Q.E.D.
```

The notation `concat[len]` is a "normal path",
which lets you transform into a more efficient program.
Normal paths are composable and point-free,
unlike their equational representations.

### Example: Levenshtein proof search

For deep automated theorem proving, Poi uses Levenshtein distance heuristic.
This is simply the minimum single-character edit distance in text representation.

Try the following:

```text
> goal a + b + c + d
> d + c + b + a
> auto lev
```

The command `auto lev` tells Poi to automatically pick the equivalence with
smallest Levenshtein distance found in any sub-proof.

### Introduction to Poi and Path Semantics

In "point-free" or "tacit" programming, functions do not identify the arguments
(or "points") on which they operate. See [Wikipedia article](https://en.wikipedia.org/wiki/Tacit_programming).

Poi is an implementation of a small subset of [Path Semantics](https://github.com/advancedresearch/path_semantics).
In order to explain how Poi works, one needs to explain a bit about Path Semantics.

[Path Semantics](https://github.com/advancedresearch/path_semantics) is an extremely expressive language for mathematical programming,
which has a "path-space" in addition to normal computation.
If normal programming is 2D, then Path Semantics is 3D.
Path Semantics is often used in combination with [Category Theory](https://en.wikipedia.org/wiki/Category_theory), [Logic](https://en.wikipedia.org/wiki/Logic), etc.

A "path" (or "normal path") is a way of navigating between functions, for example:

```text
and[not] <=> or
```

Translated into words, this sentence means:

```text
If you flip the input and output bits of an `and` function,
then you can predict the output directly from the input bits
using the function `or`.
```

In normal programming, there is no way to express this idea directly,
but you can represent the logical relationship as an equation:

```text
not(and(a, b)) = or(not(a), not(b))
```

This is known as one of [De Morgan's laws](https://en.wikipedia.org/wiki/De_Morgan's_laws).

When represented as a commutative diagram, one can visualize the dimensions:

```text
         not x not
      o ---------> o           o -------> path-space
      |            |           |  x
  and |            | or        |     x
      V            V           |   x
      o ---------> o           V        x - Sets are points
           not            computation
```

Computation and paths is like complex numbers
where the "real" part is computation and
the "imaginary" part is the path.

This is written in asymmetric path notation:

```text
and[not x not -> not] <=> or
```

In symmetric path notation:

```text
and[not] <=> or
```

Both computation and path-space are directional,
meaning that one can not always find the inverse.
Composition in path-space is just function composition:

```text
f[g][h] <=> f[h . g]
```

If one imagines `computation = 2D`, then `computation + path-space = 3D`.

Path Semantics can be thought of as "point-free style" sub-set of equations.
This sub-set of equations is particularly helpful in programming.

### Design of Poi

Poi is designed to be used as a Rust library.

It means that anybody can create their own tools on top of Poi,
without needing a lot of dependencies.

Poi uses primarily rewriting-rules for theorem proving.
This means that the core design is "stupid" and will do dumb things like running
in infinite loops when given the wrong rules.

However, this design makes also Poi very flexible, because it can pattern match
in any way, independent of computational direction.
It is relatively easy to define such rules in Rust code.

#### Syntax

Poi uses [Piston-Meta](https://github.com/pistondevelopers/meta) to describe its syntax. Piston-Meta is a meta parsing language for human readable text documents.
It makes it possible to easily make changes to Poi's grammar,
and also preserve backward compatibility.

Since Piston-Meta can describe its own grammar rules, it means that future
versions of Piston-Meta can parse grammars of old versions of Poi.
The old documents can then be transformed into new versions of Poi using synthesis.

#### Core Design

At the core of Poi, there is the `Expr` structure:

```rust(ignore)
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
    EOp(Op, Box<Expr>, Box<Expr>),
    /// A tuple for more than one argument.
    Tup(Vec<Expr>),
    /// A list.
    List(Vec<Expr>),
}
```

The simplicity of the `Expr` structure is important and heavily based on
advanced path semantical knowledge.

A symbol contains every domain-specific symbol and generalisations of symbols.

The `Ret` variant comes from the notation used in [Higher Order Operator Overloading](https://github.com/advancedresearch/path_semantics/blob/master/sequences.md#higher-order-operator-overloading). Instead of describing a value as value,
it is thought of as a function of some unknown input type, which returns a known value. For example, if a function returns `2` for all inputs, this is written `\2`.
This means that point-free transformations on functions sometimes can compute stuff, without explicitly needing to reference the concrete value directly.
See paper [Higher Order Operator Overloading and Existential Path Equations](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/higher-order-operator-overloading-and-existential-path-equations.pdf) for more information.

The `EOp` variant generalizes binary operators on functions,
such as `Composition`, `Path` (normal path),
`Apply` (call a function) and `Constrain` (partial functions).

The `Tup` variant represents tuples of expressions, where a singleton (a tuple of one element) is
"lifted up" one level. This is used e.g. to transition from `and[not x not -> not]` to `and[not]` without having to write rules for asymmetric cases.

The `List` variant represents lists of expressions, e.g. `[1, 2, 3]`.
This differs from `Tup` by the property that singletons are not "lifted up".

#### Representing Knowledge

In higher dimensions of functional programming, the definition of "normalization"
depends on the domain specific use of a theory. Intuitively, since there are
more directions, what counts as progression toward an answer is somewhat
chosen arbitrarily. Therefore, the subjectivity of this choice must be
reflected in the representation of knowledge.

Poi's representation of knowledge is designed for multi-purposes.
Unlike in normal programming, you do not want to always do e.g. evaluation.
Instead, you design different tools for different purposes, using the same
knowledge.

The `Knowledge` struct represents mathematical knowledge in form of rules:

```rust(ignore)
/// Represents knowledge about symbols.
pub enum Knowledge {
    /// A symbol has some definition.
    Def(Symbol, Expr),
    /// A reduction from a more complex expression into another by normalization.
    Red(Expr, Expr),
    /// Two expressions that are equivalent but neither normalizes the other.
    Eqv(Expr, Expr),
    /// Two expressions that are equivalent but evaluates from left to right.
    EqvEval(Expr, Expr),
}
```

The `Def` variant represents a definition.
A definition is inlined when evaluating an expression.

The `Red` variant represents what counts as "normalization" in a domain specific theory.
It can use computation in the sense of normal evaluation, or use path-space.
This rule is directional, which means it pattern matches on the first expression
and binds variables, which are synthesized using the second expression.

The `Eqv` variant represents choices that one can make when traveling along a path.
Going in one direction might be as good as another.
This is used when it is not clear which direction one should go.
This rule is bi-directional, which means one can treat it as a reduction both ways.

The `EqvEval` variant is similar to `Eqv`, but when evaluating an expression, it
reduces from left to right. This is used on e.g. `sin(τ / 8)`.
You usually want the readability of `sin(τ / 8)` when doing theorem proving.
For example, in Poi Reduce, the value of `sin(τ / 8)` is presented as a choice (equivalence).
When evaluating an expression it is desirable to just replace it with the computed value.

### What Poi is not

Some people hoped that Poi might be used to solve problems
where dependent types are used, but in a more convenient way.

Although Poi uses ideas from dependent types, it is not suitable for other applications
of dependent types, e.g. verification of programs by applying it to some immediate representation of machine code.

Normal paths might be used for such applications in the future,
but this might require a different architecture.

This implementation is designed for algebraic problems:

- The object model is restricted to dynamical types
- Reductions are balanced with equivalences

This means that not everything is provable,
because this makes automated theorem proving harder,
something that is required for the necessary depth of algebraic solving.
