use super::*;

/// Standard library knowledge base.
pub fn std() -> Vec<Knowledge> {
    vec![
        Def(False1, Ret(Bool(false))),
        Def(Not, _if(false, true)),
        Def(Idb, _if(true, false)),
        Def(True1, Ret(Bool(true))),
        Def(And, _if(_if(true, false), false)),
        Def(Or, _if(true, _if(true, false))),
        Def(Eqb, _if(_if(true, false), _if(false, true))),
        Def(Xor, _if(_if(false, true), _if(true, false))),
        Def(Nand, _if(_if(false, true), true)),
        Def(Nor, _if(false, _if(false, true))),
        Def(Exc, _if(_if(false, true), false)),
        Def(Imply, _if(_if(true, false), true)),
        Def(Fstb, _if(true, false)),
        Def(Sndb, _if(_if(true, false), _if(true, false))),
        // `x(y, z) => x(y)(z)`
        Red(app("x", head_tail("y", "z")), app(app("x", "y"), "z")),
        // `if(x, _)(true) => x`
        Red(app(_if("x", Any), true), "x".into()),
        // `if(_, x)(false) => x`
        Red(app(_if(Any, "x"), false), "x".into()),
        // `if(x, _){_}(true) => x`
        Red(constr(app(_if("x", Any), Any), true), "x".into()),
        // `if(_, x){_}(false) => x`
        Red(constr(app(_if(Any, "x"), Any), false), "x".into()),
        Red(Tup(vec!["x".into()]), "x".into()),
        Red(app(ret_var("x"), Any), "x".into()),
        Red(app("x", Tup(vec![])), "x".into()),
        // `f[g -> g] => f[g]`
        Red(path("f", ("g", "g")), path("f", "g")),
        // `f[g x g -> g] => f[g]`
        Red(path("f", ("g", "g", "g")), path("f", "g")),
        // `not . not <=> idb`
        Red(comp(Not, Not), Idb.into()),
        // `not[not] <=> not`
        Red(path(Not, Not), Not.into()),
        // `idb => id`
        Red(Idb.into(), Id.into()),
        // `x . id => x`
        Red(comp("x", Id), "x".into()),
        // `id . x` => x
        Red(comp(Id, "x"), "x".into()),
        // `x[id] => x`
        Red(path("x", Id), "x".into()),
        // `id[x] => id`
        Red(path(Id, "x"), Id.into()),
        // `and[not] => or`.
        Red(path(And, Not), Or.into()),
        // `or[not] => and`.
        Red(path(Or, Not), And.into()),
        // `xor[not] => eqb`.
        Red(path(Xor, Not), Eqb.into()),
        // `eqb[not] => xor`.
        Red(path(Eqb, Not), Xor.into()),
        // `nand[not] => nor`
        Red(path(Nand, Not), Nor.into()),
        // `nor[not] => nand`
        Red(path(Nor, Not), Nand.into()),
        // `nand[not x not -> id] => and[not]`
        Red(path(Nand, (Not, Not, Id)), path(And, Not)),
        // `not . nand => and`.
        Red(comp(Not, Nand), And.into()),
        // `not . nor => or`.
        Red(comp(Not, Nor), Or.into()),
        // `not . and => nand`.
        Red(comp(Not, And), Nand.into()),
        // `not . or => nor`.
        Red(comp(Not, Or), Nor.into()),
        // `not . eqb => xor`.
        Red(comp(Not, Eqb), Xor.into()),
        // `not . xor => eqb`.
        Red(comp(Not, Xor), Eqb.into()),

        // `add[even] => eqb`.
        Red(path(Add, Even), Eqb.into()),
        // `add[odd] => xor`.
        Red(path(Add, Odd), Xor.into()),
        // `mul[even] => or`.
        Red(path(Mul, Even), Or.into()),
        // `mul[odd] => and`.
        Red(path(Mul, Odd), And.into()),
        // `not . even => odd`.
        Red(comp(Not, Even), Odd.into()),
        // `not . odd => even`
        Red(comp(Not, Odd), Even.into()),

        // `add[exp] => mul`
        Red(path(Add, Exp), Mul.into()),
        // `mul[ln] => add`
        Red(path(Mul, Ln), Add.into()),
        // `exp . ln`
        Red(comp(Exp, Ln), Id.into()),
        // `ln . exp`
        Red(comp(Ln, Exp), Id.into()),

        // `false1(_) => false`
        Red(app(False1, Any), false.into()),
        // `true1(_) => true`
        Red(app(True1, Any), true.into()),
        // `id(x) => x`
        Red(app(Id, "x"), "x".into()),
        // `and(true) => idb`
        Red(app(And, true), Idb.into()),
        // `and(false) => false1`
        Red(app(And, false), False1.into()),
        // `or(true) => true1`
        Red(app(Or, true), True1.into()),
        // `or(false) => idb`
        Red(app(Or, false), Idb.into()),
        // `fstb(x)(y) => x`
        Red(app(app(Fstb, "x"), "y"), "x".into()),
        // `fst(x)(y) => x`
        Red(app(app(Fst, "x"), "y"), "x".into()),
        // `sndb(x)(y) => y`
        Red(app(app(Sndb, "x"), "y"), "y".into()),
        // `snd(x)(y) => y`
        Red(app(app(Snd, "x"), "y"), "y".into()),
        // `eqb(false) => not`
        Red(app(Eqb, false), Not.into()),
        // `eqb(true) => idb`
        Red(app(Eqb, true), Idb.into()),

        // `add(x)(y) => x + y`
        Red(app(app(Add, ret_var("x")), ret_var("y")), binop_ret_var("x", "y", Add)),
        // `sub(x)(y) => x - y`
        Red(app(app(Sub, ret_var("x")), ret_var("y")), binop_ret_var("x", "y", Sub)),
        // `mul(x)(y) => x * y`
        Red(app(app(Mul, ret_var("x")), ret_var("y")), binop_ret_var("x", "y", Mul)),
        // `eq(x)(y) => x == y`
        Red(app(app(Eq, ret_var("x")), ret_var("y")), binop_ret_var("x", "y", Eq)),
        // `concat(x)(y) => x ++ y`
        Red(app(app(Concat, "x"), "y"), binop_ret_var("x", "y", Concat)),
        // `len(x) => $len(x)`
        Red(app(Len, "x"), unop_ret_var("x", Len)),

        // `add(0)(x) => x`
        Red(app(app(Add, 0.0), "x"), "x".into()),
        // `add(x)(0) => x`
        Red(app(app(Add, "x"), 0.0), "x".into()),

        // `concat[len] => add`
        Red(path(Concat, Len), Add.into()),
        // `concat[sum] => add`
        Red(path(Concat, Sum), Add.into()),
        // `concat[min] => min2`
        Red(path(Concat, Min), Min2.into()),
        // `concat[max] => max2`
        Red(path(Concat, Max), Max2.into()),

        // `mul_mat[det] => mul`
        Red(path(MulMat, Det), Mul.into()),
        // `mul_mat[fst . dim x snd . dim -> dim] => id`
        Red(path(MulMat, (comp(Fst, Dim), comp(Snd, Dim), Dim)), Id.into()),

        // `if(a, b)[not -> id] => if(b, a)`.
        Red(path(_if("a", "b"), (Not, Id)), _if("b", "a")),
        // `f[id -> g] => g . f`.
        Red(path("f", (Id, "g")), comp("g", "f")),
        // `f[id x id -> g] => g . f`
        Red(path("f", (Id, Id, "g")), comp("g", "f")),
        // `not . (not . x) => x`.
        Red(comp(Not, comp(Not, "x")), "x".into()),

        // `and{eq} => fstb`
        Red(constr(And, Eq), Fstb.into()),
        // `or{eqb} => fstb`
        Red(constr(Or, Eqb), Fstb.into()),
        // `eq{eq} => \true`
        Red(constr(Eq, Eq), true.into()),
        // `sub{eq} => \0`
        Red(constr(Sub, Eq), 0.0.into()),
        // `add{eq}(x, _) => mul(2)(x)`
        Red(app(app(constr(Add, Eq), "x"), Any), app(app(Mul, 2.0), "x")),
        // `\x{eq}(_) => \x`
        Red(app(constr(ret_var("x"), Eq), Any), "x".into()),
        // `f(a)(a) => f{eq}(a)(a)`
        Red(app(app(no_constr("f"), "a"), "a"), app(app(constr("f", Eq), "a"), "a")),

        // `fstb => fst`
        Red(Fstb.into(), Fst.into()),
        // `sndb => snd`
        Red(Sndb.into(), Snd.into()),
        // `eqb => eq`
        Red(Eqb.into(), Eq.into()),

        // `len . concat => concat[len] . (len, len)`
        Red(comp(Len, Concat), comp(path(Concat, Len), (Len, Len))),
        // `(f, g)(a, b) => (f(a), g(b))`
        Red(app(app(("f", "g"), "a"), "b"), (app("f", "a"), app("g", "b")).into()),

        // `(x, y) . (a, b) => (x . a, y . b)`.
        Red(comp(("x", "y"), ("a", "b")), (comp("x", "a"), comp("y", "b")).into()),
        // `(x, y, z) . (a, b, c) => (x . a, y . b, z . c)`.
        Red(comp(("x", "y", "z"), ("a", "b", "c")),
            (comp("x", "a"), comp("y", "b"), comp("z", "c")).into()),
        // `h . f[g -> id] => f[g -> h]`.
        Red(comp("h", path("f", ("g", Id))), path("f", ("g", "h"))),
        // `h . f[g0 x g1 -> id] => f[g0 x g1 -> h]`.
        Red(comp("h", path("f", ("g0", "g1", Id))), path("f", ("g0", "g1", "h"))),

        // `f[g][h] <=> f[h . g]`.
        Eqv(path(path("f", "g"), "h"), path("f", comp("h", "g"))),
        // `f . (g . h) <=> (f . g) . h`.
        Eqv(comp("f", comp("g", "h")), comp(comp("f", "g"), "h")),
        // `f[g] <=> f[g -> id][id -> g]`
        Eqv(path("f", "g"), path(path("f", ("g", Id)), (Id, "g"))),
        // `(f . g)(a) <=> f(g(a))`
        Eqv(app(comp("f", "g"), "a"), app("f", app("g", "a"))),
        // `(f . (g0, g1))(a)(b) <=> f(g0(a))(g1(b))`
        Eqv(app(app(comp("f", ("g0", "g1")), "a"), "b"),
            app(app("f", app("g0", "a")), app("g1", "b"))),
        // `(g . f)(a)(b) <=> f[g](g(a))(g(b))`
        Eqv(app(app(comp("g", "f"), "a"), "b"),
            app(app(path("f", "g"), app("g", "a")), app("g", "b"))),
        // `(g . f)(a) <=> f[g](g(a))`
        Eqv(app(comp("g", "f"), "a"), app(path("f", "g"), app("g", "a"))),
    ]
}
