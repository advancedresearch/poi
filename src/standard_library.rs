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

        // `x((y, z..)) => x(y)(z)`
        Red(app("x", head_tail_tup("y", "z")), app2("x", "y", "z")),
        // `x{(y, z..)} => x{y}{z}`
        Red(constr("x", head_tail_tup("y", "z")), constr(constr("x", "y"), "z")),
        // `x{y}{z}(a)(b) => x{y}(a){z}(b)`
        Red(app2(constr(constr("x", "y"), "z"), "a", "b"),
            app(constr(app(constr("x", "y"), "a"), "z"), "b")),
        // `(g, f)(y, z) => (g(y)(z), f(y)(z))`
        Red(app(("g", "f"), head_tail_tup("y", "z")),
           (app2("g", "y", "z"), app2("f", "y", "z")).into()),
        // `if(x, _)(true) => x`
        Red(app(_if("x", Any), true), "x".into()),
        // `if(_, x)(false) => x`
        Red(app(_if(Any, "x"), false), "x".into()),
        // `if(x, _){_}(true) => x`
        Red(constr(app(_if("x", Any), Any), true), "x".into()),
        // `if(_, x){_}(false) => x`
        Red(constr(app(_if(Any, "x"), Any), false), "x".into()),
        // `(x) => x`
        Red(Tup(vec!["x".into()]), "x".into()),
        // `\x(_) => x`
        Red(app(ret_var("x"), Any), "x".into()),
        // `∃(\x) => eq(x)`
        Red(app(Ex, ret_var("x")), app(Eq, "x")),
        // `∃(f{f}) => idb`
        Red(app(Ex, constr("f", "f")), Idb.into()),
        // `x() => x`
        Red(app("x", Tup(vec![])), "x".into()),
        // `f[g -> g] => f[g]`
        Red(path("f", ("g", "g")), path("f", "g")),
        // `f[g x g -> g] => f[g]`
        Red(path("f", ("g", "g", "g")), path("f", "g")),
        // `∀(f:[arity]2{g0}{g1}) => (g0, g1)`
        Red(app(Triv, constr2(arity_var("f", 2), "g0", "g1")), ("g0", "g1").into()),
        // `∀(f:[arity]1{g}) => g`
        Red(app(Triv, constr(arity_var("f", 1), "g")), "g".into()),
        // `∀(f:!{}) => \true`
        Red(app(Triv, no_constr("f")), true.into()),

        // `type_of(true) => bool`
        Red(app(TypeOf, true), BoolType.into()),
        // `type_of(false) => bool`
        Red(app(TypeOf, false), BoolType.into()),
        // `type_of(\x) => compute::type_of(x)`
        Red(app(TypeOf, ret_var("x")), unop_ret_var("x", TypeOf)),
        // `type_of([x..]) => vec`
        Red(app(TypeOf, list_var("x")), VecType.into()),

        // `false1[type_of](bool) => bool`
        Red(app(path(False1, TypeOf), BoolType), BoolType.into()),
        // `not[type_of](bool) => bool`
        Red(app(path(Not, TypeOf), BoolType), BoolType.into()),
        // `idb[type_of](bool) => bool`
        Red(app(path(Idb, TypeOf), BoolType), BoolType.into()),
        // `true1[type_of](bool) => bool`
        Red(app(path(True1, TypeOf), BoolType), BoolType.into()),

        // `false2[type_of](bool)(bool) => bool`
        Red(app2(path(False2, TypeOf), BoolType, BoolType), BoolType.into()),
        // `true2[type_of](bool)(bool) => bool`
        Red(app2(path(True2, TypeOf), BoolType, BoolType), BoolType.into()),
        // `and[type_of](bool)(bool) => bool`
        Red(app2(path(And, TypeOf), BoolType, BoolType), BoolType.into()),
        // `or[type_of](bool)(bool) => bool`
        Red(app2(path(Or, TypeOf), BoolType, BoolType), BoolType.into()),
        // `eqb[type_of](bool)(bool) => bool`
        Red(app2(path(Eqb, TypeOf), BoolType, BoolType), BoolType.into()),
        // `xor[type_of](bool)(bool) => bool`
        Red(app2(path(Xor, TypeOf), BoolType, BoolType), BoolType.into()),
        // `nand[type_of](bool)(bool) => bool`
        Red(app2(path(Nand, TypeOf), BoolType, BoolType), BoolType.into()),
        // `nor[type_of](bool)(bool) => bool`
        Red(app2(path(Nor, TypeOf), BoolType, BoolType), BoolType.into()),
        // `exc[type_of](bool)(bool) => bool`
        Red(app2(path(Exc, TypeOf), BoolType, BoolType), BoolType.into()),
        // `imply[type_of](bool)(bool) => bool`
        Red(app2(path(Imply, TypeOf), BoolType, BoolType), BoolType.into()),
        // `fstb[type_of](bool)(bool) => bool`
        Red(app2(path(Fstb, TypeOf), BoolType, BoolType), BoolType.into()),
        // `sndb[type_of](bool)(bool) => bool`
        Red(app2(path(Sndb, TypeOf), BoolType, BoolType), BoolType.into()),

        // `sqrt[type_of](f64) => f64`
        Red(app(path(Sqrt, TypeOf), F64Type), F64Type.into()),
        // `ln[type_of](f64) => f64`
        Red(app(path(Ln, TypeOf), F64Type), F64Type.into()),
        // `log2[type_of](f64) => f64`
        Red(app(path(Log2, TypeOf), F64Type), F64Type.into()),
        // `log10[type_of](f64) => f64`
        Red(app(path(Log10, TypeOf), F64Type), F64Type.into()),
        // `exp[type_of](f64) => f64`
        Red(app(path(Exp, TypeOf), F64Type), F64Type.into()),

        // `eq[type_of](bool)(bool) => bool`
        Red(app2(path(Eq, TypeOf), BoolType, BoolType), BoolType.into()),
        // `add[type_of](f64)(f64) => f64`
        Red(app2(path(Add, TypeOf), F64Type, F64Type), F64Type.into()),
        // `sub[type_of](f64)(f64) => f64`
        Red(app2(path(Sub, TypeOf), F64Type, F64Type), F64Type.into()),
        // `mul[type_of](f64)(f64) => f64`
        Red(app2(path(Mul, TypeOf), F64Type, F64Type), F64Type.into()),
        // `div[type_of](f64)(f64) => f64`
        Red(app2(path(Div, TypeOf), F64Type, F64Type), F64Type.into()),
        // `rem[type_of](f64)(f64) => f64`
        Red(app2(path(Rem, TypeOf), F64Type, F64Type), F64Type.into()),
        // `pow[type_of](f64)(f64) => f64`
        Red(app2(path(Pow, TypeOf), F64Type, F64Type), F64Type.into()),
        // `rpow[type_of](f64)(f64) => f64`
        Red(app2(path(Rpow, TypeOf), F64Type, F64Type), F64Type.into()),

        // `len[type_of](vec) => f64`
        Red(app(path(Len, TypeOf), VecType), F64Type.into()),
        // `concat[type_of](vec)(vec) => vec`
        Red(app2(path(Concat, TypeOf), VecType, VecType), VecType.into()),

        // `not . not <=> idb`
        Red(comp(Not, Not), Idb.into()),
        // `not[not] <=> not`
        Red(path(Not, Not), Not.into()),
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
        // `not . (>= x) => (< x)`
        Red(comp(Not, app(Rge, "x")), app(Rlt, "x")),
        // `not . (> x) => (<= x)`
        Red(comp(Not, app(Rgt, "x")), app(Rle, "x")),
        // `not . (<= x) => (> x)`
        Red(comp(Not, app(Rle, "x")), app(Rgt, "x")),
        // `not . (< x) => (>= x)`
        Red(comp(Not, app(Rlt, "x")), app(Rge, "x")),

        // `add[even] => eqb`.
        Red(path(Add, Even), Eqb.into()),
        // `add[odd] => xor`.
        Red(path(Add, Odd), Xor.into()),
        // `add[sqrt] => sqrt . add . (rpow(2) . fst, rpow(2) . fst)`
        Red(path(Add, Sqrt),
            comp(Sqrt, comp(Add, (comp(app(Rpow, 2.0), Fst), comp(app(Rpow, 2.0), Snd))))),
        // `mul[even] => or`.
        Red(path(Mul, Even), Or.into()),
        // `mul[odd] => and`.
        Red(path(Mul, Odd), And.into()),
        // `not . even => odd`.
        Red(comp(Not, Even), Odd.into()),
        // `not . odd => even`
        Red(comp(Not, Odd), Even.into()),
        // `mul{(>= 0)}{(>= 0)}[rpow{(>= 0)}(_)] => mul`
        Red(path(constr(constr(Mul, app(Rge, 0.0)), app(Rge, 0.0)),
            app(constr(Rpow, app(Rge, 0.0)), Any)), Mul.into()),

        // `add[exp] => mul`
        Red(path(Add, Exp), Mul.into()),
        // `mul[ln] => add`
        Red(path(Mul, Ln), Add.into()),
        // `exp . ln => id`
        Red(comp(Exp, Ln), Id.into()),
        // `ln . exp => id`
        Red(comp(Ln, Exp), Id.into()),
        // `neg . neg => id`
        Red(comp(Neg, Neg), Id.into()),
        // `conj . conj => id`
        Red(comp(Conj, Conj), Id.into()),
        // `sqrt . sqnorm => norm`
        Red(comp(Sqrt, Sqnorm), Norm.into()),
        // `rpow(\2) . norm => sqnorm`
        Red(comp(app(Rpow, 2.0), Norm), Sqnorm.into()),
        // `sqrt . rpow(2) => abs`
        Red(comp(Sqrt, app(Rpow, 2.0)), Abs.into()),

        // `false1(_) => false`
        Red(app(False1, Any), false.into()),
        // `true1(_) => true`
        Red(app(True1, Any), true.into()),
        // `not(\false) => \true`
        Red(app(Not, false), true.into()),
        // `not(\true) => \false`
        Red(app(Not, true), false.into()),
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
        Red(app2(Fstb, "x", "y"), "x".into()),
        // `fst(x)(y) => x`
        Red(app2(Fst, "x", "y"), "x".into()),
        // `sndb(x)(y) => y`
        Red(app2(Sndb, "x", "y"), "y".into()),
        // `snd(x)(y) => y`
        Red(app2(Snd, "x", "y"), "y".into()),
        // `eqb(false) => not`
        Red(app(Eqb, false), Not.into()),
        // `eqb(true) => idb`
        Red(app(Eqb, true), Idb.into()),

        // `sin(mul(\x:int)(tau)) => sin(tau)`
        Red(app(Sin, app2(Mul, ret_int_var("x"), Tau)), app(Sin, Tau)),
        // `cos(mul(\x:int)(tau)) => cos(tau)`
        Red(app(Cos, app2(Mul, ret_int_var("x"), Tau)), app(Cos, Tau)),
        // `tan(mul(\x:int)(tau) => tan(tau))`
        Red(app(Tan, app2(Mul, ret_int_var("x"), Tau)), app(Tan, Tau)),
        // `pow(eps)(\2) => \0`
        Red(app2(Pow, Eps, 2.0), 0.0.into()),
        // `pow(imag)(\2) => \-1`
        Red(app2(Pow, Imag, 2.0), (-1.0).into()),
        // `lt(\x)(\y) => \x < \y`
        Red(app2(Lt, ret_var("x"), ret_var("y")), binop_ret_var("x", "y", Lt)),
        // `le(\x)(\y) => \x <= \y`
        Red(app2(Le, ret_var("x"), ret_var("y")), binop_ret_var("x", "y", Le)),
        // `gt(\x)(\y) => \x > \y`
        Red(app2(Gt, ret_var("x"), ret_var("y")), binop_ret_var("x", "y", Gt)),
        // `ge(\x)(\y) => \x >= \y`
        Red(app2(Ge, ret_var("x"), ret_var("y")), binop_ret_var("x", "y", Ge)),
        // `neg(\x) => -x`
        Red(app(Neg, ret_var("x")), unop_ret_var("x", Neg)),
        // `abs(\x) => compute::abs(x)`
        Red(app(Abs, ret_var("x")), unop_ret_var("x", Abs)),
        // `add(\x)(\y) => x + y`
        Red(app2(Add, ret_var("x"), ret_var("y")), binop_ret_var("x", "y", Add)),
        // `add(\x)(add(\y)(z)) => add(x + y)(z)`
        Red(app2(Add, ret_var("x"), app2(Add, ret_var("y"), "z")),
            app2(Add, binop_ret_var("x", "y", Add), "z")),
        // `sub(\x)(\y) => x - y`
        Red(app2(Sub, ret_var("x"), ret_var("y")), binop_ret_var("x", "y", Sub)),
        // `mul(\x)(\y) => x * y`
        Red(app2(Mul, ret_var("x"), ret_var("y")), binop_ret_var("x", "y", Mul)),
        // `mul(\x)(mul(\y)(z)) => mul(x * y)(z)`
        Red(app2(Mul, ret_var("x"), app2(Mul, ret_var("y"), "z")),
            app2(Mul, binop_ret_var("x", "y", Mul), "z")),
        // `div(\x)(\y) => x / y`
        Red(app2(Div, ret_var("x"), ret_var("y")), binop_ret_var("x", "y", Div)),
        // `rem(\x)(\y) => x % y`
        Red(app2(Rem, ret_var("x"), ret_var("y")), binop_ret_var("x", "y", Rem)),
        // `pow(\x)(\y) => x ^ y`
        Red(app2(Pow, ret_var("x"), ret_var("y")), binop_ret_var("x", "y", Pow)),
        // `rpow(\x)(\y) => x ^ y`
        Red(app2(Rpow, ret_var("x"), ret_var("y")), binop_ret_var("y", "x", Pow)),
        // `eq(\x)(\y) => x == y`
        Red(app2(Eq, ret_var("x"), ret_var("y")), binop_ret_var("x", "y", Eq)),
        // `push([x..], y) => compute::push(x, y)`
        Red(app2(Push, list_var("x"), "y"), binop_ret_var("x", "y", Push)),
        // `push_front([x..], y) => compute::push_front(x, y)`
        Red(app2(PushFront, list_var("x"), "y"), binop_ret_var("x", "y", PushFront)),
        // `concat{(: vec)}(x){(: vec)}(y) => x ++ y`
        Red(app(constr(app(constr(Concat, app(Rty, VecType)), "x"), app(Rty, VecType)),
                "y"), binop_ret_var("x", "y", Concat)),
        // `len(x) => compute::len(x)`
        Red(app(Len, "x"), unop_ret_var("x", Len)),
        // `sum{(: vec)}([x, y..]) => add(x)(sum{(: vec)}(y))`
        Red(app(constr(Sum, app(Rty, VecType)), head_tail_list("x", "y")),
            app2(Add, "x", app(constr(Sum, app(Rty, VecType)), "y"))),
        // `sum{(: vec)}([x]) => x`
        Red(app(constr(Sum, app(Rty, VecType)), singleton("x")), "x".into()),
        // `max{(: vec)}([x, y..]) => max2(x)(max{(: vec)}(y))`
        Red(app(constr(Max, app(Rty, VecType)), head_tail_list("x", "y")),
            app2(Max2, "x", app(constr(Max, app(Rty, VecType)), "y"))),
        // `max{(: vec)}([x]) => x`
        Red(app(constr(Max, app(Rty, VecType)), singleton("x")), "x".into()),
        // `min{(: vec)}([x, y..]) => min2(x)(min{(: vec)}(y))`
        Red(app(constr(Min, app(Rty, VecType)), head_tail_list("x", "y")),
            app2(Min2, "x", app(constr(Min, app(Rty, VecType)), "y"))),
        // `min{(: vec)}([x]) => x`
        Red(app(constr(Min, app(Rty, VecType)), singleton("x")), "x".into()),
        // `max2(\x)(\y) => compute::max2(x, y)`
        Red(app2(Max2, ret_var("x"), ret_var("y")), binop_ret_var("x", "y", Max2)),
        // `min2(\x)(\y) => compute::min2(x, y)`
        Red(app2(Min2, ret_var("x"), ret_var("y")), binop_ret_var("x", "y", Min2)),
        // `range(\x)(\y)(\z) => compute::range(x, y, z)`
        Red(app3(Range, ret_var("x"), ret_var("y"), ret_var("z")),
            ternop_ret_var("x", "y", "z", Range)),
        // `rangel(\x)(\y)(\z) => compute::rangel(x, y, z)`
        Red(app3(Rangel, ret_var("x"), ret_var("y"), ret_var("z")),
            ternop_ret_var("x", "y", "z", Rangel)),
        // `ranger(\x)(\y)(\z) => compute::ranger(x, y, z)`
        Red(app3(Ranger, ret_var("x"), ret_var("y"), ret_var("z")),
            ternop_ret_var("x", "y", "z", Ranger)),
        // `rangem(\x)(\y)(\z) => compute::rangem(x, y, z)`
        Red(app3(Rangem, ret_var("x"), ret_var("y"), ret_var("z")),
            ternop_ret_var("x", "y", "z", Rangem)),
        // `prob(\x) => compute::prob(x)`
        Red(app(Prob, ret_var("x")), unop_ret_var("x", Prob)),
        // `probl(\x) => compute::probl(x)`
        Red(app(Probl, ret_var("x")), unop_ret_var("x", Probl)),
        // `probr(\x) => compute::probr(x)`
        Red(app(Probr, ret_var("x")), unop_ret_var("x", Probr)),
        // `probm(\x) => compute::probm(x)`
        Red(app(Probm, ret_var("x")), unop_ret_var("x", Probm)),
        // `item(\x)([y..]) => y[x]`
        Red(app2(Item, ret_var("x"), list_var("y")), binop_ret_var("x", "y", Item)),
        // `el(x, y, z) => item(y, item(x, z))`
        Red(app3(El, "x", "y", "z"), app2(Item, "y", app2(Item, "x", "z"))),
        // `re(x) => item(0)(x)`
        Red(app(Re, "x"), app2(Item, 0.0, "x")),
        // `im(x) => item(1)(x)`
        Red(app(Im, "x"), app2(Item, 1.0, "x")),
        // `mulc([x0, y0], [x1, y1]) => [sub(mul(x0)(x1))(mul(y0)(y1)), add(mul(x0)(y1))(mul(x1)(y0))]`
        Red(app2(Mulc, vec2("x0", "y0"), vec2("x1", "y1")),
            vec2(app2(Sub, app2(Mul, "x0", "x1"), app2(Mul, "y0", "y1")),
                 app2(Add, app2(Mul, "x0", "y1"), app2(Mul, "x1", "y0")))),
        // `conj([x, y]) => [x, neg(y)]`
        Red(app(Conj, vec2("x", "y")), vec2("x", app(Neg, "y"))),
        // `sqnorm{(: vec)}(x) => sum(vec_op(mul)(x)(x))`
        Red(app(constr(Sqnorm, app(Rty, VecType)), "x"), app(Sum, app3(VecOp, Mul, "x", "x"))),
        // `norm(x) => sqrt(sqnorm(x))`
        Red(app(Norm, "x"), app(Sqrt, app(Sqnorm, "x"))),
        // `is_square_mat{(: vec)}(x) => compute::is_square_mat(x)`
        Red(app(constr(IsSquareMat, app(Rty, VecType)), "x"), unop_ret_var("x", IsSquareMat)),
        // `base(\x)(\y) => compute::base(x, y)`
        Red(app2(Base, ret_var("x"), ret_var("y")), binop_ret_var("x", "y", Base)),
        // `arity(x) => compute::arity(x)`
        Red(app(Arity, "x"), unop_ret_var("x", Arity)),

        // `mul[neg] => (neg . mul)`
        Red(path(Mul, Neg), comp(Neg, Mul)),

        // `add(0)(x) => x`
        Red(app2(Add, 0.0, "x"), "x".into()),
        // `add(x)(0) => x`
        Red(app2(Add, "x", 0.0), "x".into()),
        // `sub(0)(x) => neg(x)`
        Red(app2(Sub, 0.0, "x"), app(Neg, "x")),
        // `sub(x)(0) => x`
        Red(app2(Sub, "x", 0.0), "x".into()),
        // `mul(1)(x) => x`
        Red(app2(Mul, 1.0, "x"), "x".into()),
        // `mul(x)(1) => x`
        Red(app2(Mul, "x", 1.0), "x".into()),
        // `mul(0) => 0`
        Red(app(Mul, 0.0), 0.0.into()),
        // `mul(_)(0) => 0`
        Red(app2(Mul, Any, 0.0), 0.0.into()),
        // `pow(x)(1) => x`
        Red(app2(Pow, "x", 1.0), "x".into()),
        // `pow(x)(0) => 1`
        Red(app2(Pow, "x", 0.0), 1.0.into()),
        // `sin(tau) => 0`
        Red(app(Sin, Tau), 0.0.into()),
        // `cos(tau) => 1`
        Red(app(Cos, Tau), 1.0.into()),
        // `tan(tau) => 0`
        Red(app(Tan, Tau), 0.0.into()),

        // `add(x)(neg(y)) => sub(x)(y)`
        Red(app2(Add, "x", app(Neg, "y")), app2(Sub, "x", "y")),
        // `mul(x)(neg(y)) => neg(mul(x)(y))`
        Red(app2(Mul, "x", app(Neg, "y")), app(Neg, app2(Mul, "x", "y"))),

        // `f(x : \)(y : \) => f(x)(y) : \`
        concrete_op(Add),
        concrete_op(Sub),
        concrete_op(Mul),
        concrete_op(Div),
        concrete_op(Rem),
        concrete_op(Pow),
        concrete_op(Rpow),

        // Component-wise vector operations.
        vec_op(Add),
        vec_op(Sub),
        vec_op(Mul),
        vec_op(Div),
        vec_op(Rem),
        vec_op(Pow),
        vec_op(Rpow),

        // `vec_op(f)([x0, y0..])([x1, y1..]) => concat([f(x0)(x1)])(vec_op(f)(y0)(y1))`
        Red(app2(app(VecOp, "f"), head_tail_list("x0", "y0"), head_tail_list("x1", "y1")),
            app2(Concat, List(vec![app2("f", "x0", "x1")]), app2(app(VecOp, "f"), "y0", "y1"))),
        // `vec_op(f)([x])([y]) => [f(x)(y)]`
        Red(app2(app(VecOp, "f"), singleton("x"), singleton("y")), List(vec![app2("f", "x", "y")])),
        // `vec_uop(f)([x, y..]) => concat([f(x)])(vec_uop(f)(y))`
        Red(app2(VecUop, "f", head_tail_list("x", "y")), app2(Concat, List(vec![app("f", "x")]),
            app2(VecUop, "f", "y"))),
        // `vec_uop(f)([x]) => [f(x)]`
        Red(app2(VecUop, "f", singleton("x")), List(vec![app("f", "x")])),

        // `dot{(: vec)}([x0, y0]){(: vec)}([x1, y1]) => add(mul(x0)(x1))(mul(y0)(y1))`
        Red(app(constr(app(constr(Dot, app(Rty, VecType)), vec2("x0", "y0")), app(Rty, VecType)), vec2("x1", "y1")),
            app2(Add, app2(Mul, "x0", "x1"), app2(Mul, "y0", "y1"))),

        // `concat[len] => add`
        Red(path(Concat, Len), Add.into()),
        // `concat[sum] => add`
        Red(path(Concat, Sum), Add.into()),
        // `concat[min] => min2`
        Red(path(Concat, Min), Min2.into()),
        // `concat[max] => max2`
        Red(path(Concat, Max), Max2.into()),
        // `concat[sqnorm] => add`
        Red(path(Concat, Sqnorm), Add.into()),

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
        // `and . (le, ge) => eq`
        Red(comp(And, (Le, Ge)), Eq.into()),
        // `and . (f, f) => f`
        Red(comp(And, ("f", "f")), "f".into()),
        // `and . ((>= \x), (>= \y)) => (>= max2(x)(y))`
        Red(comp(And, (app(Rge, ret_var("x")), app(Rge, ret_var("y")))),
            app(Rge, app2(Max2, "x", "y"))),
        // `and . ((> \x), (> \y)) => (> max2(x)(y))`
        Red(comp(And, (app(Rgt, ret_var("x")), app(Rgt, ret_var("y")))),
            app(Rgt, app2(Max2, "x", "y"))),
        // `and . ((<= \x), (<= \y)) => (<= min2(x)(y))`
        Red(comp(And, (app(Rle, ret_var("x")), app(Rle, ret_var("y")))),
            app(Rle, app2(Min2, "x", "y"))),
        // `and . ((< \x), (< \y)) => (< min2(x)(y))`
        Red(comp(And, (app(Rlt, ret_var("x")), app(Rlt, ret_var("y")))),
            app(Rlt, app2(Min2, "x", "y"))),
        // `and . ((< x), (<= x)) => (< x)`
        Red(comp(And, (app(Rlt, "x"), app(Rle, "x"))), app(Rlt, "x")),
        // `and . ((<= x), (< y)) => and . ((< y), (<= x))`
        Red(comp(And, (app(Rle, "x"), app(Rlt, "y"))), comp(And, (app(Rlt, "y"), app(Rle, "x")))),
        // `and . ((< x), (> x)) => \false`
        Red(comp(And, (app(Rlt, "x"), app(Rgt, "x"))), false.into()),
        // `and . ((> x), (< y)) => and . ((< y), (> x))`
        Red(comp(And, (app(Rgt, "x"), app(Rlt, "y"))), comp(And, (app(Rlt, "y"), app(Rgt, "x")))),
        // `and . ((> x), (<= y)) => and . ((<= y), (> x))`
        Red(comp(And, (app(Rgt, "x"), app(Rle, "y"))), comp(And, (app(Rle, "y"), app(Rgt, "x")))),
        // `and . ((<= x), (>= x)) => eq(x)`
        Red(comp(And, (app(Rle, "x"), app(Rge, "x"))), app(Eq, "x")),
        // `and . ((> x), (>= x)) => (> x)`
        Red(comp(And, (app(Rgt, "x"), app(Rge, "x"))), app(Rgt, "x")),
        // `and . ((>= x), (> y)) => and . ((> y), (>= x))`
        Red(comp(And, (app(Rge, "x"), app(Rgt, "y"))), comp(And, (app(Rgt, "y"), app(Rge, "x")))),
        // `and . ((>= x), (< y)) => and . ((< y), (>= x))`
        Red(comp(And, (app(Rge, "x"), app(Rlt, "y"))), comp(And, (app(Rlt, "y"), app(Rge, "x")))),
        // `and . ((>= x), (<= y)) => and . ((<= y), (>= x))`
        Red(comp(And, (app(Rge, "x"), app(Rle, "y"))), comp(And, (app(Rle, "y"), app(Rge, "x")))),
        // `and . ((< \x), (> \y)) => if(\false, rangem(min2(x)(y), max2(x)(y)))(le(x)(y))`
        Red(comp(And, (app(Rlt, ret_var("x")), app(Rgt, ret_var("y")))),
            app(_if(false, app2(Rangem, app2(Min2, "x", "y"), app2(Max2, "x", "y"))),
                app2(Le, "x", "y"))),
        // `and . ((< \x), (>= \y)) => if(\false, rangel(min2(x)(y), max2(x)(y)))(le(x)(y))`
        Red(comp(And, (app(Rlt, ret_var("x")), app(Rge, ret_var("y")))),
            app(_if(false, app2(Rangel, app2(Min2, "x", "y"), app2(Max2, "x", "y"))),
                app2(Le, "x", "y"))),
        // `and . ((<= \x), (> \y)) => if(\false, ranger(min2(x)(y), max2(x)(y)))(le(x)(y))`
        Red(comp(And, (app(Rle, ret_var("x")), app(Rgt, ret_var("y")))),
            app(_if(false, app2(Ranger, app2(Min2, "x", "y"), app2(Max2, "x", "y"))),
                app2(Le, "x", "y"))),
        // `and . ((<= \x), (>= \y)) => if(\false, range(min2(x)(y), max2(x)(y)))(lt(x)(y))`
        Red(comp(And, (app(Rle, ret_var("x")), app(Rge, ret_var("y")))),
            app(_if(false, app2(Range, app2(Min2, "x", "y"), app2(Max2, "x", "y"))),
                app2(Lt, "x", "y"))),
        // `and . ((< \x), (<= \y)) => if((< x), (<= y))(le(x)(y))`
        Red(comp(And, (app(Rlt, ret_var("x")), app(Rle, ret_var("y")))),
            app(_if(app(Rlt, "x"), app(Rle, "y")), app2(Le, "x", "y"))),
        // `and . ((> \x), (>= \y)) => if((> x), (>= y))(ge(x)(y))`
        Red(comp(And, (app(Rgt, ret_var("x")), app(Rge, ret_var("y")))),
            app(_if(app(Rgt, "x"), app(Rge, "y")), app2(Ge, "x", "y"))),
        // `or . ((< x), (<= x)) => (<= x)`
        Red(comp(Or, (app(Rlt, "x"), app(Rle, "x"))), app(Rle, "x")),
        // `or . ((<= x), (< y)) => or . ((< y), (<= x))`
        Red(comp(Or, (app(Rle, "x"), app(Rlt, "y"))), comp(Or, (app(Rlt, "y"), app(Rle, "x")))),
        // `or . ((< x), eq(x)) => (<= x)`
        Red(comp(Or, (app(Rlt, "x"), app(Eq, "x"))), app(Rle, "x")),
        // `or . (eq(x), (> x)) => (>= x)`
        Red(comp(Or, (app(Eq, "x"), app(Rgt, "x"))), app(Rge, "x")),
        // `or . ((< x), (>= x)) => \true`
        Red(comp(Or, (app(Rlt, "x"), app(Rge, "x"))), true.into()),
        // `or . ((<= x), (> x)) => \true`
        Red(comp(Or, (app(Rle, "x"), app(Rgt, "x"))), true.into()),
        // `or . ((<= x), (>= x)) => \true`
        Red(comp(Or, (app(Rle, "x"), app(Rge, "x"))), true.into()),
        // `or . ((>= x), (< y)) => or . ((< y), (>= x))`
        Red(comp(Or, (app(Rge, "x"), app(Rlt, "y"))), comp(Or, (app(Rlt, "y"), app(Rge, "x")))),
        // `or . ((> x), (<= y)) => or . ((<= y), (> x))`
        Red(comp(Or, (app(Rgt, "x"), app(Rle, "y"))), comp(Or, (app(Rle, "y"), app(Rgt, "x")))),
        // `or . ((>= x), (<= y)) => or . ((<= y), (>= x))`
        Red(comp(Or, (app(Rge, "x"), app(Rle, "y"))), comp(Or, (app(Rle, "y"), app(Rge, "x")))),
        // `or . (eq(y), (< x)) => or . ((< x), eq(y))`
        Red(comp(Or, (app(Eq, "y"), app(Rlt, "x"))), comp(Or, (app(Rlt, "x"), app(Eq, "y")))),
        // `or . ((> x), eq(y)) => or . (eq(y), (> x))`
        Red(comp(Or, (app(Rgt, "x"), app(Eq, "y"))), comp(Or, (app(Eq, "y"), app(Rgt, "x")))),
        // `or . (eq(x), (>= x)) => (>= x)`
        Red(comp(Or, (app(Eq, "x"), app(Rge, "x"))), app(Rge, "x")),
        // `or . ((<= x), eq(x)) => (<= x)`
        Red(comp(Or, (app(Rle, "x"), app(Eq, "x"))), app(Rle, "x")),
        // `or . ((>= x), eq(y)) => or . (eq(y), (>= x))`
        Red(comp(Or, (app(Rge, "x"), app(Eq, "y"))), comp(Or, (app(Eq, "y"), app(Rge, "x")))),
        // `or . (eq(x), (<= y)) => or . ((<= y), eq(x))`
        Red(comp(Or, (app(Eq, "x"), app(Rle, "y"))), comp(Or, (app(Rle, "y"), app(Eq, "x")))),
        // `or . ((> x), (>= x)) => (>= x)`
        Red(comp(Or, (app(Rgt, "x"), app(Rge, "x"))), app(Rge, "x")),
        // `or . ((>= x), (> y)) => or . ((> y), (>= x))`
        Red(comp(Or, (app(Rge, "x"), app(Rgt, "y"))), comp(Or, (app(Rgt, "y"), app(Rge, "x")))),
        // `or . ((< \x), (<= \y)) => if((<= y), (< x))(le(x)(y))`
        Red(comp(Or, (app(Rlt, ret_var("x")), app(Rle, ret_var("y")))),
            app(_if(app(Rle, "y"), app(Rlt, "x")), app2(Le, "x", "y"))),
        // `or . ((> \x), (>= \y)) => if((>= y), (> x))(ge(x)(y))`
        Red(comp(Or, (app(Rgt, ret_var("x")), app(Rge, ret_var("y")))),
            app(_if(app(Rge, "y"), app(Gt, "x")), app2(Ge, "x", "y"))),
        // `or . (f, f) => f`
        Red(comp(Or, ("f", "f")), "f".into()),

        // `d(!\x)(x) => 1`
        Red(app2(D, not_ret_var("x"), "x"), 1.0.into()),
        // `d(!\x)(\y) => 0`
        Red(app2(D, not_ret_var("x"), ret_var("y")), 0.0.into()),
        // `d(!\x)(mul(\k)(y)) => mul(k)(d(x)(y))`
        Red(app2(D, not_ret_var("x"), app2(Mul, ret_var("k"), "y")), app2(Mul, "k", app2(D, "x", "y"))),
        // `d(!\x)(mul(pi)(y)) => mul(pi)(d(x)(y))`
        Red(app2(D, not_ret_var("x"), app2(Mul, Pi, "y")), app2(Mul, Pi, app2(D, "x", "y"))),
        // `d(!\x)(mul(tau)(y)) => mul(tau)(d(x)(y))`
        Red(app2(D, not_ret_var("x"), app2(Mul, Tau, "y")), app2(Mul, Tau, app2(D, "x", "y"))),
        // `d(!\x)(pow(x)(\k)) => mul(k)(pow(x)(sub(k)(1)))`
        Red(app2(D, not_ret_var("x"), app2(Pow, "x", ret_var("k"))),
            app2(Mul, "k", app2(Pow, "x", app2(Sub, "k", 1.0)))),
        // `d(!\x)(sin(x)) => cos(x)`
        Red(app2(D, not_ret_var("x"), app(Sin, "x")), app(Cos, "x")),
        // `d(!\x)(cos(x)) => neg(sin(x))`
        Red(app2(D, not_ret_var("x"), app(Cos, "x")), app(Neg, app(Sin, "x"))),
        // `d(!\x)(sin(mul(\k)(x))) => mul(k)(cos(mul(k)(x)))`
        Red(app2(D, not_ret_var("x"), app(Sin, app2(Mul, ret_var("k"), "x"))),
            app2(Mul, "k", app(Cos, app2(Mul, "k", "x")))),
        // `d(!\x)(cos(mul(\k)(x))) => mul(neg(k))(sin(mul(k)(x)))`
        Red(app2(D, not_ret_var("x"), app(Cos, app2(Mul, ret_var("k"), "x"))),
            app2(Mul, app(Neg, "k"), app(Sin, app2(Mul, "k", "x")))),

        // `and{eq} => fstb`
        Red(constr(And, Eq), Fstb.into()),
        // `or{eq} => fstb`
        Red(constr(Or, Eq), Fstb.into()),
        // `eq{eq} => \true`
        Red(constr(Eq, Eq), true.into()),
        // `sub{eq} => \0`
        Red(constr(Sub, Eq), 0.0.into()),
        // `add{eq}(x, _) => mul(2)(x)`
        Red(app2(constr(Add, Eq), "x", Any), app2(Mul, 2.0, "x")),
        // `mul{eq}(x, _) => pow(x)(2)`
        Red(app2(constr(Mul, Eq), "x", Any), app2(Pow, "x", 2.0)),
        // `\x{eq}(_) => \x`
        Red(app(constr(ret_var("x"), Eq), Any), "x".into()),
        // `f{true2} => f`
        Red(constr("f", True2), "f".into()),
        // `f{true1} => f`
        Red(constr("f", True1), "f".into()),

        // `∃(false1) => not`
        Red(app(Ex, False1), Not.into()),
        // `∃(not) => true1`
        Red(app(Ex, Not), True1.into()),
        // `∃(idb) => true1`
        Red(app(Ex, Idb), True1.into()),
        // `∃(true1) => idb`
        Red(app(Ex, True1), Idb.into()),
        // `∃(and) => true1`
        Red(app(Ex, And), True1.into()),
        // `∃(or) => true1`
        Red(app(Ex, Or), True1.into()),
        // `∃(nand) => true1`
        Red(app(Ex, Nand), True1.into()),
        // `∃(nor) => true1`
        Red(app(Ex, Nor), True1.into()),
        // `∃(xor) => true1`
        Red(app(Ex, Xor), True1.into()),
        // `∃(eqb) => true1`
        Red(app(Ex, Eqb), True1.into()),
        // `∃(exc) => true1`
        Red(app(Ex, Exc), True1.into()),
        // `∃(imply) => true1`
        Red(app(Ex, Imply), True1.into()),
        // `∃(fstb) => true1`
        Red(app(Ex, Fstb), True1.into()),
        // `∃(sndb) => true1`
        Red(app(Ex, Sndb), True1.into()),
        // `∃(id) => \true`
        Red(app(Ex, Id), true.into()),

        // `∃(add{(>= x)}{(>= y)}) => (>= add(x)(y))`
        Red(app(Ex, constr(constr(Add, app(Rge, "x")), app(Rge, "y"))),
            app(Rge, app2(Add, "x", "y"))),
        // `∃(add{(> x)}{(> y)}) => (> add(x)(y))`
        Red(app(Ex, constr(constr(Add, app(Rgt, "x")), app(Rgt, "y"))),
            app(Rgt, app2(Add, "x", "y"))),
        // `∃(add{(<= x)}{(<= y)}) => (<= add(x)(y))`
        Red(app(Ex, constr(constr(Add, app(Rle, "x")), app(Rle, "y"))),
            app(Rle, app2(Add, "x", "y"))),
        // `∃(add{(< x)}{(< y)}) => (< add(x)(y))`
        Red(app(Ex, constr(constr(Add, app(Rlt, "x")), app(Rlt, "y"))),
            app(Rlt, app2(Add, "x", "y"))),

        // `idb => id`
        Red(Idb.into(), Id.into()),
        // `fstb => fst`
        Red(Fstb.into(), Fst.into()),
        // `sndb => snd`
        Red(Sndb.into(), Snd.into()),
        // `eqb => eq`
        Red(Eqb.into(), Eq.into()),

        // `len . concat => concat[len] . (len . fst, len . snd)`
        Red(comp(Len, Concat), comp(path(Concat, Len), (comp(Len, Fst), comp(Len, Snd)))),
        // `sum . concat => concat[sum] . (sum . fst, sum . snd)`
        Red(comp(Sum, Concat), comp(path(Concat, Sum), (comp(Sum, Fst), comp(Sum, Snd)))),
        // `max . concat => concat[max] . (max . fst, max . snd)`
        Red(comp(Max, Concat), comp(path(Concat, Max), (comp(Max, Fst), comp(Max, Snd)))),
        // `min . concat => concat[min] . (min . fst, min . snd)`
        Red(comp(Min, Concat), comp(path(Concat, Min), (comp(Min, Fst), comp(Min, Snd)))),
        // `sqnorm . concat => concat[sqnorm] . (sqnorm . fst, sqnorm . snd)`
        Red(comp(Sqnorm, Concat),
            comp(path(Concat, Sqnorm), (comp(Sqnorm, Fst), comp(Sqnorm, Snd)))),
        // `norm . concat => sqrt . (sqnorm . concat)`
        Red(comp(Norm, Concat), comp(Sqrt, comp(Sqnorm, Concat))),
        // `len . base(x) => x`
        Red(comp(Len, app(Base, "x")), "x".into()),
        // `(f . fst){x}(a){_}(_) => f{x}(a)`
        Red(app(constr(app(constr(comp("f", Fst), "x"), "a"), Any), Any),
            app(constr("f", "x"), "a")),
        // `(f . fst)(a)(_) => f(a)`
        Red(app2(comp("f", Fst), "a", Any), app("f", "a")),
        // `(f . snd){_}(_){x}(a) => f{x}(a)`
        Red(app(constr(app(constr(comp("f", Snd), Any), Any), "x"), "a"),
            app(constr("f", "x"), "a")),
        // `(f . snd)(_)(a) => f(a)`
        Red(app2(comp("f", Snd), Any, "a"), app("f", "a")),
        // `(f . fst){_}(a)(_) => f(a)`
        Red(app2(constr(comp("f", Fst), Any), "a", Any), app("f", "a")),
        // `(f . snd){_}(_)(a) => f(a)`
        Red(app2(constr(comp("f", Snd), Any), Any, "a"), app("f", "a")),
        // `(f . fst) . (x, _) <=> f . x`
        Red(comp(comp("f", Fst), ("x", Any)), comp("f", "x")),
        // `(f . snd) . (_, x) <=> f . x`
        Red(comp(comp("f", Snd), (Any, "x")), comp("f", "x")),

        // `(x, y) . (a, b) => (x . (a, b), y . (a, b))`.
        Red(comp(("x", "y"), ("a", "b")), (comp("x", ("a", "b")), comp("y", ("a", "b"))).into()),
        // `(x, y, z) . (a, b, c) => (x . a, y . b, z . c)`.
        Red(comp(("x", "y", "z"), ("a", "b", "c")),
            (comp("x", "a"), comp("y", "b"), comp("z", "c")).into()),
        // `h . f[g -> id] => f[g -> h]`.
        Red(comp("h", path("f", ("g", Id))), path("f", ("g", "h"))),
        // `h . f[g0 x g1 -> id] => f[g0 x g1 -> h]`.
        Red(comp("h", path("f", ("g0", "g1", Id))), path("f", ("g0", "g1", "h"))),

        // `add(pow(cos(x))(\2))(pow(sin(x))(\2)) <=> 1`
        Red(app2(Add, app2(Pow, app(Cos, "x"), 2.0),
                      app2(Pow, app(Sin, "x"), 2.0)), 1.0.into()),

        // `f:!{}([x..]) => f{(: vec)}(x)`
        Red(app(no_constr("f"), list_var("x")), app(constr("f", app(Rty, VecType)), "x")),

        // `add(!\a)(\b) => add(b)(a)`
        Red(app2(Add, not_ret_var("a"), ret_var("b")), app2(Add, "b", "a")),
        // `add(!\a)(add(\b)(c)) => add(b)(add(a)(c))`
        Red(app2(Add, not_ret_var("a"), app2(Add, ret_var("b"), "c")),
            app2(Add, "b", app2(Add, "a", "c"))),
        // `mul(!\a)(\b) => mul(b)(a)`
        Red(app2(Mul, not_ret_var("a"), ret_var("b")), app2(Mul, "b", "a")),

        // `sqrt(\x) <=> compute::sqrt(x)`
        Eqv(app(Sqrt, ret_var("x")), unop_ret_var("x", Sqrt)),
        // `ln(\x) <=> compute::ln(x)`
        Eqv(app(Ln, ret_var("x")), unop_ret_var("x", Ln)),
        // `log2(\x) <=> compute::log2(x)`
        Eqv(app(Log2, ret_var("x")), unop_ret_var("x", Log2)),
        // `log10(\x) <=> compute::log10(x)`
        Eqv(app(Log10, ret_var("x")), unop_ret_var("x", Log10)),
        // `exp(\x) <=> compute::exp(x)`
        Eqv(app(Exp, ret_var("x")), unop_ret_var("x", Exp)),
        // `sin(\x) <=> compute::sin(x)`
        Eqv(app(Sin, ret_var("x")), unop_ret_var("x", Sin)),
        // `asin(\x) <=> compute::asin(x)`
        Eqv(app(Asin, ret_var("x")), unop_ret_var("x", Asin)),
        // `cos(\x) <=> compute::cos(x)`
        Eqv(app(Cos, ret_var("x")), unop_ret_var("x", Cos)),
        // `acos(\x) <=> compute::acos(x)`
        Eqv(app(Acos, ret_var("x")), unop_ret_var("x", Acos)),
        // `tan(\x) <=> compute::tan(x)`
        Eqv(app(Tan, ret_var("x")), unop_ret_var("x", Tan)),
        // `atan(\x) <=> compute::atan(x)`
        Eqv(app(Atan, ret_var("x")), unop_ret_var("x", Atan)),
        // `atan2(\x)(\y) <=> compute::atan2(x, y)`
        Eqv(app2(Atan2, ret_var("x"), ret_var("y")), binop_ret_var("x", "y", Atan2)),
        // `mul(\2, pi) <=> tau`
        Eqv(app2(Mul, 2.0, Pi), Tau.into()),
        // `pi <=> \3.141592653589793`
        Eqv(Pi.into(), 3.141592653589793.into()),
        // `tau <=> \6.283185307179586`
        Eqv(Tau.into(), 6.283185307179586.into()),

        // `pow(x)(\2) <=> mul(x)(x)`
        Eqv(app2(Pow, "x", 2.0), app2(Mul, "x", "x")),

        // `not . nand <=> and`.
        Eqv(comp(Not, Nand), And.into()),
        // `not . nor <=> or`.
        Eqv(comp(Not, Nor), Or.into()),
        // `not . and <=> nand`.
        Eqv(comp(Not, And), Nand.into()),
        // `not . or <=> nor`.
        Eqv(comp(Not, Or), Nor.into()),
        // `not . eqb <=> xor`.
        Eqv(comp(Not, Eqb), Xor.into()),
        // `not . xor <=> eqb`.
        Eqv(comp(Not, Xor), Eqb.into()),
        // `(>= x) <=> le(x)`
        Eqv(app(Rge, "x"), app(Le, "x")),
        // `(> x) <=> lt(x)`
        Eqv(app(Rgt, "x"), app(Lt, "x")),
        // `(<= x) <=> ge(x)`
        Eqv(app(Rle, "x"), app(Ge, "x")),
        // `(< x) <=> gt(x)`
        Eqv(app(Rlt, "x"), app(Gt, "x")),

        // `range(0)(1) <=> prob`
        Eqv(app2(Range, 0.0, 1.0), Prob.into()),
        // `rangel(0)(1) <=> probl`
        Eqv(app2(Rangel, 0.0, 1.0), Probl.into()),
        // `ranger(0)(1) <=> probr`
        Eqv(app2(Ranger, 0.0, 1.0), Probr.into()),
        // `rangem(0)(1) <=> probm`
        Eqv(app2(Rangem, 0.0, 1.0), Probm.into()),

        // `el(x)(y) <=> item(x) . item(y)`
        Eqv(app2(El, "x", "y"), comp(app(Item, "x"), app(Item, "y"))),

        // `and(a)(b) <=> and(b)(a)`
        commutative(And),
        // `or(a)(b) <=> or(b)(a)`
        commutative(Or),
        // `nand(a)(b) <=> nand(b)(a)`
        commutative(Nand),
        // `nor(a)(b) <=> nor(b)(a)`
        commutative(Nor),
        // `xor(a)(b) <=> xor(b)(a)`
        commutative(Xor),
        // `eq(a)(b) <=> eq(b)(a)`
        commutative(Eq),
        // `add(a)(b) <=> add(b)(a)`
        commutative(Add),
        // `mul(a)(b) <=> mul(b)(a)`
        commutative(Mul),
        // `add(a)(add(b)(c)) <=> add(add(a)(b))(c)`
        associative(Add),
        // `mul(a)(mul(b)(c)) <=> mul(mul(a)(b))(c)`
        associative(Mul),
        // `mul(a)(add(b)(c)) <=> add(mul(a)(b))(mul(a)(c))`
        distributive(Mul, Add),

        // `((a + b)^2) <=> (a^2 + 2 * a * b + b^2)`
        Eqv(app2(Pow, app2(Add, "a", "b"), 2.0), app2(Add, app2(Add, app2(Pow, "a", 2.0),
            app2(Mul, app2(Mul, 2.0, "a"), "b")), app2(Pow, "b", 2.0))),
        // `((a * b)^2) <=> (a^2 * b^2)`
        Eqv(app2(Pow, app2(Mul, "a", "b"), 2.0), app2(Mul, app2(Pow, "a", 2.0), app2(Pow, "b", 2.0))),
        // `(^ a)(b) <=> (a ^ b)`
        Eqv(app2(Rpow, "a", "b"), app2(Pow, "b", "a")),

        // `f:!{}(a)(a) <=> f{eq}(a)(a)`
        Eqv(app2(no_constr("f"), "a", "a"), app2(constr("f", Eq), "a", "a")),
        // `f[g][h] <=> f[h . g]`.
        Eqv(path(path("f", "g"), "h"), path("f", comp("h", "g"))),
        // `f . (g . (h0, h1)) <=> (f . g) . (h0, h1)`
        Eqv(comp("f", comp("g", ("h0", "h1"))), comp(comp("f", "g"), ("h0", "h1"))),
        // `(f . (g0, g1)) . (h0, h1) <=> f . ((g0, g1) . (h0, h1))`
        Eqv(comp(comp("f", ("g0", "g1")), ("h0", "h1")),
            comp("f", comp(("g0", "g1"), ("h0", "h1")))),
        // `f . (g . h) <=> (f . g) . h`.
        Eqv(comp("f", comp("g", "h")), comp(comp("f", "g"), "h")),
        // `f:[arity]1[g] <=> f:[arity]1[g -> id][id -> g]`
        Eqv(path(arity_var("f", 1), "g"), path(path(arity_var("f", 1), ("g", Id)), (Id, "g"))),
        // `(f . (g0, g1)){x}(a){y}(b) <=> f(g0{x}(a){y}(b))(g1{x}(a){y}(b))`
        Eqv(app(constr(app(constr(comp("f", ("g0", "g1")), "x"), "a"), "y"), "b"),
            app2("f", app(constr(app(constr("g0", "x"), "a"), "y"), "b"),
                      app(constr(app(constr("g1", "x"), "a"), "y"), "b"))),
        // `(f . (g0, g1))(a)(b) <=> f(g0(a)(b))(g1(a)(b))`
        Eqv(app2(comp("f", ("g0", "g1")), "a", "b"),
            app2("f", app2("g0", "a", "b"), app2("g1", "a", "b"))),
        // `(f . (g0, g1))(a) <=> f(g0(a))(g1(a))`
        Eqv(app(comp("f", ("g0", "g1")), "a"), app2("f", app("g0", "a"), app("g1", "a"))),
        // `(f . (g0(a), g1(b)))(c) <=> (f . (g0 . fst, g1 . snd))(a)(b)(c)`
        Eqv(app(comp("f", (app("g0", "a"), app("g1", "b"))), "c"),
            app3(comp("f", (comp("g0", Fst), comp("g1", Snd))), "a", "b", "c")),
        // `(f . g)(a)(b) <=> f(g(a)(b))`
        Eqv(app2(comp("f", "g"), "a", "b"), app("f", app2("g", "a", "b"))),
        // `(f . g){x}(a){y}(b) <=> f(g{x}(a){y}(b))`
        Eqv(app(constr(app(constr(comp("f", "g"), "x"), "a"), "y"), "b"),
            app("f", app(constr(app(constr("g", "x"), "a"), "y"), "b"))),
        // `(f . g)(a) <=> f(g(a))`
        Eqv(app(comp("f", "g"), "a"), app("f", app("g", "a"))),
        // `(f . g){x}(a){y}(b) <=> (f . g{x}{y})(a)(b)`
        Eqv(app(constr(app(constr(comp("f", "g"), "x"), "a"), "y"), "b"),
            app2(comp("f", constr(constr("g", "x"), "y")), "a", "b")),
        // `(f . g:[arity]1){x}(a) <=> f(g{x}(a))`
        Eqv(app(constr(comp("f", arity_var("g", 1)), "x"), "a"), app("f", app(constr("g", "x"), "a"))),
        // `(g . f:[arity]2){_}(a){_}(b) <=> f:[arity]2[g](g(a))(g(b))`
        Eqv(app(constr(app(constr(comp("g", arity_var("f", 2)), Any), "a"), Any), "b"),
            app(app(path(arity_var("f", 2), "g"), app("g", "a")), app("g", "b"))),
        // `(g . f:[arity]1){_}(a) <=> f:[arity]1[g](g(a))`
        Eqv(app(constr(comp("g", arity_var("f", 1)), Any), "a"),
            app(path(arity_var("f", 1), "g"), app("g", "a"))),
        // `(g . f:[arity]2)(a)(b) <=> f:[arity]2[g](g(a))(g(b))`
        Eqv(app(app(comp("g", arity_var("f", 2)), "a"), "b"),
            app2(path(arity_var("f", 2), "g"), app("g", "a"), app("g", "b"))),
        // `g . f:[arity]2 <=> f:[arity]2[g] . (g . fst, g . snd)`
        Eqv(comp("g", arity_var("f", 2)),
            comp(path(arity_var("f", 2), "g"), (comp("g", Fst), comp("g", Snd)))),
        // `(g . f:[arity]1)(a) <=> f:[arity]1[g](g(a))`
        Eqv(app(comp("g", arity_var("f", 1)), "a"), app(path(arity_var("f", 1), "g"), app("g", "a"))),
        // `(g, f)(a) <=> (g(a), f(a))`
        Eqv(app(("g", "f"), "a"), (app("g", "a"), app("f", "a")).into()),
        // `f . (g0, g1)(a) <=> (f . (g0, g1))(a)`
        Eqv(comp("f", app(("g0", "g1"), "a")), app(comp("f", ("g0", "g1")), "a")),
        // `(g . f){h} <=> g . f{h}`
        Eqv(constr(comp("g", "f"), "h"), comp("g", constr("f", "h"))),
        // `f[g0 x g1 -> g2] . (g0 . fst, g1 . snd) <=> g2 . f`
        Eqv(comp(path("f", ("g0", "g1", "g2")), (comp("g0", Fst), comp("g1", Snd))),
            comp("g2", "f")),
        // `f[g0 -> g1] . g0 <=> g1 . f`
        Eqv(comp(path("f", ("g0", "g1")), "g0"), comp("g1", "f")),
        // `f[id x g0 -> g1] . (fst, g0 . snd) <=> g1 . f`
        Eqv(comp(path("f", (Id, "g0", "g1")), (Fst, comp("g0", Snd))), comp("g1", "f")),
        // `f[g0 x id -> g1] . (g0 . fst, snd) <=> g1 . f`
        Eqv(comp(path("f", ("g0", Id, "g1")), (comp("g0", Fst), Snd)), comp("g1", "f")),
    ]
}
