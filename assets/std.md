# Poi Standard Library

The Poi knowledge format is compatible with markdown text files:

- Must start with `#` (markdown title)
- A code block must use 3 backticks and `poi`
- Rules are seperated by `;`.

### Definitions

A definition uses the syntax `<sym> := <expr>`.

Definitions can be inlined under theorem proving
in Poi Reduce with `inline all`.
Under evaluation, definitions are always inlined.
See `help` for more information.

```poi
false1 := false;
not := if(false)(true);
idb := if(true)(false);
true1 := true;
and := if(true)(if(true)(false));
or := if(true)(if(true)(false));
eqb := if(if(true)(false))(if(false)(true));
xor := if(if(false)(true))(if(true)(false));
nand := if(if(false)(true))(true);
not := if(false)(if(false)(true));
exc := if(if(false)(true))(false);
imply := if(if(true)(false))(true);
fstb := if(true)(false);
sndb := if(if(true)(false))(if(true)(false));
```

### Reductions

A reduction uses the syntax `<pat> => <expr>`.

The pattern binds variables on the left side and synthesizes the expression on the right side.

There is a trade-off between reductions and equivalences.
Reductions are used to simplify automated theorem proving.

#### Misc

```poi
x((y, z..)) => x(y)(z);
x{(y, z..)} => x{y}{z};
x{y}{z}(a)(b) => x{y}(a){z}(b);
(g, f)((y, z..)) => (g(y)(z), f(y)(z));
if(x)(_)(true) => x;
if(_)(x)(false) => x;
if(x)(_){_}(true) => x;
if(_)(x){_}(false) => x;
\x(_) => x;
\x . _ => x;
∃(\x) => eq(x);
∃(f{f}) => idb;
∀(f:[arity]2{g0}{g1}) => (g0, g1);
∀(f:[arity]1{g}) => g;
∀(f:!{}) => true;
```

#### Quaterions

Quaternions are lifted to a type vector,
in order to avoid combinatorial explosion in rules.

```poi
imag2 => [0, 0, 1, 0] : quat;
imag3 => [0, 0, 0, 1] : quat;
(imag * (x : quat)) => ([0, 1, 0, 0] * x) : quat;
((x : quat) * imag) => (x * [0, 1, 0, 0]) : quat;
((x * imag) * (y : quat)) => (x * (imag * (y : quat)));

neg([x, y, z, w] : quat) => [neg(x), neg(y), neg(z), neg(w)] : quat;
((x : quat) * imag) => ((x : quat) * (imag : quat));
(imag + (x : quat)) => ([0, 1, 0, 0] + x) : quat;
((x : quat) + imag) => (x + [0, 1, 0, 0]) : quat;
((x : quat) * imag2) => (x * [0, 0, 1, 0]) : quat;
((x : quat) * imag3) => (x * [0, 0, 0, 1]) : quat;
s + ([x, y, z, w] : quat) => [s + x, s + y, s + z, s + w] : quat;
s * ([x, y, z, w] : quat) => [s * x, s * y, s * z, s * w] : quat;
([x, y, z, w] : quat) * s => [x * s, y * s, z * s, w * s] : quat;
((x : quat) + (y * imag)) => (x + [0, y, 0, 0]) : quat;
(x * imag + (y : quat)) => ([0, x, 0, 0] + y) : quat;
((x : quat) * (y : quat)) => (x * y) : quat;
((x : quat) + (y : quat)) => (x + y) : quat;
x + (y : quat) => (x + y) : quat;
[x, y, 𝐢, z] : quat => 𝐢 * 𝐢₂ + ([x, y, 0, z] : quat);
[x, y, z, 𝐢] : quat => 𝐢 * 𝐢₃ + ([x, y, z, 0] : quat);
```

Quaternion algebra:

```poi
([x0, y0, z0, w0] + [x1, y1, z1, w1]) : quat =>
 [x0+x1,y0+y1,z0+z1,w0+w1] : quat;
([x0, y0, z0, w0] * [x1, y1, z1, w1]) : quat => [
    x0*x1-y0*y1-z0*z1-w0*w1,
    x0*y1+y0*x1+z0*w1-w0*z1,
    x0*z1+z0*x1-y0*w1+w0*y1,
    x0*w1+w0*x1+y0*z1-z0*y1,
] : quat;
```

#### Types

```poi
type_of(true) => bool;
type_of(false) => bool;
type_of(\x) => compute::type_of(x);
type_of([x..]) => vec;

false1[type_of](bool) => bool;
not[type_of](bool) => bool;
idb[type_of](bool) => bool;
true1[type_of](bool) => bool;

false2[type_of](bool)(bool) => bool;
true2[type_of](bool)(bool) => bool;
and[type_of](bool)(bool) => bool;
or[type_of](bool)(bool) => bool;
eqb[type_of](bool)(bool) => bool;
xor[type_of](bool)(bool) => bool;
nand[type_of](bool)(bool) => bool;
nor[type_of](bool)(bool) => bool;
exc[type_of](bool)(bool) => bool;
imply[type_of](bool)(bool) => bool;
fstb[type_of](bool)(bool) => bool;
sndb[type_of](bool)(bool) => bool;

sqrt[type_of](f64) => f64;
ln[type_of](f64) => f64;
log2[type_of](f64) => f64;
log10[type_of](f64) => f64;
exp[type_of](f64) => f64;

eq[type_of](bool)(bool) => bool;
add[type_of](f64)(f64) => f64;
sub[type_of](f64)(f64) => f64;
mul[type_of](f64)(f64) => f64;
div[type_of](f64)(f64) => f64;
rem[type_of](f64)(f64) => f64;
pow[type_of](f64)(f64) => f64;
rpow[type_of](f64)(f64) => f64;

len[type_of](vec) => f64;
concat[type_of](vec)(vec) => vec;
```

#### Symmetric normal paths

```poi
add[even] => eqb;
add[exp] => mul;
add[neg] => add;
add[odd] => xor;
and[not] => or;
concat[len] => add;
concat[max] => max2;
concat[min] => min2;
concat[sqnorm] => add;
concat[sum] => add;
eqb[not] => xor;
mul[even] => or;
mul[ln] => add;
mul[log10] => add;
mul[log2] => add;
mul[neg] => neg · mul;
mul[odd] => and;
mul_mat[det] => mul;
nand[not] => nor;
nor[not] => nand;
not[not] => not;
or[not] => and;
xor[not] => eqb;
```

#### Asymmetric normal paths

```poi
add[sqrt] => sqrt · (add · ((^ 2) · fst, (^ 2) · snd));
nand[not x not -> id] => and[not];
mul_mat[len ⨯ (item(1) · dim) → dim] => id;
if(a)(b)[not → id] => if(b)(a);
```

#### Identity normal paths

```poi
x[id] => x;
id[x] => id;
```

#### Misc

```poi
inv(f) . f => id;
f . inv(f) => id;
inv(inv(f)) => f;
not . not => idb;
x . id => x;
id . x => x;
(fst, snd) => id;

not . even => odd;
not . odd => even;
mul{(>= 0)}{(>= 0)}[rpow{(>= 0)}(_)] => mul;

exp . ln => id;
ln . exp => id;
neg . neg => id;
conj . conj => id;
sqrt . sqnorm => norm;
(^ 2) · norm => sqnorm;
sqrt · (^ 2) => abs;
transpose . transpose => id;

false1(_) => false;
true1(_) => true;
not(\false) => true;
not(\true) => false;
id(x) => x;
and(true) => idb;
and(false) => false1;
or(true) => true1;
or(false) => idb;
fstb(x)(y) => x;
fst(x)(y) => x;
sndb(x)(y) => y;
snd(x)(y) => y;
eqb(false) => not;
eqb(true) => idb;
```

#### Complex numbers

```poi
ε ^ 2 => 0;
𝐢 ^ 2 => -1;
```

Complex number utilities:
```poi
ε * ε => ε ^ 2;

𝐢 * 𝐢 => 𝐢 ^ 2;
𝐢 + 𝐢 => 2𝐢;
x * 𝐢 + 𝐢 => (x + 1) * 𝐢;
𝐢 + x * 𝐢 => (1 + x) * 𝐢;
sqrt(-1) => 𝐢;
```

#### Misc
```poi
sin(\x:int * τ) => sin(τ);
cos(\x:int * τ) => cos(τ);
tan(\x:int * τ) => tan(τ);
-(\a + \b * x) => (-a) + (-b) * x;
reci((\x + \y * imag)) => x / (x^2 + y^2) + (neg(y) / (x^2 + y^2)) * imag;
\a - \b * x => a + (-b) * x;
(\a + \b * x) - (\c + \d * x) => (a - c) + (b - d) * x;
(\a + \b * x) + (\c * x) => a + (b + c) * x;
(\a * x) + (\b * x) => (a + b) * x;
\a * x + x => (a + 1) * x;
\a * x - x => (a - 1) * x;
\a * (\b + \c * x) => (a * \b) + (a * c) * x;
((\a + \b * x) * (\c * x)) => ((c * x) * (a + b * x));
(\a * x) * (\b + \c * x) => ((a * c) * x^2 + (a * b) * x);
(\a + \b * x) * (\c + \d * x) => a * c + b * d * x^2 + (a * d + b * c) * x;
(\a * x) * (\b * x) => (a * b) * x^2;
\x / \y => compute::div(x, y);
(\a + \b * ε) / (\c + \d * ε) => a / c + (b * c - a * d) / c ^ 2 * ε;
x / (\a + \b * 𝐢) => x * reci(a + b * 𝐢);
not{(: vec)}([x]) => [!x];
not{(: vec)}([x, y..]) => [not(x)] ++ not{(: vec)}(y);
neg{(: vec)}(\[x]) => [-x];
neg{(: vec)}([x, y..]) => [neg(x)] ++ neg{(: vec)}(y);
sum{(: vec)}([x, y..]) => add(x)(sum{(: vec)}(y));
sum{(: vec)}(\[x]) => x;
max{(: vec)}([x, y..]) => max2(x)(max{(: vec)}(y));
max{(: vec)}(\[x]) => x;
min{(: vec)}([x, y..]) => min2(x)(min{(: vec)}(y));
min{(: vec)}(\[x]) => x;
el(x)(y)(z) => item(y)(item(x)(z));
re{(: vec)}(x) => item(0)(x);
re(a + _ * 𝐢) => a;
im{(: vec)}(x) => item(1)(x);
im(_ + a * 𝐢) => a;
a * 𝐢 * 𝐢 => a * (𝐢 * 𝐢);
mulc([x0, y0])([x1, y1]) => [x0 * x1 - y0 * y1, x0 * y1 + x1 * y0];
conj([x, y]) => [x, -y];
conj(a + b * 𝐢) => a + (-b) * 𝐢;
```

#### Computations

```poi
-\x => compute::neg(x);
\x < \y => compute::lt(x, y);
\x <= \y => compute::le(x, y);
\x = \y => compute::eq(x, y);
\x >= \y => compute::ge(x, y);
\x > \y => compute::gt(x, y);
\x + \y => compute::add(x, y);
\x - \y => compute::sub(x, y);
\x * \y => compute::mul(x, y);
\x % \y => compute::rem(x, y);
\x ^ \y => compute::pow(x, y);
(^ \x)(\y) => compute::pow(y, x);
abs(\x) => compute::abs(x);
arity(x) => compute::arity(x);
base(\x)(\y) => compute::base(x, y);
col(\k){(: vec)}(x) => compute::col(k, x);
concat{(: vec)}(x){(: vec)}(y) => compute::concat(x, y);
dim{(: vec)}(x) => compute::dim(x);
even(\x) => compute::even(x);
inc(\x) => compute::inc(x);
item(\x)([y..]) => compute::item(x, y);
is_square_mat{(: vec)}(x) => compute::is_square_mat(x);
len{(: vec)}(x) => compute::len(x);
max2(\x)(\y) => compute::max2(x, y);
min2(\x)(\y) => compute::min2(x, y);
mul_mat{(: vec)}(x){(: vec)}(y) => compute::mul_mat(x, y);
norm(x) => sqrt(sqnorm(x));
odd(\x) => compute::odd(x);
prob(\x) => compute::prob(x);
probl(\x) => compute::probl(x);
probm(\x) => compute::probm(x);
probr(\x) => compute::probr(x);
push([x..])(y) => compute::push(x, y);
push_front([x..])(y) => compute::push_front(x, y);
range(\x)(\y)(\z) => compute::range(x, y, z);
rangel(\x)(\y)(\z) => compute::rangel(x, y, z);
rangem(\x)(\y)(\z) => compute::rangem(x, y, z);
ranger(\x)(\y)(\z) => compute::ranger(x, y, z);
reci(\x) => compute::reci(x);
sqnorm{(: vec)}(x) => sum(vec_op(mul)(x)(x));
transpose{(: vec)}(x) => compute::transpose(x);
```

Computation utilities:
```poi
\x + (\y + z) => compute::add(x, y) + z;
\x * (\y * z) => compute::mul(x, y) * z;
```

#### Misc

```poi
(* x) · (mul · (g, (* y) · snd)) => (* x) · ((* y) · (mul · (g, snd)));
(* x) · (mul · ((* y) · fst, g)) => (* x) · ((* y) · (mul · (fst, g)));
(* x) · (* y) => (* x * y);

-(-x) => x;
0 + x => x;
x + 0 => x;
0 - x => -x;
x - 0 => x;
1 * x => x;
x * 1 => x;
(* 0) => 0;
_ * 0 => 0;
\x / ∞ => 0;
x ^ 1 => x;
x ^ 0 => 1;

x * (-y) => (-x) * y;
```

#### Concreteness

Concreteness is used to in meta-reasoning about whether an expression
will return a concrete value.

```poi
(x : \) + (y : \) => (x + y) : \;
(x : \) - (y : \) => (x - y) : \;
(x : \) * (y : \) => (x * y) : \;
(x : \) / (y : \) => (x / y) : \;
(x : \) % (y : \) => (x % y) : \;
(x : \) ^ (y : \) => (x ^ y) : \;
(^ x : \)(y : \) => (^ x)(y) : \;
```

#### Vector operations
```poi
and{(: vec)}(x){(: vec)}(y) => vec_op(and)(x)(y);
or{(: vec)}(x){(: vec)}(y) => vec_op(or)(x)(y);
add{(: vec)}(x){(: vec)}(y) => vec_op(add)(x)(y);
sub{(: vec)}(x){(: vec)}(y) => vec_op(sub)(x)(y);
mul{(: vec)}(x){(: vec)}(y) => vec_op(mul)(x)(y);
div{(: vec)}(x){(: vec)}(y) => vec_op(div)(x)(y);
rem{(: vec)}(x){(: vec)}(y) => vec_op(rem)(x)(y);
pow{(: vec)}(x){(: vec)}(y) => vec_op(pow)(x)(y);
rpow{(: vec)}(x){(: vec)}(y) => vec_op(rpow)(x)(y);
```

```poi
vec_op(f)([x0, y0..])([x1, y1..]) => concat([f(x0)(x1)])(vec_op(f)(y0)(y1));
vec_op(f)(\[x])(\[y]) => [f(x)(y)];
vec_uop(f)([x, y..]) => concat([f(x)])(vec_uop(f)(y));
vec_uop(f)(\[x]) => [f(x)];
```

#### Misc
```poi
dot{(: vec)}([x0, y0]){(: vec)}([x1, y1]) => x0 * x1 + y0 * y1;
not · (not · x) => x;
```

#### Ranges

```poi
not . (< x) => (>= x);
not . (<= x) => (> x);
not . (>= x) => (< x);
not . (> x) => (<= x);
```

```poi
and · (le, ge) => eq;
and · (f, f) => f;
and · ((>= \x), (>= \y)) => (>= max2(x)(y));
and · ((> \x), (> \y)) => (> max2(x)(y));
and · ((<= \x), (<= \y)) => (<= min2(x)(y));
and · ((< \x), (< \y)) => (< min2(x)(y));
and · ((< x), (<= x)) => (< x);
and · ((<= x), (< y)) => and · ((< y), (<= x));
and · ((< x), (> x)) => false;
and · ((> x), (< y)) => and · ((< y), (> x));
and · ((> x), (<= y)) => and · ((<= y), (> x));
and · ((<= x), (>= x)) => (= x);
and · ((> x), (>= x)) => (> x);
and · ((>= x), (> y)) => and · ((> y), (>= x));
and · ((>= x), (< y)) => and · ((< y), (>= x));
and · ((>= x), (<= y)) => and · ((<= y), (>= x));
and · ((< \x), (> \y)) => if(false)(rangem(min2(x)(y))(max2(x)(y)))(x <= y);
and · ((< \x), (>= \y)) => if(false)(rangel(min2(x)(y))(max2(x)(y)))(x <= y);
and · ((<= \x), (> \y)) => if(false)(ranger(min2(x)(y))(max2(x)(y)))(x <= y);
and · ((<= \x), (>= \y)) => if(false)(range(min2(x)(y))(max2(x)(y)))(x < y);
and · ((< \x), (<= \y)) => if((< x))((<= y))(x <= y);
and · ((> \x), (>= \y)) => if((> x))((>= y))(x >= y);
```

```poi
or · ((< x), (<= x)) => (<= x);
or · ((<= x), (< y)) => or · ((< y), (<= x));
or · ((< x), (= x)) => (<= x);
or · ((= x), (> x)) => (>= x);
or · ((< x), (>= x)) => true;
or · ((<= x), (> x)) => true;
or · ((<= x), (>= x)) => true;
or · ((>= x), (< y)) => or · ((< y), (>= x));
or · ((> x), (<= y)) => or · ((<= y), (> x));
or · ((>= x), (<= y)) => or · ((<= y), (>= x));
or · ((= y), (< x)) => or · ((< x), (= y));
or · ((> x), (= y)) => or · ((= y), (> x));
or · ((= x), (>= x)) => (>= x);
or · ((<= x), (= x)) => (<= x);
or · ((>= x), (= y)) => or · ((= y), (>= x));
or · ((= x), (<= y)) => or · ((<= y), (= x));
or · ((> x), (>= x)) => (>= x);
or · ((>= x), (> y)) => or · ((> y), (>= x));
or · ((< \x), (<= \y)) => if((<= y))((< x))(x <= y);
or · ((> \x), (>= \y)) => if((>= y))(gt(x))(x >= y);
or · (f, f) => f;
```

#### Derivatives
```poi
d(!\x)(x) => 1;
d(!\x)(\y) => 0;
d(!\x)(\k * y) => k * d(x)(y);
d(!\x)(π * y) => π * d(x)(y);
d(!\x)(τ * y) => τ * d(x)(y);
d(!\x)(x ^ \k) => k * x ^ (k - 1);
d(!\x)(sin(x)) => cos(x);
d(!\x)(cos(x)) => -sin(x);
d(!\x)(sin(\k * x)) => k * cos(k * x);
d(!\x)(cos(\k * x)) => -k * sin(k * x);
d(!\x)(exp(x)) => exp(x);
d(!\x)(exp(\k * x)) => k * exp(k * x);
```

#### Indefinite integrals

```poi
∫(!\x)(c)(x) => c + 0.5 * x ^ 2;
∫(!\x)(c)(\k) => c + k * x;
∫(!\x)(c)(\k * y) => k * ∫(x)(c / k)(y);
∫(!\x)(c)(x ^ \k) => c + 1 / (k + 1) * x ^ (k + 1);
∫(!\x)(c)(cos(x)) => c + sin(x);
∫(!\x)(c)(sin(x)) => c + -cos(x);
∫(!\x)(c)(exp(x)) => c + exp(x);
∫(!\x)(c)(exp(\k * x)) => c + 1 / k * exp(k * x);
∫(!\x)(c)(d(x)(y) * exp(y)) => c + exp(y);
∫(!\x)(c)(\k ^ x) => c + k ^ x / ln(k);
∫(!\x)(c)(ln(x)) => c + (-x + x * ln(x));
```

Indefinite integral utilities:
```poi
(\k * ((c / \k) + y)) => c + k * y;
```

#### Equality domain constraints

```poi
and{eq} => fstb;
or{eq} => fstb;
eq{eq} => true;
add{eq}(x)(_) => 2 * x;
mul{eq}(x)(_) => x ^ 2;
sub{eq} => 0;
```

Equality constraint utilities:
```poi
\x{eq}(_) => x;
eq{(: vec)}(x){(: vec)}(x) => eq{eq}(x)(x);
```

#### Misc

```poi
div{and . (eq, (> 0) . fst)} => 1;
f{true2} => f;
f{true1} => f;
(x^\k * x) => x^(k + 1);
(x * x^\k) => x^(k + 1);
(x^\a * x^\b) => x^(a + b);
(x * x) => x^2;
```

#### Existential paths (codomains)
```poi
∃(false1) => not;
∃(not) => true1;
∃(idb) => true1;
∃(true1) => idb;
∃(and) => true1;
∃(or) => true1;
∃(nand) => true1;
∃(nor) => true1;
∃(xor) => true1;
∃(eqb) => true1;
∃(exc) => true1;
∃(imply) => true1;
∃(fstb) => true1;
∃(sndb) => true1;
∃(id) => true;

∃(add{(>= x)}{(>= y)}) => (>= x + y);
∃(add{(> x)}{(> y)}) => (> x + y);
∃(add{(<= x)}{(<= y)}) => (<= x + y);
∃(add{(< x)}{(< y)}) => (< x + y);
```

#### Misc
```poi
idb => id;
fstb => fst;
sndb => snd;
eqb => eq;

len . concat => concat[len] . (len . fst, len . snd);
sum . concat => concat[sum] . (sum . fst, sum . snd);
max . concat => concat[max] . (max . fst, max . snd);
min . concat => concat[min] . (min . fst, min . snd);
sqnorm . concat => concat[sqnorm] . (sqnorm . fst, sqnorm . snd);
norm . concat => sqrt . (sqnorm . concat);
len . base(x) => x;
item(0) . dim => len;
(f . fst){x}(a){_}(_) => f{x}(a);
(f . fst)(a)(_) => f(a);
(f . snd){_}(_){x}(a) => f{x}(a);
(f . snd)(_)(a) => f(a);
(f . fst){_}(a)(_) => f(a);
(f . snd){_}(_)(a) => f(a);
(f . fst) . (x, _) => f . x;
(f . snd) . (_, x) => f . x;

(x, y) . (a, b) => (x . (a, b), y . (a, b));
(x, y, z) . (a, b, c) => (x . (a, b, c), y . (a, b, c), z . (a, b, c));

cos(x) ^ 2 + sin(x) ^ 2 => 1;

f:!{}([x..]) => f{(: vec)}(x);

(-(x + y)) => (-x + -y);
(-(x * y)) => (-x * y);
!\a + \b => b + a;
!\a + (\b + c) => b + (a + c);
\a + !\b - !\c => a + (b - c);
!\a * \b => b * a;
(x + x) => (2 * x);
```

### Equivalences

Equivalences are used to present available choices after reduction.

An equivalence uses the syntax `<expr> <=> <expr>`.
When `<=>>` is used, it means reduction from left to right under evaluation.

Equivalences are similar to reductions, but with the difference
that they might work both ways.
Some equivalences have fewer variables or uses `compute::` on one side,
which means they can only be used from left to right.

#### Trigonometry

```poi
sqrt(\x:(>= 0)) <=> compute::sqrt(x);
sqrt(\x:(< 0)) <=>> mul(sqrt(x))(imag);
ln(\x) <=>> compute::ln(x);
log2(\x) <=>> compute::log2(x);
log10(\x) <=>> compute::log10(x);
exp(\x) <=>> compute::exp(x);
sin(\x) <=>> compute::sin(x);
asin(\x) <=>> compute::asin(x);
cos(\x) <=>> compute::cos(x);
acos(\x) <=>> compute::acos(x);
tan(\x) <=>> compute::tan(x);
atan(\x) <=>> compute::atan(x);
atan2(\x)(\y) <=>> compute::atan2(x, y);
```

Constants:
```poi
pi <=>> 3.141592653589793;
tau <=>> 6.283185307179586;
```

Trigonometry utilities:
```poi
2π <=> τ;
cos(τ) => 1;
sin(τ) => 0;
sqrt(1) => 1;
sqrt(x) ^ 2 => x;
tan(τ) => 0;
```

#### Ranges to probabilities

```poi
range(0)(1) <=> prob;
rangel(0)(1) <=> probl;
ranger(0)(1) <=> probr;
rangem(0)(1) <=> probm;
```

#### Misc

```poi
x ^ 2 <=> x * x;

not . nand <=> and;
not . nor <=> or;
not . and <=> nand;
not . or <=> nor;
not . eqb <=> xor;
not . xor <=> eqb;
(>= x) <=> le(x);
(> x) <=> lt(x);
(<= x) <=> ge(x);
(< x) <=> gt(x);
and . (f, g) <=> and . (g, f);
or . (f, g) <=> or . (g, f);
nand . (f, g) <=> nand . (g, f);
nor . (f, g) <=> nor . (g, f);
(not . and) . (not . fst, not . snd) <=> or;

el(x)(y) <=> item(x) . item(y);

a & b <=> b & a;
a | b <=> b | a;
nand(a)(b) <=> nand(b)(a);
nor(a)(b) <=> nor(b)(a);
xor(a)(b) <=> xor(b)(a);
(a = b) <=> (b = a);
a + b <=> b + a;
a * b <=> b * a;
a + (b + c) <=> a + b + c;
a - (b - c) <=> a - b + c;
a - b - c <=> a - (b + c);
a * (b * c) <=> a * b * c;
a * (b + c) <=> a * b + a * c;
a * (b - c) <=> a * b - a * c;
((a - b) * c) <=> (a * c - b * c);
((a + b) * c) <=> (a * c + b * c);
((a + b) - c) <=> (a + (b - c));

((a + b)^2) <=> (a^2 + 2 * a * b + b^2);
((a - b)^2) <=> (a^2 - 2 * a * b + b^2);
((a + b) * (a - b)) <=> (a^2 - b^2);
((a * b)^2) <=> (a^2 * b^2);
(^ a)(b) <=> (a ^ b);
```

#### Function inverses

```poi
inv(id) <=> id;
inv(not) <=> not;
```

#### Algebra misc

```poi
inc(x) <=> 1 + x;
(x + -y) <=> (x - y);
neg(x + y) <=> neg(x) - y;
neg(x) <=> -1 * x;
(a + b = c) <=> ((-a + a) + b = -a + c);
(a - b = c) <=> (a - (b - b) = c + b);
(a + b = c) <=> (b = c - a);
(a + b = c) <=> (a = c - b);
(a + b = c + b) <=> (a = c);
mul(-1) <=> neg;
(a - b = c - b) <=> (a = c);
(a / b = c / b) <=> (a * (b / b) = c * (b / b));
(a / c + b / c) <=> ((a + b) / c);
((a * b) / c) <=> (a * (b / c));
(a * b - a) <=> (a * (b - 1));
(- y)(x) <=> (x - y);
(x / y) <=> x * reci(y);
(/ y)(x) <=> (x / y);
```

#### Logarithms and exponentials

```poi
log10(x) <=> ln(x) / ln(10);
log2(x) <=> ln(x) / ln(2);
ln(y ^ x) <=> x * ln(y);
log2(y ^ x) <=> x * log2(y);
log10(y ^ x) <=> x * log10(y);
ln(x * y) <=> ln(x) + ln(y);
log10(x * y) <=> log10(x) + log10(y);
log2(x * y) <=> log2(x) + log2(y);
exp(x + y) <=> exp(x) * exp(y);
exp(x * ln(y)) <=> y^x;
```

#### Generic transformations
```poi
(f . g) <=> f[inv(g) -> id];
(f . (g0 . fst, g1 . snd)) <=> f[inv(g0) x inv(g1) -> id];
(f . inv(g)) <=> f[g -> id];
(f . (inv(g0) . fst, inv(g1) . snd)) <=> f[g0 x g1 -> id];
f[id -> g2] . inv(g1) <=> f[g1 -> g2];
f[id -> g2] . g1 <=> f[inv(g1) -> g2];
inv(f) <=> id[f -> id];
inv(f . g) <=> inv(g) . inv(f);
id[(f . g) -> id] <=> id[f -> id[g -> id]];
((g2 . f . g1) = h) <=> (f = (inv(g2) . h . inv(g1)));
((f . g) = h) <=> (((inv(f) . f) . g) = (inv(f) . h));
((f . g) = h) <=> ((f . (g . inv(g))) = (h . inv(g)));
(f[g] = h) <=> (f = h[inv(g)]);
(f[g1 -> g2] = h) <=> (f = h[inv(g1) -> inv(g2)]);
(f[g0 x g1 -> g2] = h) <=> (f = h[inv(g0) x inv(g1) -> inv(g2)]);
(f[g1 -> id] = h[id -> inv(g2)]) <=> (f[g1 -> g2] = h);
h . f[g -> id] <=> f[g -> h];
f[id -> g] <=> g . f;
f[id x id -> g] <=> g . f;
f:!{}(a)(a) <=> f{eq}(a)(a);
f:!{} . (g, g) <=> f{eq} . (g, g);
f[g][h] <=> f[h . g];
f[g0 -> g1][g2 -> g3] <=> f[(g2 . g0) -> (g3 . g1)];
f[g0 x g1 -> g2][h0 x h1 -> h2] <=> f[(h0 . g0) x (h1 . g1) -> (h2 . g2)];
f . (g . (h0, h1)) <=> (f . g) . (h0, h1);
(f . (g0, g1)) . (h0, h1) <=> f . ((g0, g1) . (h0, h1));
f . (g . h) <=> (f . g) . h;
f:[arity]1[g] <=> f:[arity]1[g -> id][id -> g];
(f . (g0, g1)){x}(a){y}(b) <=> f(g0{x}(a){y}(b))(g1{x}(a){y}(b));
(f . (g0, g1))(a)(b) <=> f(g0(a)(b))(g1(a)(b));
(f . (g0, g1))(a) <=> f(g0(a))(g1(a));
(f . (g0(a), g1(b)))(c) <=> (f . (g0 . fst, g1 . snd))(a)(b)(c);
(f . g)(a)(b) <=> f(g(a)(b));
(f . g){x}(a){y}(b) <=> f(g{x}(a){y}(b));
(f . g)(a) <=> f(g(a));
(f . g){x}(a){y}(b) <=> (f . g{x}{y})(a)(b);
(f . g:[arity]1){x}(a) <=> f(g{x}(a));
(g . f:[arity]2){_}(a){_}(b) <=> f:[arity]2[g](g(a))(g(b));
(g . f:[arity]1){_}(a) <=> f:[arity]1[g](g(a));
(g . f:[arity]2)(a)(b) <=> f:[arity]2[g](g(a))(g(b));
g . f:[arity]2 <=> f:[arity]2[g] . (g . fst, g . snd);
(g . f:[arity]1)(a) <=> f:[arity]1[g](g(a));
(g, f)(a) <=> (g(a), f(a));
f . (g0, g1)(a) <=> (f . (g0, g1))(a);
(g . f){h} <=> g . f{h};
f[g0 x g1 -> g2] . (g0 . fst, g1 . snd) <=> g2 . f;
f[g0 -> g1] . g0 <=> g1 . f;
f[id x g0 -> g1] . (fst, g0 . snd) <=> g1 . f;
f[g0 x id -> g1] . (g0 . fst, snd) <=> g1 . f;
f[g -> g] <=> f[g];
f[g x g -> g] <=> f[g];
(f(x) = g(x)) <=> (f = g);
g2 . f[g0 x g1 -> id] <=> (g2 . f)[g0 x g1 -> id];
h . f[g0 x g1 -> id] <=> f[g0 x g1 -> h];
```
