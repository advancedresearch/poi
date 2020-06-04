use super::*;

use piston_meta::{Convert, Range};

fn parse_expr(node: &str, mut convert: Convert, ignored: &mut Vec<Range>) -> Result<(Range, Expr), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut expr: Option<Expr> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_alg(convert, ignored) {
            convert.update(range);
            expr = Some(val);
        } else if let Ok((range, val)) = parse_seq(convert, ignored) {
            convert.update(range);
            expr = Some(val);
        } else if let Ok((range, val)) = parse_tup(convert, ignored) {
            convert.update(range);
            if let Tup(val) = &val {
                // Reduce tuple singleton.
                if val.len() == 1 {
                    expr = Some(val[0].clone());
                    continue;
                }
            }
            expr = Some(val);
        } else if let Ok((range, val)) = parse_list(convert, ignored) {
            convert.update(range);
            expr = Some(val);
        } else if let Ok((range, val)) = parse_rapp(convert, ignored) {
            convert.update(range);
            expr = Some(val);
        } else if let Ok((range, val)) = convert.meta_string("var") {
            convert.update(range);
            expr = Some(Sym(match &**val {
                "triv" | "∀" | "dom" => Triv,
                "ex" | "∃" | "codom" => Ex,
                "false1" => False1,
                "idb" => Idb,
                "not" => Not,
                "true1" => True1,
                "false2" => False2,
                "true2" => True2,
                "and" => And,
                "or" => Or,
                "eqb" => Eqb,
                "xor" => Xor,
                "nand" => Nand,
                "nor" => Nor,
                "exc" => Exc,
                "imply" => Imply,
                "fstb" => Fstb,
                "sndb" => Sndb,
                "neqb" => Xor,
                "id" => Id,
                "lt" => Lt,
                "rlt" => Rlt,
                "le" => Le,
                "rle" => Rle,
                "gt" => Gt,
                "rgt" => Rgt,
                "ge" => Ge,
                "rge" => Rge,
                "mul" => Mul,
                "mulc" => Mulc,
                "div" => Div,
                "rem" => Rem,
                "pow" => Pow,
                "rpow" => Rpow,
                "sqrt" => Sqrt,
                "even" => Even,
                "odd" => Odd,
                "abs" => Abs,
                "neg" => Neg,
                "reci" => Reci,
                "conj" => Conj,
                "norm" => Norm,
                "sqnorm" => Sqnorm,
                "add" => Add,
                "sub" => Sub,
                "len" => Len,
                "concat" => Concat,
                "sum" => Sum,
                "mul_mat" => MulMat,
                "det" => Det,
                "dim" => Dim,
                "is_square_mat" => IsSquareMat,
                "base" => Base,
                "fst" => Fst,
                "snd" => Snd,
                "ln" => Ln,
                "log2" => Log2,
                "log10" => Log10,
                "exp" => Exp,
                "min2" => Min2,
                "max2" => Max2,
                "min" => Min,
                "max" => Max,
                "range" => Range,
                "rangel" => Rangel,
                "ranger" => Ranger,
                "rangem" => Rangem,
                "prob" => Prob,
                "probl" => Probl,
                "probr" => Probr,
                "probm" => Probm,
                "eq" => Eq,
                "neq" => Neq,
                "if" => If,
                "sin" => Sin,
                "asin" => Asin,
                "cos" => Cos,
                "acos" => Acos,
                "tan" => Tan,
                "atan" => Atan,
                "atan2" => Atan2,
                "dot" => Dot,
                "item" => Item,
                "el" => El,
                "re" => Re,
                "im" => Im,
                "push" => Push,
                "push_front" => PushFront,
                "\\" => RetType,
                "vec" => VecType,
                "rty" => Rty,
                "vec_op" => VecOp,
                "vec_uop" => VecUop,
                "arity" => Arity,
                "d" => D,
                "integ" | "∫" => Integ,
                "pi" | "π" => Pi,
                "tau" | "τ" => Tau,
                "eps" | "ε" => Eps,
                "imag" | "𝐢" => Imag,
                "imag2" | "𝐢₂" => Imag2,
                "imag3" | "𝐢₃" => Imag3,
                "type_of" => TypeOf,
                "bool" => BoolType,
                "f64" => F64Type,
                "inf" | "∞" => Inf,
                _ => Var(val),
            }));
        } else if let Ok((range, val)) = convert.meta_bool("bool") {
            convert.update(range);
            expr = Some(val.into());
        } else if let Ok((range, val)) = convert.meta_f64("num") {
            convert.update(range);
            expr = Some(val.into());
        } else if let Ok((range, val)) = convert.meta_f64("num_pi") {
            convert.update(range);
            expr = Some(app2(Mul, val, Pi));
        } else if let Ok((range, val)) = convert.meta_f64("num_tau") {
            convert.update(range);
            expr = Some(app2(Mul, val, Tau));
        } else if let Ok((range, val)) = convert.meta_f64("num_eps") {
            convert.update(range);
            expr = Some(app2(Mul, val, Eps));
        } else if let Ok((range, val)) = convert.meta_f64("num_imag") {
            convert.update(range);
            expr = Some(app2(Mul, val, Imag));
        } else if let Ok((range, val)) = convert.meta_f64("num_imag2") {
            convert.update(range);
            expr = Some(app2(Mul, val, Imag2));
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let expr = expr.ok_or(())?;
    Ok((convert.subtract(start), expr))
}

fn parse_alg(mut convert: Convert, ignored: &mut Vec<Range>) -> Result<(Range, Expr), ()> {
    let start = convert;
    let node = "alg";
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut op: Option<Symbol> = None;
    let mut left: Option<Expr> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_expr("alg_item", convert, ignored) {
            convert.update(range);
            if let (Some(expr), Some(op)) = (left, op.clone()) {
                left = Some(app2(op, expr, val));
            } else {
                left = Some(val);
            }
        } else if let Ok((range, val)) = parse_alg(convert, ignored) {
            convert.update(range);
            if let (Some(expr), Some(op)) = (left, op.clone()) {
                left = Some(app2(op, expr, val));
            } else {
                left = Some(val);
            }
        } else if let Ok((range, _)) = convert.meta_bool("+") {
            convert.update(range);
            op = Some(Add);
        } else if let Ok((range, _)) = convert.meta_bool("-") {
            convert.update(range);
            op = Some(Sub);
        } else if let Ok((range, _)) = convert.meta_bool("*") {
            convert.update(range);
            op = Some(Mul);
        } else if let Ok((range, _)) = convert.meta_bool("/") {
            convert.update(range);
            op = Some(Div);
        } else if let Ok((range, _)) = convert.meta_bool("%") {
            convert.update(range);
            op = Some(Rem);
        } else if let Ok((range, _)) = convert.meta_bool("^") {
            convert.update(range);
            op = Some(Pow);
        } else if let Ok((range, _)) = convert.meta_bool("&") {
            convert.update(range);
            op = Some(And);
        } else if let Ok((range, _)) = convert.meta_bool("|") {
            convert.update(range);
            op = Some(Or);
        } else if let Ok((range, _)) = convert.meta_bool("++") {
            convert.update(range);
            op = Some(Concat);
        } else if let Ok((range, _)) = convert.meta_bool("<") {
            convert.update(range);
            op = Some(Lt);
        } else if let Ok((range, _)) = convert.meta_bool("<=") {
            convert.update(range);
            op = Some(Le);
        } else if let Ok((range, _)) = convert.meta_bool("=") {
            convert.update(range);
            op = Some(Eq);
        } else if let Ok((range, _)) = convert.meta_bool(">=") {
            convert.update(range);
            op = Some(Ge);
        } else if let Ok((range, _)) = convert.meta_bool(">") {
            convert.update(range);
            op = Some(Gt);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let left = left.ok_or(())?;
    Ok((convert.subtract(start), left))
}

fn parse_tup(mut convert: Convert, ignored: &mut Vec<Range>) -> Result<(Range, Expr), ()> {
    let start = convert;
    let node = "tup";
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut items: Vec<Expr> = vec![];
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_expr("item", convert, ignored) {
            convert.update(range);
            items.push(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    Ok((convert.subtract(start), Tup(items)))
}

fn parse_list(mut convert: Convert, ignored: &mut Vec<Range>) -> Result<(Range, Expr), ()> {
    let start = convert;
    let node = "list";
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut items: Vec<Expr> = vec![];
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_expr("item", convert, ignored) {
            convert.update(range);
            items.push(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    Ok((convert.subtract(start), List(items)))
}

fn parse_rapp(mut convert: Convert, ignored: &mut Vec<Range>) -> Result<(Range, Expr), ()> {
    let start = convert;
    let node = "rapp";
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut sym: Option<Symbol> = None;
    let mut arg: Option<Expr> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, _)) = convert.meta_bool("rty") {
            convert.update(range);
            sym = Some(Rty);
        } else if let Ok((range, _)) = convert.meta_bool("rlt") {
            convert.update(range);
            sym = Some(Rlt);
        } else if let Ok((range, _)) = convert.meta_bool("rle") {
            convert.update(range);
            sym = Some(Rle);
        } else if let Ok((range, _)) = convert.meta_bool("eq") {
            convert.update(range);
            sym = Some(Eq);
        } else if let Ok((range, _)) = convert.meta_bool("rgt") {
            convert.update(range);
            sym = Some(Rgt);
        } else if let Ok((range, _)) = convert.meta_bool("rge") {
            convert.update(range);
            sym = Some(Rge);
        } else if let Ok((range, _)) = convert.meta_bool("mul") {
            convert.update(range);
            sym = Some(Mul);
        } else if let Ok((range, _)) = convert.meta_bool("rpow") {
            convert.update(range);
            sym = Some(Rpow);
        } else if let Ok((range, val)) = parse_expr("arg", convert, ignored) {
            convert.update(range);
            arg = Some(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let sym = sym.ok_or(())?;
    let arg = arg.ok_or(())?;
    Ok((convert.subtract(start), app(sym, arg)))
}

fn parse_seq(mut convert: Convert, ignored: &mut Vec<Range>) -> Result<(Range, Expr), ()> {
    let start = convert;
    let node = "seq";
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut op: Option<Op> = None;
    let mut left: Option<Expr> = None;
    let mut right: Option<Expr> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_expr("left", convert, ignored) {
            convert.update(range);
            left = Some(val);
        } else if let Ok((range, val)) = parse_rapp(convert, ignored) {
            convert.update(range);
            left = Some(val);
        } else if let Ok((range, val)) = parse_alg(convert, ignored) {
            convert.update(range);
            left = Some(val);
        } else if let Ok((range, val)) = parse_expr("path", convert, ignored) {
            convert.update(range);
            if let (Some(nleft), Some(nright), Some(nop)) = (&left, &right, op) {
                left = Some(Op(nop, Box::new(nleft.clone()), Box::new(nright.clone())));
            }
            right = Some(val);
            op = Some(Path);
        } else if let Ok((range, val)) = parse_expr("app", convert, ignored) {
            convert.update(range);
            if let (Some(nleft), Some(nright), Some(nop)) = (&left, &right, op) {
                left = Some(Op(nop, Box::new(nleft.clone()), Box::new(nright.clone())));
            }
            right = Some(val);
            op = Some(Apply);
        } else if let Ok((range, val)) = parse_expr("constr", convert, ignored) {
            convert.update(range);
            if let (Some(nleft), Some(nright), Some(nop)) = (&left, &right, op) {
                left = Some(Op(nop, Box::new(nleft.clone()), Box::new(nright.clone())));
            }
            right = Some(val);
            op = Some(Constrain);
        } else if let Ok((range, val)) = parse_expr("comp", convert, ignored) {
            convert.update(range);
            if let (Some(nleft), Some(nright), Some(nop)) = (&left, &right, op) {
                left = Some(Op(nop, Box::new(nleft.clone()), Box::new(nright.clone())));
            }
            right = Some(val);
            op = Some(Compose);
        } else if let Ok((range, val)) = parse_expr("typ", convert, ignored) {
            convert.update(range);
            if let (Some(nleft), Some(nright), Some(nop)) = (&left, &right, op) {
                left = Some(Op(nop, Box::new(nleft.clone()), Box::new(nright.clone())));
            }
            right = Some(val);
            op = Some(Type);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let op = op.ok_or(())?;
    let left = left.ok_or(())?;
    let right = right.ok_or(())?;
    Ok((convert.subtract(start), Op(op, Box::new(left), Box::new(right))))
}

/// Parses a string.
pub fn parse_str(data: &str) -> Result<Expr, String> {
    use piston_meta::{parse_errstr, syntax_errstr};

    let syntax_src = include_str!("../assets/syntax.txt");
    let syntax = syntax_errstr(syntax_src)?;

    let mut meta_data = vec![];
    parse_errstr(&syntax, &data, &mut meta_data)?;

    // piston_meta::json::print(&meta_data);

    let convert = Convert::new(&meta_data);
    let mut ignored = vec![];
    match parse_expr("expr", convert, &mut ignored) {
        Err(()) => Err("Could not convert meta data".into()),
        Ok((_, expr)) => Ok(expr),
    }
}

/// Parses a source file.
pub fn parse(source: &str) -> Result<Expr, String> {
    use std::fs::File;
    use std::io::Read;

    let mut data_file = File::open(source).map_err(|err|
        format!("Could not open `{}`, {}", source, err))?;
    let mut data = String::new();
    data_file.read_to_string(&mut data).unwrap();

    parse_str(&data)
}
