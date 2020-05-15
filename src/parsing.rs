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
        } else if let Ok((range, val)) = convert.meta_string("var") {
            convert.update(range);
            expr = Some(Sym(match &**val {
                "and" => And,
                "or" => Or,
                "not" => Not,
                "eqb" => Eqb,
                "xor" => Xor,
                "idb" => Idb,
                "nand" => Nand,
                "nor" => Nor,
                "fstb" => Fstb,
                "sndb" => Sndb,
                "neqb" => Xor,
                "id" => Id,
                "mul" => Mul,
                "div" => Div,
                "rem" => Rem,
                "pow" => Pow,
                "sqrt" => Sqrt,
                "even" => Even,
                "odd" => Odd,
                "neg" => Neg,
                "add" => Add,
                "sub" => Sub,
                "len" => Len,
                "concat" => Concat,
                "sum" => Sum,
                "mul_mat" => MulMat,
                "det" => Det,
                "dim" => Dim,
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
                "eq" => Eq,
                "if" => If,
                "sin" => Sin,
                "asin" => Asin,
                "cos" => Cos,
                "acos" => Acos,
                "tan" => Tan,
                "atan" => Atan,
                "atan2" => Atan2,
                _ => Var(val),
            }));
        } else if let Ok((range, val)) = convert.meta_bool("bool") {
            convert.update(range);
            expr = Some(val.into());
        } else if let Ok((range, val)) = convert.meta_f64("num") {
            convert.update(range);
            expr = Some(val.into());
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let expr = expr.ok_or(())?;
    Ok((convert.subtract(start), expr))
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
