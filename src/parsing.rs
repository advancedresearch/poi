use super::*;

use piston_meta::{Convert, Range};

fn parse_expr(node: &str, dirs: &[String], mut convert: Convert, ignored: &mut Vec<Range>) -> Result<(Range, Expr), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut expr: Option<Expr> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_alg(dirs, convert, ignored) {
            convert.update(range);
            expr = Some(val);
        } else if let Ok((range, val)) = parse_seq(dirs, convert, ignored) {
            convert.update(range);
            expr = Some(val);
        } else if let Ok((range, val)) = parse_tup(dirs, convert, ignored) {
            convert.update(range);
            if let Tup(val) = &val {
                // Reduce tuple singleton.
                if val.len() == 1 {
                    expr = Some(val[0].clone());
                    continue;
                }
            }
            expr = Some(val);
        } else if let Ok((range, val)) = parse_list(dirs, convert, ignored) {
            convert.update(range);
            expr = Some(val);
        } else if let Ok((range, val)) = parse_rapp(dirs, convert, ignored) {
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
                "inv" => Inv,
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
                "inc" => Inc,
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
                "col" => Col,
                "det" => Det,
                "dim" => Dim,
                "transpose" => Transpose,
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
                "quat" => QuatType,
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
        } else if let Ok((range, val)) = convert.meta_f64("num_imag3") {
            convert.update(range);
            expr = Some(app2(Mul, val, Imag3));
        } else if let Ok((range, val)) = convert.meta_string("poi") {
            convert.update(range);
            let mut found = false;
            for dir in dirs.iter().rev() {
                use std::fs::File;
                use std::io::Read;
                use std::path::PathBuf;

                let path = PathBuf::from(dir).join(val.as_ref().to_owned() + ".poi");

                let mut data_file = match File::open(path) {
                    Ok(f) => f,
                    Err(_) => continue,
                };
                let mut data = String::new();
                data_file.read_to_string(&mut data).unwrap();

                expr = Some(parse_str(&data, dirs).map_err(|err| {
                    eprintln!("ERROR:\n{}", err);
                    ()
                })?);
                found = true;
                break;
            }
            if !found {
                eprintln!("ERROR:\nPoi file `{}` not found", val);
                return Err(())
            };
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let expr = expr.ok_or(())?;
    Ok((convert.subtract(start), expr))
}

fn parse_alg(
    dirs: &[String],
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, Expr), ()> {
    let start = convert;
    let node = "alg";
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut op: Option<Symbol> = None;
    let mut left: Option<Expr> = None;
    let mut unop: Option<Symbol> = None;
    let un = |expr: Expr, unop: &mut Option<Symbol>| {
        if let Some(f) = unop {
            let f = f.clone();
            *unop = None;
            app(f, expr)
        } else {
            expr
        }
    };
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_expr("alg_item", dirs, convert, ignored) {
            convert.update(range);
            if let (Some(expr), Some(op)) = (left, op.clone()) {
                left = Some(un(app2(op, expr, val), &mut unop));
            } else {
                left = Some(un(val, &mut unop));
            }
        } else if let Ok((range, val)) = parse_alg(dirs, convert, ignored) {
            convert.update(range);
            if let (Some(expr), Some(op)) = (left, op.clone()) {
                left = Some(un(app2(op, expr, val), &mut unop));
            } else {
                left = Some(un(val, &mut unop));
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
        } else if let Ok((range, _)) = convert.meta_bool("neg") {
            convert.update(range);
            unop = Some(Neg);
        } else if let Ok((range, _)) = convert.meta_bool("not") {
            convert.update(range);
            unop = Some(Not);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let left = left.ok_or(())?;
    Ok((convert.subtract(start), left))
}

fn parse_tup(dirs: &[String], mut convert: Convert, ignored: &mut Vec<Range>) -> Result<(Range, Expr), ()> {
    let start = convert;
    let node = "tup";
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut items: Vec<Expr> = vec![];
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_expr("item", dirs, convert, ignored) {
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

fn parse_list(dirs: &[String], mut convert: Convert, ignored: &mut Vec<Range>) -> Result<(Range, Expr), ()> {
    let start = convert;
    let node = "list";
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut items: Vec<Expr> = vec![];
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_expr("item", dirs, convert, ignored) {
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

fn parse_rapp(dirs: &[String], mut convert: Convert, ignored: &mut Vec<Range>) -> Result<(Range, Expr), ()> {
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
        } else if let Ok((range, _)) = convert.meta_bool("rsub") {
            convert.update(range);
            sym = Some(Rsub);
        } else if let Ok((range, _)) = convert.meta_bool("rdiv") {
            convert.update(range);
            sym = Some(Rdiv);
        } else if let Ok((range, _)) = convert.meta_bool("mul") {
            convert.update(range);
            sym = Some(Mul);
        } else if let Ok((range, _)) = convert.meta_bool("add") {
            convert.update(range);
            sym = Some(Add);
        } else if let Ok((range, _)) = convert.meta_bool("rpow") {
            convert.update(range);
            sym = Some(Rpow);
        } else if let Ok((range, val)) = parse_expr("arg", dirs, convert, ignored) {
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

fn parse_seq(
    dirs: &[String],
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, Expr), ()> {
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
        } else if let Ok((range, val)) = parse_expr("left", dirs, convert, ignored) {
            convert.update(range);
            left = Some(val);
        } else if let Ok((range, val)) = parse_rapp(dirs, convert, ignored) {
            convert.update(range);
            left = Some(val);
        } else if let Ok((range, val)) = parse_alg(dirs, convert, ignored) {
            convert.update(range);
            left = Some(val);
        } else if let Ok((range, val)) = parse_list(dirs, convert, ignored) {
            convert.update(range);
            left = Some(val);
        } else if let Ok((range, val)) = parse_expr("path", dirs, convert, ignored) {
            convert.update(range);
            if let (Some(nleft), Some(nright), Some(nop)) = (&left, &right, op) {
                left = Some(Op(nop, Box::new(nleft.clone()), Box::new(nright.clone())));
            }
            right = Some(val);
            op = Some(Path);
        } else if let Ok((range, val)) = parse_expr("app", dirs, convert, ignored) {
            convert.update(range);
            if let (Some(nleft), Some(nright), Some(nop)) = (&left, &right, op) {
                left = Some(Op(nop, Box::new(nleft.clone()), Box::new(nright.clone())));
            }
            right = Some(val);
            op = Some(Apply);
        } else if let Ok((range, val)) = parse_expr("constr", dirs, convert, ignored) {
            convert.update(range);
            if let (Some(nleft), Some(nright), Some(nop)) = (&left, &right, op) {
                left = Some(Op(nop, Box::new(nleft.clone()), Box::new(nright.clone())));
            }
            right = Some(val);
            op = Some(Constrain);
        } else if let Ok((range, val)) = parse_expr("comp", dirs, convert, ignored) {
            convert.update(range);
            if let (Some(nleft), Some(nright), Some(nop)) = (&left, &right, op) {
                left = Some(Op(nop, Box::new(nleft.clone()), Box::new(nright.clone())));
            }
            right = Some(val);
            op = Some(Compose);
        } else if let Ok((range, val)) = parse_expr("typ", dirs, convert, ignored) {
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

fn parse_knowledge(
    dirs: &[String],
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, Knowledge), ()> {
    enum KnowledgeOp {
        Eqv,
        Red,
    }

    let start = convert;
    let node = "knowledge";
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut op: Option<KnowledgeOp> = None;
    let mut left: Option<Expr> = None;
    let mut right: Option<Expr> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_expr("left", dirs, convert, ignored) {
            convert.update(range);
            left = Some(val);
        } else if let Ok((range, val)) = parse_expr("right", dirs, convert, ignored) {
            convert.update(range);
            right = Some(val);
        } else if let Ok((range, _)) = convert.meta_bool("<=>") {
            convert.update(range);
            op = Some(KnowledgeOp::Eqv);
        } else if let Ok((range, _)) = convert.meta_bool("=>") {
            convert.update(range);
            op = Some(KnowledgeOp::Red);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let op = op.ok_or(())?;
    let left = left.ok_or(())?;
    let right = right.ok_or(())?;
    let knowledge = match op {
        KnowledgeOp::Eqv => Knowledge::Eqv(left, right),
        KnowledgeOp::Red => Knowledge::Red(left, right),
    };
    Ok((convert.subtract(start), knowledge))
}

/// Stores result of parsing.
pub enum ParseData {
    /// Parsed an expression.
    Expr(Expr),
    /// Parsed some knowledge.
    Knowledge(Knowledge),
}

impl ParseData {
    fn parse(
        dirs: &[String],
        mut convert: Convert,
        ignored: &mut Vec<Range>
    ) -> Result<(Range, ParseData), ()> {
        let start = convert;

        let mut data: Option<ParseData> = None;
        if let Ok((range, val)) = parse_knowledge(dirs, convert, ignored) {
            convert.update(range);
            data = Some(ParseData::Knowledge(val));
        } else if let Ok((range, val)) = parse_expr("expr", dirs, convert, ignored) {
            convert.update(range);
            data = Some(ParseData::Expr(val));
        }

        Ok((convert.subtract(start), data.ok_or(())?))
    }
}

/// Parses an expression string.
pub fn parse_str(data: &str, dirs: &[String]) -> Result<Expr, String> {
    use piston_meta::{parse_errstr, syntax_errstr};

    let syntax_src = include_str!("../assets/syntax.txt");
    let syntax = syntax_errstr(syntax_src)?;

    let mut meta_data = vec![];
    parse_errstr(&syntax, &data, &mut meta_data)?;

    // piston_meta::json::print(&meta_data);

    let convert = Convert::new(&meta_data);
    let mut ignored = vec![];
    match parse_expr("expr", dirs, convert, &mut ignored) {
        Err(()) => Err("Could not convert meta data".into()),
        Ok((_, expr)) => Ok(expr),
    }
}

/// Parses an expression source file.
pub fn parse(source: &str, dirs: &[String]) -> Result<Expr, String> {
    use std::fs::File;
    use std::io::Read;

    let mut data_file = File::open(source).map_err(|err|
        format!("Could not open `{}`, {}", source, err))?;
    let mut data = String::new();
    data_file.read_to_string(&mut data).unwrap();

    parse_str(&data, dirs)
}


/// Parses a data string (expression or knowledge).
pub fn parse_data_str(data: &str, dirs: &[String]) -> Result<ParseData, String> {
    use piston_meta::{parse_errstr, syntax_errstr};

    let syntax_src = include_str!("../assets/syntax.txt");
    let syntax = syntax_errstr(syntax_src)?;

    let mut meta_data = vec![];
    parse_errstr(&syntax, &data, &mut meta_data)?;

    // piston_meta::json::print(&meta_data);

    let convert = Convert::new(&meta_data);
    let mut ignored = vec![];
    match ParseData::parse(dirs, convert, &mut ignored) {
        Err(()) => Err("Could not convert meta data".into()),
        Ok((_, expr)) => Ok(expr),
    }
}

/// Parses a data source file (expression or knowledge).
pub fn parse_data(source: &str, dirs: &[String]) -> Result<ParseData, String> {
    use std::fs::File;
    use std::io::Read;

    let mut data_file = File::open(source).map_err(|err|
        format!("Could not open `{}`, {}", source, err))?;
    let mut data = String::new();
    data_file.read_to_string(&mut data).unwrap();

    parse_data_str(&data, dirs)
}
