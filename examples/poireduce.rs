use poi::*;

fn main() {
    println!("=== Poi Reduce 0.14 ===");
    println!("Type `help` for more information.");
    let ref std = std();

    let mut prev_expr: Option<Expr> = None;
    loop {
        use std::io::{self, Write};

        print!("> ");
        let mut input = String::new();
        io::stdout().flush().unwrap();
        match io::stdin().read_line(&mut input) {
            Ok(_) => {}
            Err(_) => {
                println!("ERROR: Could not read input");
                continue;
            }
        };

        let mut inlined = false;
        match input.trim() {
            "" => {
                // Print separator for readability.
                print!("\n------------------------------------<o=o");
                println!("o=o>------------------------------------\n");
                continue;
            }
            "help" => {print_help(); continue}
            "help norm" => {print_help_norm(); continue}
            "help eqv" => {print_help_eqv(); continue}
            "help sym" => {print_help_sym(); continue}
            "help asym" => {print_help_asym(); continue}
            "help dom" => {print_help_dom(); continue}
            "help triv" => {print_help_triv(); continue}
            "help ex" => {print_help_ex(); continue}
            "help rad" => {print_help_rad(); continue}
            "help imag" => {print_help_imag(); continue}
            "help eps" => {print_help_eps(); continue}
            "std" => {for k in std {println!("{}", k)}; continue}
            "inline all" => {
                if let Some(expr) = &prev_expr {
                    prev_expr = Some(match expr.inline_all(std) {
                        Ok(x) => {
                            inlined = true;
                            x
                        }
                        Err(err) => {
                            println!("ERROR: {:?}", err);
                            continue;
                        }
                    });
                } else {
                    println!("ERROR: No previous expression");
                    continue;
                }
            }
            "bye" => break,
            x => {
                // Print definitions of symbol.
                if x.starts_with("def ") {
                    match parse_str(x[4..].trim()) {
                        Ok(Expr::Sym(s)) => {
                            let mut found = false;
                            for k in std.iter() {
                                if let Knowledge::Def(a, b) = k {
                                    if a == &s {
                                        found = true;
                                        println!("{}", b);
                                    };
                                }
                            }
                            if !found {println!("(no definition found)")};
                            continue;
                        }
                        Err(err) => {
                            println!("ERROR:\n{}", err);
                            continue;
                        }
                        _ => {
                            println!("ERROR:\nExpected symbol");
                            continue;
                        }
                    }
                } else if x.starts_with("echo ") {
                    match parse_str(x[5..].trim()) {
                        Ok(x) => {
                            println!("{}", x);
                            println!("{:?}", x);
                            continue;
                        }
                        Err(err) => {
                            println!("ERROR:\n{}", err);
                            continue;
                        }
                    }
                } else if x.starts_with("eval ") {
                    match parse_str(x[5..].trim()) {
                        Ok(x) => {
                            match x.eval(&std) {
                                Ok(x) => {
                                    println!("{}", x);
                                    continue;
                                }
                                Err(err) => {
                                    println!("ERROR:\n{:?}", err);
                                    continue;
                                }
                            }
                        }
                        Err(err) => {
                            println!("ERROR:\n{}", err);
                            continue;
                        }
                    }
                }
            }
        }

        let mut expr = if inlined {prev_expr.unwrap()} else {
                match parse_str(&input) {
                    Ok(expr) => expr,
                    Err(err) => {
                        println!("ERROR:\n{}", err);
                        continue;
                    }
                }
            };
        println!("{}", expr);
        loop {
            if let Ok((nexpr, i)) = expr.reduce(std) {
                if nexpr == expr {break};
                expr = nexpr;
                println!("{}\n∵ {}", expr, std[i]);
            } else {
                break;
            }
        }

        let equivalences = expr.equivalences(std);
        for i in 0..equivalences.len() {
            let j = equivalences[i].1;
            println!("<=>  {}\n     ∵ {}", equivalences[i].0, std[j]);
        }

        println!("∴ {}", expr);

        prev_expr = Some(expr);
    }
}

fn print_help() {print!("{}", include_str!("../assets/help.txt"))}
fn print_help_norm() {print!("{}", include_str!("../assets/help-norm.txt"))}
fn print_help_eqv() {print!("{}", include_str!("../assets/help-eqv.txt"))}
fn print_help_sym() {print!("{}", include_str!("../assets/help-sym.txt"))}
fn print_help_asym() {print!("{}", include_str!("../assets/help-asym.txt"))}
fn print_help_dom() {print!("{}", include_str!("../assets/help-dom.txt"))}
fn print_help_triv() {print!("{}", include_str!("../assets/help-triv.txt"))}
fn print_help_ex() {print!("{}", include_str!("../assets/help-ex.txt"))}
fn print_help_rad() {print!("{}", include_str!("../assets/help-rad.txt"))}
fn print_help_imag() {print!("{}", include_str!("../assets/help-imag.txt"))}
fn print_help_eps() {print!("{}", include_str!("../assets/help-eps.txt"))}
