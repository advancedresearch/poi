use poi::*;

const DEFAULT_GOAL_DEPTH: u64 = 2;

fn main() {
    println!("=== Poi Reduce 0.14 ===");
    println!("Type `help` for more information.");
    let ref std = std();

    let mut prev_expr: Option<Expr> = None;
    let mut goal: Option<Expr> = None;
    let mut goal_depth: u64 = DEFAULT_GOAL_DEPTH;
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
            "reset goal" => {goal = None; println!("Poi: Goal is reset."); continue}
            "reset depth" => {
                goal_depth = DEFAULT_GOAL_DEPTH;
                println!("Poi: Goal depth is reset to {}.", goal_depth);
                continue;
            }
            "inc depth" => {
                goal_depth += 1;
                println!("Poi: Goal depth is set to {}.", goal_depth);
                continue;
            }
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
                } else if x.starts_with("goal ") {
                    match parse_str(x[5..].trim()) {
                        Ok(mut expr) => {
                            // Reduce expression first.
                            loop {
                                if let Ok((nexpr, i)) = expr.reduce(std) {
                                    if nexpr == expr {break};
                                    expr = nexpr;
                                    println!("{}\n∵ {}", expr, std[i]);
                                } else {
                                    break;
                                }
                            }
                            println!("new goal: {}", expr);
                            goal = Some(expr);
                            continue;
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

        let goal_reached = if let Some(g) = &goal {
            if &expr == g {
                goal = None;
                true
            } else {false}
        } else {false};

        if !goal_reached {
            let mut found_any = false;
            let equivalences = expr.equivalences(std);
            loop {
                let mut line = false;
                for i in 0..equivalences.len() {
                    let j = equivalences[i].1;
                    let display = if let Some(g) = &goal {
                        let mut history = vec![expr.clone()];
                        if let Some(d) = find_goal(g, &equivalences[i].0, std, goal_depth, &mut history) {
                            found_any = true;
                            if line {println!("")};
                            print!("depth: {} ", d);
                            true
                        } else {
                            false
                        }
                    } else {false};
                    if display {
                        println!("<=>  {}\n     ∵ {}", equivalences[i].0, std[j]);
                    } else {
                        line = true;
                        print!(".");
                        io::stdout().flush().unwrap();
                    }
                }
                if line {println!("")};

                if found_any || goal.is_none() {
                    break;
                } else {
                    println!("Poi: Could not find goal in {} steps (Tip: Use `inc depth`).", goal_depth);
                    break;
                }
            }

            if !found_any && goal.is_some() {
                for i in 0..equivalences.len() {
                    let j = equivalences[i].1;
                    println!("<=>  {}\n     ∵ {}", equivalences[i].0, std[j]);
                }
            }
        }

        println!("∴ {}", expr);
        if goal_reached {
            println!("Q.E.D.");
        }

        prev_expr = Some(expr);
    }
}

fn find_goal(
    goal: &Expr,
    expr: &Expr,
    std: &[Knowledge],
    depth: u64,
    history: &mut Vec<Expr>
) -> Option<u64> {
    // Reduce expression.
    let mut expr = expr.clone();
    loop {
        if let Ok((nexpr, _)) = expr.reduce(std) {
            if nexpr == expr {break};
            expr = nexpr;
        } else {
            break;
        }
    }

    for i in 0..history.len() {
        if &history[i] == &expr {return None};
    }
    history.push(expr.clone());

    if goal == &expr {return Some(0)};

    if depth > 0 {
        let equivalences = expr.equivalences(std);
        for i in 0..equivalences.len() {
            // Add depth to the output.
            if let Some(d) = find_goal(goal, &equivalences[i].0, std, depth - 1, history) {
                return Some(d+1);
            }
        }
    }

    None
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
