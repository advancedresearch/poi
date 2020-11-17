use poi::*;

const DEFAULT_GOAL_DEPTH: u64 = 2;

fn main() {
    println!("=== Poi Reduce 0.17 ===");
    println!("Type `help` for more information.");
    let ref std = std();

    let mut prev_expr: Option<Expr> = None;
    let mut goal: Option<Expr> = None;
    let mut goal_depth: u64 = DEFAULT_GOAL_DEPTH;
    let mut use_min_depth = true;
    let mut dirs: Vec<String> = vec![];
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
            "help goal" => {print_help_goal(); continue}
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
            "help d" => {print_help_d(); continue}
            "help integ" => {print_help_integ(); continue}
            "help list" => {print_help_list(); continue}
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
            "min depth" => {
                use_min_depth = true;
                println!("Poi: Automated minimum depth toward goal.");
                continue;
            }
            "pick depth" => {
                use_min_depth = false;
                println!("Poi: User chooses equivalence toward goal.");
                continue;
            }
            "clear dir" => {
                dirs.clear();
                println!("Poi: Directories cleared.");
                continue;
            }
            x => {
                // Print definitions of symbol.
                if x.starts_with("def ") {
                    match parse_str(x[4..].trim(), &dirs) {
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
                    match parse_str(x[5..].trim(), &dirs) {
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
                    match parse_str(x[5..].trim(), &dirs) {
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
                    match parse_str(x[5..].trim(), &dirs) {
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
                } else if x.starts_with("open ") {
                    if let Some(s) = json_str(&x[5..]) {
                        println!("Poi: Added directory `{}`.", s);
                        dirs.push(s);
                    }
                    continue;
                }
            }
        }

        let mut expr = if inlined {prev_expr.unwrap()} else {
                match parse_str(&input, &dirs) {
                    Ok(expr) => expr,
                    Err(err) => {
                        println!("ERROR:\n{}", err);
                        continue;
                    }
                }
            };

        // Keeps track of goal depth to reduce search space
        // when getting closer to the goal using minimum depth selection.
        let mut min: Option<u64> = None;
        'process_expr: loop {
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
                let mut found_count = 0;
                let mut first_found: Option<usize> = None;
                let mut min_found: Option<(usize, u64)> = None;
                let equivalences = expr.equivalences(std);
                loop {
                    let mut line = false;
                    for i in 0..equivalences.len() {
                        let mut cont = false;
                        let mut br = false;
                        let j = equivalences[i].1;
                        let display = if let Some(g) = &goal {
                            let eqv_expr = equivalences[i].0.reduce_all(std);
                            let mut history = vec![expr.clone(), eqv_expr.clone()];
                            let depth = min.unwrap_or(goal_depth);
                            if let Some(d) = find_goal(g, &eqv_expr, std, depth, &mut history) {
                                found_count += 1;
                                if first_found.is_none() {
                                    first_found = Some(i);
                                }
                                if min_found.is_none() || min_found.unwrap().1 > d {
                                    min_found = Some((i, d));
                                }
                                if line {line = false; println!("")};
                                print!("depth: {} ", d);
                                if d == 0 {
                                    expr = equivalences[i].0.clone();
                                    cont = true;
                                } else if min == Some(d) {
                                    br = true;
                                }
                                true
                            } else {
                                false
                            }
                        } else {true};
                        if display {
                            println!("<=>  {}\n     ∵ {}", equivalences[i].0, std[j]);
                        } else {
                            line = true;
                            print!(".");
                            io::stdout().flush().unwrap();
                        }
                        if cont {continue 'process_expr};
                        if br {break};
                    }
                    if line {println!("")};

                    if use_min_depth && min_found.is_some() {
                        expr = equivalences[min_found.unwrap().0].0.clone();
                        min = Some(min_found.unwrap().1 - 1);
                        continue 'process_expr;
                    } else if found_count == 1 && goal.is_some() {
                        expr = equivalences[first_found.unwrap()].0.clone();
                        continue 'process_expr;
                    } else if found_count > 0 || goal.is_none() {
                        break;
                    } else {
                        println!("Poi: Could not find goal in {} steps (Tip: Use `inc depth`).", goal_depth);
                        break;
                    }
                }

                if found_count == 0 && goal.is_some() {
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
            break;
        }

        prev_expr = Some(expr);
    }
}

// Parses a JSON string.
fn json_str(txt: &str) -> Option<String> {
    use read_token::ReadToken;
    let r = ReadToken::new(txt, 0);
    if let Some(range) = r.string() {
        if let Ok(txt) = r.parse_string(range.length) {
            Some(txt)
        } else {
            println!("ERROR:\nCould not parse string");
            None
        }
    } else {
        println!("ERROR:\nExpected string");
        None
    }
}

fn find_goal(
    goal: &Expr,
    expr: &Expr,
    std: &[Knowledge],
    depth: u64,
    history: &mut Vec<Expr>
) -> Option<u64> {
    if goal == expr {return Some(0)};

    if depth > 0 {
        let equivalences = expr.equivalences(std);
        let n = history.len();
        // Use breath-first search.
        for i in 0..equivalences.len() {
            let expr = equivalences[i].0.reduce_all(std);

            for i in 0..history.len() {
                if &history[i] == &expr {continue};
            }

            if goal == &expr {return Some(1)};
            history.push(expr);
        }
        for i in n..history.len() {
            // Add depth to the output.
            let expr = history[i].clone();
            if let Some(d) = find_goal(goal, &expr, std, depth - 1, history) {
                return Some(d+1);
            }
        }
    }

    None
}

fn print_help() {print!("{}", include_str!("../assets/help.txt"))}
fn print_help_goal() {print!("{}", include_str!("../assets/help-goal.txt"))}
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
fn print_help_d() {print!("{}", include_str!("../assets/help-d.txt"))}
fn print_help_integ() {print!("{}", include_str!("../assets/help-integ.txt"))}
fn print_help_list() {print!("{}", include_str!("../assets/help-list.txt"))}
