use comfy_table::presets::UTF8_HORIZONTAL_ONLY;
use comfy_table::{Attribute, Cell, ContentArrangement, Table};
use itertools::Itertools;
use z3::ast::Ast;
use z3::{ast, Config, Context, Model, Optimize, SatResult, Solver};

macro_rules! function {
    () => {{
        fn f() {}
        fn type_name_of<T>(_: T) -> &'static str {
            std::any::type_name::<T>()
        }
        let name = type_name_of(f);

        // Find and cut the rest of the path
        match &name[..name.len() - 3].rfind(':') {
            Some(pos) => &name[pos + 1..name.len() - 3],
            None => &name[..name.len() - 3],
        }
    }};
}

fn main() {
    with_forall();
    prover();
    chehov_tutor();
    sum_of_non_zero_4_times_product();
    subset_sum();
    animals();
    wood_workshop();
    xkcd287();
    toy();
    zebra_puzzle();
    fred_puzzle();
    multiple_choice_logic_puzzle();
    feed_kids_puzzle();
    popsicles();
}

fn popsicles() {
    println!("--- {} ---", function!());
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let box1pop = ast::Int::new_const(&ctx, "1 popsicle");
    let box3pop = ast::Int::new_const(&ctx, "3 popsicles");
    let box5pop = ast::Int::new_const(&ctx, "5 popsicles");
    let pop_total = ast::Int::new_const(&ctx, "Total popsicles");
    let cost_total = ast::Int::new_const(&ctx, "Cost total");

    let solver = Optimize::new(&ctx);
    solver.assert(&(&box1pop * 1u64 + &box3pop * 3u64 + &box5pop * 5u64)._eq(&pop_total));
    solver.assert(&(&box1pop * 1u64 + &box3pop * 2u64 + &box5pop * 3u64)._eq(&cost_total));
    solver.assert(&cost_total._eq(&ast::Int::from_i64(&ctx, 8)));
    solver.assert(&box1pop.ge(&ast::Int::from_i64(&ctx, 0)));
    solver.assert(&box3pop.ge(&ast::Int::from_i64(&ctx, 0)));
    solver.assert(&box5pop.ge(&ast::Int::from_i64(&ctx, 0)));
    solver.maximize(&pop_total);

    let result = solver.check(&[]);
    println!("Result: {result:?}");
    if let Some(m) = solver.get_model() {
        println!("Model:");
        println!("{m}");
    };
}

fn feed_kids_puzzle() {
    println!("--- {} ---", function!());
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let erica = ast::Int::new_const(&ctx, "Erica");
    let frank = ast::Int::new_const(&ctx, "Frank");
    let greg = ast::Int::new_const(&ctx, "Greg");
    let hank = ast::Int::new_const(&ctx, "Hank");

    let apple = ast::Int::from_i64(&ctx, 1);
    let banana = ast::Int::from_i64(&ctx, 2);
    let cherry = ast::Int::from_i64(&ctx, 3);
    let date = ast::Int::from_i64(&ctx, 4);

    let solver = Solver::new(&ctx);
    solver.assert(&ast::Ast::distinct(&ctx, &[&erica, &frank, &greg, &hank]));

    let params = vec![
        &erica, &frank, &greg, &hank, &apple, &banana, &cherry, &date,
    ];

    for p in &params {
        solver.assert(&ast::Bool::and(
            &ctx,
            &[
                &p.ge(&ast::Int::from_i64(&ctx, 1)),
                &p.le(&ast::Int::from_i64(&ctx, 4)),
            ],
        ));
    }

    solver.assert(&ast::Bool::or(
        &ctx,
        &[&erica._eq(&cherry), &erica._eq(&date)],
    ));
    solver.assert(&ast::Bool::or(
        &ctx,
        &[&frank._eq(&cherry), &frank._eq(&apple)],
    ));
    solver.assert(&ast::Bool::or(
        &ctx,
        &[&greg._eq(&cherry), &greg._eq(&banana)],
    ));
    solver.assert(&ast::Bool::or(
        &ctx,
        &[&hank._eq(&apple), &hank._eq(&banana), &hank._eq(&date)],
    ));

    let read_param = |m: &Model<'_>, param: &ast::Int<'_>| -> (String, i64) {
        let name = param.to_string();
        let value = m.eval(param, true).unwrap().as_i64().unwrap();
        (name, value)
    };

    while solver.check() == SatResult::Sat {
        if let Some(m) = solver.get_model() {
            let mut modifications = Vec::new();
            m.iter().for_each(|fd| {
                modifications.push(
                    fd.apply(&[])
                        ._eq(&m.get_const_interp(&fd.apply(&[])).unwrap())
                        .not(),
                );
            });
            solver.assert(&ast::Bool::or(
                &ctx,
                &modifications.iter().collect::<Vec<_>>(),
            ));

            let groupped = params
                .iter()
                .map(|p| read_param(&m, p))
                .into_group_map_by(|(_, v)| *v);

            let mut table = Table::new();
            table
                .load_preset(UTF8_HORIZONTAL_ONLY)
                .set_content_arrangement(ContentArrangement::Dynamic)
                .set_width(120)
                .set_header(vec![
                    Cell::new("apple").add_attribute(Attribute::Bold),
                    Cell::new("banana").add_attribute(Attribute::Bold),
                    Cell::new("cherry").add_attribute(Attribute::Bold),
                    Cell::new("date").add_attribute(Attribute::Bold),
                ]);
            let first_col = &groupped[&1];
            let second_col = &groupped[&2];
            let third_col = &groupped[&3];
            let fourth_col = &groupped[&4];

            for n in 0usize..1 {
                let (s1, _) = &first_col[n];
                let (s2, _) = &second_col[n];
                let (s3, _) = &third_col[n];
                let (s4, _) = &fourth_col[n];

                table.add_row(vec![
                    Cell::new(s1),
                    Cell::new(s2),
                    Cell::new(s3),
                    Cell::new(s4),
                ]);
            }
            println!("{table}");
        }
    }
}

fn multiple_choice_logic_puzzle() {
    println!("--- {} ---", function!());
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let problem = r#"
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-fun e () Bool)
(declare-fun f () Bool)
    
( assert (= a (and b c d e f)))
( assert (= b (and (not c) (not d) (not e) (not f))))
( assert (= c (and a b)))
( assert (= d (or
    (and a (not b) (not c))
    (and (not a) b (not c))
    (and (not a) (not b) c)
    )))
( assert (= e (and (not a) (not b) (not c) (not d))))
( assert (= f (and (not a) (not b) (not c) (not d) (not e))))
"#;
    let solver = Solver::new(&ctx);
    solver.from_string(problem);
    let result = solver.check();
    println!("Result: {result:?}");
    if let Some(m) = solver.get_model() {
        println!("Model:");
        println!("{m}");
    };
}

fn fred_puzzle() {
    println!("--- {} ---", function!());
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let ei = ast::Bool::new_const(&ctx, "Ed Innocent");
    let fi = ast::Bool::new_const(&ctx, "Fred Innocent");
    let ti = ast::Bool::new_const(&ctx, "Ted Innocent");
    let eg = ast::Bool::new_const(&ctx, "Ed Guilty");
    let fg = ast::Bool::new_const(&ctx, "Fred Guilty");
    let tg = ast::Bool::new_const(&ctx, "Ted Guilty");

    let solver = Solver::new(&ctx);
    solver.assert(&ei._eq(&eg).not());
    solver.assert(&fi._eq(&fg).not());
    solver.assert(&ti._eq(&tg).not());

    solver.assert(&ei._eq(&ast::Bool::and(&ctx, &[&fg, &ti])));
    solver.assert(&fi._eq(&eg.implies(&tg)));
    solver.assert(&ti._eq(&ast::Bool::and(
        &ctx,
        &[&ti, &ast::Bool::or(&ctx, &[&fg, &eg])],
    )));

    let result = solver.check();
    println!("Result: {result:?}");
    if let Some(m) = solver.get_model() {
        println!("Model:");
        println!("{m}");
    };
}

fn zebra_puzzle() {
    println!("--- {} ---", function!());
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let yellow = ast::Int::new_const(&ctx, "Yellow");
    let blue = ast::Int::new_const(&ctx, "Blue");
    let red = ast::Int::new_const(&ctx, "Red");
    let ivory = ast::Int::new_const(&ctx, "Ivory");
    let green = ast::Int::new_const(&ctx, "Green");

    let norwegian = ast::Int::new_const(&ctx, "Norwegian");
    let ukrainian = ast::Int::new_const(&ctx, "Ukrainian");
    let englishman = ast::Int::new_const(&ctx, "Englishman");
    let spaniard = ast::Int::new_const(&ctx, "Spaniard");
    let japanese = ast::Int::new_const(&ctx, "Japanese");

    let water = ast::Int::new_const(&ctx, "Water");
    let milk = ast::Int::new_const(&ctx, "Milk");
    let tea = ast::Int::new_const(&ctx, "Tea");
    let orange_juice = ast::Int::new_const(&ctx, "OrangeJuice");
    let coffee = ast::Int::new_const(&ctx, "Coffee");

    let kools = ast::Int::new_const(&ctx, "Kool");
    let chesterfield = ast::Int::new_const(&ctx, "Chesterfield");
    let old_gold = ast::Int::new_const(&ctx, "OldGold");
    let lucky_strike = ast::Int::new_const(&ctx, "LuckyStrike");
    let parliament = ast::Int::new_const(&ctx, "Parliament");

    let fox = ast::Int::new_const(&ctx, "Fox");
    let horse = ast::Int::new_const(&ctx, "Horse");
    let snails = ast::Int::new_const(&ctx, "Snail");
    let dog = ast::Int::new_const(&ctx, "Dog");
    let zebra = ast::Int::new_const(&ctx, "Zebra");

    let params = vec![
        &norwegian,
        &ukrainian,
        &spaniard,
        &englishman,
        &japanese,
        &red,
        &blue,
        &ivory,
        &green,
        &yellow,
        &water,
        &milk,
        &tea,
        &orange_juice,
        &coffee,
        &kools,
        &chesterfield,
        &lucky_strike,
        &old_gold,
        &parliament,
        &fox,
        &horse,
        &snails,
        &dog,
        &zebra,
    ];

    let solver = Solver::new(&ctx);
    solver.assert(&ast::Ast::distinct(
        &ctx,
        &[&yellow, &blue, &red, &ivory, &green],
    ));
    solver.assert(&ast::Ast::distinct(
        &ctx,
        &[&norwegian, &ukrainian, &englishman, &spaniard, &japanese],
    ));
    solver.assert(&ast::Ast::distinct(
        &ctx,
        &[&water, &milk, &orange_juice, &coffee, &tea],
    ));
    solver.assert(&ast::Ast::distinct(
        &ctx,
        &[&kools, &chesterfield, &old_gold, &lucky_strike, &parliament],
    ));
    solver.assert(&ast::Ast::distinct(
        &ctx,
        &[&fox, &horse, &snails, &dog, &zebra],
    ));

    for p in &params {
        solver.assert(&ast::Bool::and(
            &ctx,
            &[
                &p.ge(&ast::Int::from_i64(&ctx, 1)),
                &p.le(&ast::Int::from_i64(&ctx, 5)),
            ],
        ));
    }

    solver.assert(&englishman._eq(&red));
    solver.assert(&spaniard._eq(&dog));
    solver.assert(&coffee._eq(&green));
    solver.assert(&ukrainian._eq(&tea));
    solver.assert(&green._eq(&(&ivory + 1i64)));
    solver.assert(&old_gold._eq(&snails));
    solver.assert(&kools._eq(&yellow));
    solver.assert(&milk._eq(&ast::Int::from_i64(&ctx, 3)));
    solver.assert(&norwegian._eq(&ast::Int::from_i64(&ctx, 1)));

    solver.assert(&ast::Bool::or(
        &ctx,
        &[
            &chesterfield._eq(&(&fox + 1i64)),
            &chesterfield._eq(&(&fox - 1i64)),
        ],
    ));
    solver.assert(&ast::Bool::or(
        &ctx,
        &[&kools._eq(&(&horse + 1i64)), &kools._eq(&(&horse - 1i64))],
    ));

    solver.assert(&lucky_strike._eq(&orange_juice));
    solver.assert(&japanese._eq(&parliament));

    solver.assert(&ast::Bool::or(
        &ctx,
        &[
            &norwegian._eq(&(&blue + 1i64)),
            &norwegian._eq(&(&blue - 1i64)),
        ],
    ));

    let result = solver.check();
    println!("Result: {result:?}");

    let read_param = |m: &Model<'_>, param: &ast::Int<'_>| -> (String, i64) {
        let name = param.to_string();
        let value = m.eval(param, true).unwrap().as_i64().unwrap();
        (name, value)
    };

    if let Some(m) = solver.get_model() {
        let groupped = params
            .into_iter()
            .map(|p| read_param(&m, p))
            .into_group_map_by(|(_, v)| *v);

        let mut table = Table::new();
        table
            .load_preset(UTF8_HORIZONTAL_ONLY)
            .set_content_arrangement(ContentArrangement::Dynamic)
            .set_width(120)
            .set_header(vec![
                Cell::new("1").add_attribute(Attribute::Bold),
                Cell::new("2").add_attribute(Attribute::Bold),
                Cell::new("3").add_attribute(Attribute::Bold),
                Cell::new("4").add_attribute(Attribute::Bold),
                Cell::new("5").add_attribute(Attribute::Bold),
            ]);
        let first_col = &groupped[&1];
        let second_col = &groupped[&2];
        let third_col = &groupped[&3];
        let fourth_col = &groupped[&4];
        let fifth_col = &groupped[&5];

        for n in 0usize..5 {
            let (s1, _) = &first_col[n];
            let (s2, _) = &second_col[n];
            let (s3, _) = &third_col[n];
            let (s4, _) = &fourth_col[n];
            let (s5, _) = &fifth_col[n];

            table.add_row(vec![
                Cell::new(s1),
                Cell::new(s2),
                Cell::new(s3),
                Cell::new(s4),
                Cell::new(s5),
            ]);
        }
        println!("{table}");
    };
}

fn with_forall() {
    println!("--- {} ---", function!());
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let x = ast::BV::new_const(&ctx, "x", 64);
    let y = ast::BV::new_const(&ctx, "y", 64);
    let one = ast::BV::from_i64(&ctx, 1, 64);

    let a1 = ((&x + &y) - ((&x & &y).bvshl(&one)))._eq(&(&x ^ &y));

    let a1 = ast::forall_const(&ctx, &[&x, &y], &[], &a1);

    let solver = Solver::new(&ctx);
    solver.assert(&a1);
    let result = solver.check();
    println!("Result: {result:?}");
}

fn prover() {
    println!("--- {} ---", function!());
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let x = ast::BV::new_const(&ctx, "x", 64);
    let y = ast::BV::new_const(&ctx, "y", 64);
    let minus_two = ast::BV::from_i64(&ctx, -2, 64);
    let output = ast::BV::new_const(&ctx, "output", 64);

    let a1 = (&x ^ &y)._eq(&output);
    let a2 = (((&x & &y) * &minus_two) + (&y + &x))._eq(&output).not();

    let solver = Solver::new(&ctx);
    solver.assert(&a1);
    solver.assert(&a2);
    let result = solver.check();
    println!("Result: {result:?}");
    if let Some(m) = solver.get_model() {
        println!("Model:");
        println!("{m}");
    };
}

fn chehov_tutor() {
    println!("--- {} ---", function!());
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let black_cloth = ast::Int::new_const(&ctx, "black_cloth");
    let blue_cloth = ast::Int::new_const(&ctx, "blue_cloth");

    let a1 = (5i64 * &blue_cloth + 3i64 * &black_cloth)._eq(&ast::Int::from_i64(&ctx, 540));
    let a2 = (&blue_cloth + &black_cloth)._eq(&ast::Int::from_i64(&ctx, 138));

    let solver = Solver::new(&ctx);
    solver.assert(&a1);
    solver.assert(&a2);

    let result = solver.check();
    println!("Result: {result:?}");
    if let Some(m) = solver.get_model() {
        println!("Model:");
        println!("{m}");
    };
}

fn sum_of_non_zero_4_times_product() {
    println!("--- {} ---", function!());
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let x = ast::Real::new_const(&ctx, "x");
    let y = ast::Real::new_const(&ctx, "x");

    let zero = ast::Real::from_real(&ctx, 0, 1);
    let one = ast::Real::from_real(&ctx, 1, 1);
    let four = ast::Real::from_real(&ctx, 4, 1);
    let a1 = x.gt(&zero);
    let a2 = y.gt(&zero);
    let a3 = (&x + &y)._eq(&(&four * &x * &y));

    let solver = Solver::new(&ctx);
    solver.assert(&a1);
    solver.assert(&a2);
    solver.assert(&a3);

    let result = solver.check();
    println!("Result: {result:?}");
    if let Some(m) = solver.get_model() {
        let answer = m.eval(&(&one / &x + &one / &y), true);
        println!("Model: {m} answer: {answer:?}");
        println!();
    };
}

fn subset_sum() {
    println!("--- {} ---", function!());
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let set = vec![-7i64, -3, -2, 5, 8];

    let vars = set
        .iter()
        .map(|i| ast::Int::new_const(&ctx, format!("var_{i}")))
        .collect_vec();

    let solver = Solver::new(&ctx);
    let mut rt = vec![];
    for (ix, v) in vars.iter().enumerate() {
        let z = v._eq(&ast::Int::from_i64(&ctx, 0));
        let nz = v._eq(&ast::Int::from_i64(&ctx, 1));
        solver.assert(&ast::Bool::or(&ctx, &[&z, &nz]));
        rt.push(v * set[ix]);
    }

    let sum = ast::Int::add(&ctx, rt.iter().collect_vec().as_slice());
    let sum_vars = ast::Int::add(&ctx, vars.iter().collect_vec().as_slice());

    solver.assert(&sum._eq(&ast::Int::from_i64(&ctx, 0)));
    solver.assert(&sum_vars.ge(&ast::Int::from_i64(&ctx, 1)));

    let result = solver.check();
    println!("Result: {result:?}");
    if let Some(m) = solver.get_model() {
        println!("Model:");
        println!("{m}");
        let mut subset = vec![];
        for (ix, v) in vars.iter().enumerate() {
            let r = m.eval(v, true).unwrap().as_i64().unwrap();
            if r == 1 {
                subset.push(set[ix])
            }
        }
        println!("set: {set:?}");
        println!("subset: {subset:?}");
        println!();
    };
}

fn animals() {
    println!("--- {} ---", function!());
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let cat = ast::Int::new_const(&ctx, "cat");
    let dog = ast::Int::new_const(&ctx, "dog");
    let rabbit = ast::Int::new_const(&ctx, "rabbit");

    let a1 = (&rabbit + &cat)._eq(&ast::Int::from_i64(&ctx, 10));
    let a2 = (&rabbit + &dog)._eq(&ast::Int::from_i64(&ctx, 20));
    let a3 = (&cat + &dog)._eq(&ast::Int::from_i64(&ctx, 24));

    let solver = Solver::new(&ctx);
    solver.assert(&a1);
    solver.assert(&a2);
    solver.assert(&a3);

    let result = solver.check();
    println!("Result: {result:?}");
    if let Some(m) = solver.get_model() {
        println!("Model:");
        println!("{m}");
    };
}

fn wood_workshop() {
    println!("--- {} ---", function!());
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let workpieces_total = ast::Int::new_const(&ctx, "workpieces_total");

    let cut_a = ast::Int::new_const(&ctx, "cut_a");
    let cut_b = ast::Int::new_const(&ctx, "cut_b");
    let cut_c = ast::Int::new_const(&ctx, "cut_c");
    let cut_d = ast::Int::new_const(&ctx, "cut_d");

    let out_a = ast::Int::new_const(&ctx, "out_a");
    let out_b = ast::Int::new_const(&ctx, "out_b");

    let zero = ast::Int::from_i64(&ctx, 0);

    let out_a_eq = (&(&cut_a * 3i64) + &(&cut_b * 2i64) + &(&cut_c * 1i64))._eq(&out_a);
    let out_b_eq =
        (&(&cut_a * 1i64) + &(&cut_b * 6i64) + &(&cut_c * 9i64) + &(&cut_d * 13i64))._eq(&out_b);

    let solver = Optimize::new(&ctx);
    solver.assert(&cut_a.ge(&zero));
    solver.assert(&cut_b.ge(&zero));
    solver.assert(&cut_c.ge(&zero));
    solver.assert(&cut_d.ge(&zero));
    solver.assert(&out_a_eq);
    solver.assert(&out_b_eq);

    solver.assert(&out_a._eq(&ast::Int::from_i64(&ctx, 800)));
    solver.assert(&out_b._eq(&ast::Int::from_i64(&ctx, 400)));
    solver.assert(&(&cut_a + &cut_b + &cut_c + &cut_d)._eq(&workpieces_total));

    solver.minimize(&workpieces_total);

    let result = solver.check(&[]);

    println!("Result: {result:?}");
    if let Some(m) = solver.get_model() {
        println!("Model:");
        println!("{m}");
    };
}

fn xkcd287() {
    println!("--- {} ---", function!());
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let a = ast::Int::new_const(&ctx, "a");
    let b = ast::Int::new_const(&ctx, "b");
    let c = ast::Int::new_const(&ctx, "c");
    let d = ast::Int::new_const(&ctx, "d");
    let e = ast::Int::new_const(&ctx, "e");
    let f = ast::Int::new_const(&ctx, "f");

    let zero = ast::Int::from_i64(&ctx, 0);

    let equation = (&(&a * 215i64)
        + &(&b * 275i64)
        + &(&c * 335i64)
        + &(&d * 355i64)
        + &(&e * 420i64)
        + &(&f * 580i64))
        ._eq(&ast::Int::from_i64(&ctx, 1505));

    let solver = Solver::new(&ctx);
    solver.assert(&a.ge(&zero));
    solver.assert(&b.ge(&zero));
    solver.assert(&c.ge(&zero));
    solver.assert(&d.ge(&zero));
    solver.assert(&e.ge(&zero));
    solver.assert(&f.ge(&zero));
    solver.assert(&equation);

    let result = solver.check();

    println!("Result: {result:?}");
    if let Some(m) = solver.get_model() {
        println!("Model:");
        println!("{m}");
    };
}

fn toy() {
    println!("--- {} ---", function!());
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let circle = ast::Int::new_const(&ctx, "circle");
    let triangle = ast::Int::new_const(&ctx, "triangle");
    let square = ast::Int::new_const(&ctx, "square");

    let a1 = (&circle + &circle)._eq(&ast::Int::from_i64(&ctx, 10));

    let a2 = ((&circle * &square) + &square)._eq(&ast::Int::from_i64(&ctx, 12));

    let a3 = ((&circle * &square) - (&triangle * &circle))._eq(&circle);

    let solver = Solver::new(&ctx);
    solver.assert(&a1);
    solver.assert(&a2);
    solver.assert(&a3);

    let result = solver.check();
    println!("Result: {result:?}");
    if let Some(m) = solver.get_model() {
        println!("Model:");
        println!("{m}");
    };
}
