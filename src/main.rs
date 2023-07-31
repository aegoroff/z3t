use itertools::Itertools;
use z3::ast::Ast;
use z3::{ast, Config, Context, Optimize, Solver};

fn main() {
    prover();
    chehov_tutor();
    sum_of_non_zero_4_times_product();
    subset_sum();
    animals();
    wood_workshop();
    xkcd287();
    toy();
}

fn prover() {
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
    match solver.get_model() {
        Some(m) => {
            println!("Result: {result:?}");
            println!("Model:");
            println!("{m}");
        }
        None => println!("Result: {result:?}"),
    };
}

fn chehov_tutor() {
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
    match solver.get_model() {
        Some(m) => {
            println!("Result: {result:?}");
            println!("Model:");
            println!("{m}");
        }
        None => println!("Result: {result:?}"),
    };
}

fn sum_of_non_zero_4_times_product() {
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
    match solver.get_model() {
        Some(m) => {
            println!("Result: {result:?}");
            let answer = m.eval(&(&one / &x + &one / &y), true);
            println!("Model: {m} answer: {answer:?}");
            println!();
        }
        None => println!("Result: {result:?}"),
    };
}

fn subset_sum() {
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
    match solver.get_model() {
        Some(m) => {
            println!("Result: {result:?}");
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
        }
        None => println!("Result: {result:?}"),
    };
}

fn animals() {
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
    match solver.get_model() {
        Some(m) => {
            println!("Result: {result:?}");
            println!("Model:");
            println!("{m}");
        }
        None => println!("Result: {result:?}"),
    };
}

fn wood_workshop() {
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

    match solver.get_model() {
        Some(m) => {
            println!("Result: {result:?}");
            println!("Model:");
            println!("{m}");
        }
        None => println!("Result: {result:?}"),
    };
}

fn xkcd287() {
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

    match solver.get_model() {
        Some(m) => {
            println!("Result: {result:?}");
            println!("Model:");
            println!("{m}");
        }
        None => println!("Result: {result:?}"),
    };
}

fn toy() {
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
    match solver.get_model() {
        Some(m) => {
            println!("Result: {result:?}");
            println!("Model:");
            println!("{m}");
        }
        None => println!("Result: {result:?}"),
    };
}
