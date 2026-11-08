//! Command-line interface for the PRA checker.

mod check;
mod kernel;
mod parser;
mod spec;
mod syntax;

use crate::check::run;
use crate::syntax::Res;
use std::path::Path;
use std::time::Instant;

fn execute() -> Res<()> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let usage = "usage: pra-check DIRECTORY";
    if args.len() == 1 && matches!(args[0].as_str(), "--help" | "-h") {
        println!("{usage}\nCheck every specification/object pair listed in DIRECTORY/modules.txt.");
        return Ok(());
    }
    if args.len() != 1 || args[0].starts_with('-') {
        return Err(usage.into());
    }
    let start = Instant::now();
    let (t, n, p) = run(Path::new(&args[0]))?;
    println!(
        concat!(
            "{{\"declarations\":{},\"proof_nodes\":{},",
            "\"total_s\":{},\"spec_s\":{},\"object_s\":{},",
            "\"match_s\":{},\"check_s\":{}}}"
        ),
        n,
        p,
        start.elapsed().as_secs_f64(),
        t.spec.as_secs_f64(),
        t.full.as_secs_f64(),
        t.matching.as_secs_f64(),
        t.checking.as_secs_f64()
    );
    Ok(())
}

fn main() {
    // Run the checker on a 64 MiB stack.
    let outcome = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(execute)
        .expect("checker thread")
        .join();
    match outcome {
        Ok(Ok(())) => {}
        Ok(Err(e)) => {
            eprintln!("rejected: {e}");
            std::process::exit(1);
        }
        Err(_) => {
            eprintln!("checker panic");
            std::process::exit(2);
        }
    }
}
