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
    let usage = "usage: pra-check DIRECTORY [--max-record-mib N]";
    if args.len() == 1 && matches!(args[0].as_str(), "--help" | "-h") {
        println!(
            "{usage}\nCheck every specification/object pair listed in DIRECTORY/modules.txt.\n\
             --max-record-mib N  Maximum size of each input record in MiB (default: 256)."
        );
        return Ok(());
    }
    let mut directory = None;
    let mut record_bytes = None;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        if arg == "--max-record-mib" {
            if record_bytes.is_some() {
                return Err("duplicate --max-record-mib option".into());
            }
            let mib = args
                .next()
                .and_then(|s| s.parse::<usize>().ok())
                .filter(|&n| n > 0)
                .ok_or("--max-record-mib requires a positive integer")?;
            record_bytes = Some(
                mib.checked_mul(1024 * 1024)
                    .ok_or("--max-record-mib exceeds the platform size limit")?,
            );
        } else if arg.starts_with('-') || directory.replace(arg).is_some() {
            return Err(usage.into());
        }
    }
    let Some(directory) = directory else {
        return Err(usage.into());
    };
    let start = Instant::now();
    let (t, n, p) = run(
        Path::new(directory),
        record_bytes.unwrap_or(parser::DEFAULT_LIMIT),
    )?;
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
