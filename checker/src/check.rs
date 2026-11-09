//! Match module specifications with their object files and admit declarations in dependency order.

use crate::kernel::{shape, Kernel};
use crate::parser::Records;
use crate::spec::Specifications;
use crate::syntax::{fields, node, op, Res};
use std::path::Path;
use std::time::{Duration, Instant};

#[derive(Default)]
pub(crate) struct Timings {
    pub(crate) spec: Duration,
    pub(crate) full: Duration,
    pub(crate) matching: Duration,
    pub(crate) checking: Duration,
}

pub(crate) fn run(dir: &Path, record_bytes: usize) -> Res<(Timings, usize, usize)> {
    let order = std::fs::read_to_string(dir.join("modules.txt")).map_err(|e| e.to_string())?;
    let mut kernel = Kernel::default();
    let mut times = Timings::default();
    let mut count = 0;
    let mut seen = std::collections::HashSet::new();
    for m in order.lines() {
        if m.split('.').any(str::is_empty) || m.contains('/') || m.contains('\\') || m.contains(':')
        {
            return Err("module path".into());
        }
        if !seen.insert(m) {
            return Err("duplicate module".into());
        }
        let base = dir.join(m.replace('.', "/"));
        let mut spec = Specifications::open(&base.with_extension("pra"), record_bytes)?;
        let mut full = Records::open(&base.with_extension("prao"), record_bytes)?;
        let mut i = 0;
        loop {
            let start = Instant::now();
            let s = spec.next()?;
            times.spec += start.elapsed();
            let start = Instant::now();
            let f = full.next()?;
            times.full += start.elapsed();
            let (s, f) = match (s, f) {
                (None, None) => break,
                (Some(s), Some(f)) => (s, f),
                _ => {
                    return Err(format!(
                        "{m}, declaration {i}: specification/object length mismatch"
                    ))
                }
            };
            let start = Instant::now();
            shape(&s, "spec", 2048)?;
            let projection = if op(&f) == "theorem" && fields(&f).len() == 4 {
                node("theorem", fields(&f)[..3].to_vec())
            } else {
                f.clone()
            };
            if s != projection {
                return Err(format!("{m}, declaration {i}: specification mismatch"));
            }
            times.matching += start.elapsed();
            let start = Instant::now();
            kernel
                .admit(&f)
                .map_err(|e| format!("{m}, declaration {i}, {:?}: {e}", fields(&f)[0]))?;
            times.checking += start.elapsed();
            count += 1;
            i += 1;
        }
    }
    if count == 0 {
        return Err("empty corpus".into());
    }
    Ok((times, count, kernel.proof_nodes))
}
