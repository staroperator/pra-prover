//! Type-check elaborated PRA declarations and proofs.
//! The environment stores definition bodies and theorem statements; proofs are checked during
//! admission and then dropped.

use crate::syntax::*;
use std::collections::HashMap;
use std::rc::Rc;

fn n0(t: &str) -> R {
    node(t, vec![])
}

fn n1(t: &str, a: R) -> R {
    node(t, vec![a])
}

fn n2(t: &str, a: R, b: R) -> R {
    node(t, vec![a, b])
}

fn var(i: u64) -> R {
    n1("tvar", num(i))
}

fn all(body: R) -> R {
    n1("all", n2("plam", n2("binder", n0("name"), num(0)), body))
}

fn is_rec_app(x: &R) -> bool {
    op(x) == "tapp" && op(&fields(x)[0]) == "rec"
}

fn ensure(b: bool, msg: &str) -> Res<()> {
    if b {
        Ok(())
    } else {
        Err(msg.into())
    }
}

fn depth(d: usize) -> Res<usize> {
    d.checked_sub(1)
        .ok_or_else(|| "resource depth exhausted".into())
}

/// Check constructor categories and field counts before type checking.
pub fn shape(x: &R, category: &'static str, d: usize) -> Res<()> {
    shape_cached(x, category, d, &mut HashMap::new())
}

// A successful check can be reused with at least as much remaining depth. The root keeps all
// pointer keys alive, and categories stay separate because a node can occur in different fields.
fn shape_cached(
    x: &R,
    category: &'static str,
    d: usize,
    cache: &mut HashMap<(usize, &'static str), usize>,
) -> Res<()> {
    let key = (Rc::as_ptr(x) as usize, category);
    let shared = matches!(**x, X::L(..)) && Rc::strong_count(x) > 1;
    if shared && cache.get(&key).is_some_and(|&checked| checked <= d) {
        return Ok(());
    }
    shape_visit(x, category, d, cache)?;
    if shared {
        cache.insert(key, d);
    }
    Ok(())
}

fn shape_visit(
    x: &R,
    category: &'static str,
    d: usize,
    cache: &mut HashMap<(usize, &'static str), usize>,
) -> Res<()> {
    let d = depth(d)?;
    match category {
        "nat" => {
            return ensure(
                matches!(**x, X::N(n) if n <= 1_000_000),
                "natural exceeds limit",
            )
        }
        "name" => {
            ensure(op(x) == "name", "expected structural name")?;
            for c in fields(x) {
                ensure(matches!(&**c, X::N(_) | X::S(_)), "name component")?;
            }
            return Ok(());
        }
        "terms" | "preds" | "params" => {
            ensure(matches!(**x, X::L(..)), "expected list")?;
            let cat = match category {
                "terms" => "term",
                "preds" => "pred",
                _ => "param",
            };
            for a in list(x) {
                shape_cached(a, cat, d, cache)?;
            }
            return Ok(());
        }
        "sort" => {
            return ensure(
                matches!(**x, X::A(i) if TAGS[i as usize] == "qf" || TAGS[i as usize] == "prop"),
                "sort",
            )
        }
        "bool" => return ensure(matches!(**x, X::N(0 | 1)), "binder visibility"),
        _ => {}
    }
    let (cat, args): (&str, &[&str]) = match op(x) {
        "binder" => ("binder", &["name", "bool"]),
        "sig" => ("sig", &["nat", "sort"]),
        "funparam" => ("param", &["binder", "nat"]),
        "predparam" => ("param", &["binder", "sig"]),
        "tvar" | "tparam" => ("term", &["nat"]),
        "zero" | "succ" => ("term", &[]),
        "tlam" => ("term", &["name", "term"]),
        "tapp" => ("term", &["term", "term"]),
        "tlet" => ("term", &["name", "term", "term"]),
        "rec" => ("term", &["term", "term"]),
        "tdef" => ("term", &["name", "terms"]),
        "false" | "true" => ("pred", &[]),
        "eq" => ("pred", &["term", "term"]),
        "imp" | "and" | "or" => ("pred", &["pred", "pred"]),
        "all" | "ex" => ("pred", &["pred"]),
        "pparam" => ("pred", &["nat"]),
        "plam" => ("pred", &["binder", "pred"]),
        "papp" => ("pred", &["pred", "term"]),
        "pletTerm" => ("pred", &["name", "term", "pred"]),
        "pletPred" => ("pred", &["name", "pred", "pred"]),
        "pdef" => ("pred", &["name", "terms", "preds"]),
        "hyp" => ("proof", &["nat"]),
        "trueIntro" => ("proof", &[]),
        "thm" => ("proof", &["name", "terms", "preds"]),
        "impIntro" => ("proof", &["name", "pred", "proof"]),
        "impElim" | "andIntro" => ("proof", &["proof", "proof"]),
        "andLeft" | "andRight" | "orLeft" | "orRight" => ("proof", &["pred", "pred"]),
        "falseElim" => ("proof", &["pred"]),
        "ascribe" => ("proof", &["pred", "proof"]),
        "orElim" => ("proof", &["pred", "pred", "pred"]),
        "forallIntro" => ("proof", &["name", "pred", "proof"]),
        "forallElim" => ("proof", &["proof", "term"]),
        "existsIntro" => ("proof", &["pred", "term", "proof"]),
        "existsElim" => ("proof", &["pred", "pred"]),
        "hlet" => ("proof", &["name", "pred", "proof", "proof"]),
        "hletTerm" => ("proof", &["name", "term", "proof"]),
        "hletPred" => ("proof", &["name", "pred", "proof"]),
        "refl" | "succNeZero" | "succInj" => ("proof", &[]),
        "subst" => ("proof", &["pred"]),
        "lem" => ("proof", &["pred"]),
        "ind" => ("proof", &["pred"]),
        "function" => ("decl", &["name", "params", "nat", "term"]),
        "predicate" => ("decl", &["name", "params", "sig", "pred"]),
        "theorem" if category == "spec" => ("spec", &["name", "params", "pred"]),
        "theorem" => ("decl", &["name", "params", "pred", "proof"]),
        _ => return Err(format!("unknown constructor {}", op(x))),
    };
    ensure(
        cat == category || (cat == "decl" && category == "spec"),
        "wrong syntax category",
    )?;
    ensure(
        fields(x).len() == args.len(),
        "wrong constructor field count",
    )?;
    for (a, c) in fields(x).iter().zip(args) {
        shape_cached(a, c, d, cache)?;
    }
    Ok(())
}

// Substitution increments depth at numerical lambdas and term lets; predicate and proof lets
// already have expanded bodies.
enum Transform<'a> {
    Shift(u64),
    Subst(&'a R),
    Inst(&'a [R], &'a [R]),
}

fn transform(x: &R, tr: &Transform, k: u64) -> R {
    transform_cached(x, tr, k, &mut HashMap::new())
}

// Substitution depends on binder depth. Keep sharing within this traversal, and drop the cache
// when it returns so previous proofs cannot accumulate in the environment.
fn transform_cached(x: &R, tr: &Transform, k: u64, cache: &mut HashMap<(usize, u64), R>) -> R {
    let key = (Rc::as_ptr(x) as usize, k);
    let shared = matches!(**x, X::L(..)) && Rc::strong_count(x) > 1;
    if shared {
        if let Some(value) = cache.get(&key) {
            return value.clone();
        }
    }
    let value = transform_visit(x, tr, k, cache);
    if shared {
        cache.insert(key, value.clone());
    }
    value
}

fn transform_visit(x: &R, tr: &Transform, k: u64, cache: &mut HashMap<(usize, u64), R>) -> R {
    let tag = op(x);
    if tag == "name" || tag == "binder" {
        return x.clone();
    }
    if tag == "tvar" {
        let i = nat(&fields(x)[0]);
        return match tr {
            Transform::Shift(n) if i >= k => var(i + n),
            Transform::Subst(a) if i == k => shift_by(a, k),
            Transform::Subst(_) if i > k => var(i - 1),
            _ => x.clone(),
        };
    }
    if let Transform::Inst(fs, ps) = tr {
        let actual = match tag {
            "tparam" => fs.get(nat(&fields(x)[0]) as usize),
            "pparam" => ps.get(nat(&fields(x)[0]) as usize),
            _ => None,
        };
        if let Some(a) = actual {
            return shift_by(a, k);
        }
    }
    if let X::L(xs) = &**x {
        let mut changed: Option<Vec<R>> = None;
        for (i, a) in xs.iter().enumerate() {
            let bind = matches!(tag, "tlam" | "plam") && i == 2 || tag == "tlet" && i == 3;
            let b = transform_cached(a, tr, k + u64::from(bind), cache);
            if let Some(ys) = &mut changed {
                ys.push(b);
            } else if !Rc::ptr_eq(a, &b) {
                let mut ys = Vec::with_capacity(xs.len());
                ys.extend(xs[..i].iter().cloned());
                ys.push(b);
                changed = Some(ys);
            }
        }
        if let Some(ys) = changed {
            Rc::new(tree(ys))
        } else {
            x.clone()
        }
    } else {
        x.clone()
    }
}

fn shift_by(x: &R, n: u64) -> R {
    if n == 0 {
        x.clone()
    } else {
        transform(x, &Transform::Shift(n), 0)
    }
}

fn shift(x: &R) -> R {
    shift_by(x, 1)
}

fn subst(x: &R, a: &R) -> R {
    transform(x, &Transform::Subst(a), 0)
}

fn inst(x: &R, fs: &[R], ps: &[R]) -> R {
    if fs.is_empty() && ps.is_empty() {
        x.clone()
    } else {
        transform(x, &Transform::Inst(fs, ps), 0)
    }
}

#[derive(Clone, Default)]
struct Ctx {
    locals: Vec<u64>,
    fs: Vec<u64>,
    ps: Vec<(u64, bool)>,
    // Each hypothesis stores the local-variable count at its introduction.
    hs: Vec<(usize, R)>,
}

impl Ctx {
    // Term and predicate checking uses variable and parameter arities without proof hypotheses.
    fn expression_local(&self, k: u64) -> Self {
        let mut locals = self.locals.clone();
        locals.insert(0, k);
        Self {
            locals,
            fs: self.fs.clone(),
            ps: self.ps.clone(),
            hs: Vec::new(),
        }
    }

    fn local(&self, k: u64) -> Self {
        let mut c = self.clone();
        c.locals.insert(0, k);
        c
    }

    fn hyp(&self, p: R) -> Self {
        let mut c = self.clone();
        c.hs.insert(0, (self.locals.len(), p));
        c
    }

    fn hypothesis(&self, index: usize) -> Res<R> {
        let (level, value) = self.hs.get(index).ok_or("unbound hypothesis")?;
        let distance = self
            .locals
            .len()
            .checked_sub(*level)
            .ok_or("hypothesis scope")?;
        Ok(shift_by(value, distance as u64))
    }
}

#[derive(Clone)]
struct Decl {
    kind: String,
    fs: Vec<u64>,
    ps: Vec<(u64, bool)>,
    sig: (u64, bool),
    value: R,
}

#[derive(Default)]
pub struct Kernel {
    env: HashMap<R, Decl>,
    pub admitted: usize,
    pub proof_nodes: usize,
}

fn signature(x: &R) -> (u64, bool) {
    (
        nat(&fields(x)[0]),
        matches!(*fields(x)[1], X::A(i) if TAGS[i as usize] == "prop"),
    )
}

impl Kernel {
    fn get(&self, n: &R, kind: &str) -> Res<&Decl> {
        let d = self
            .env
            .get(n)
            .ok_or_else(|| format!("unknown reference {n:?}"))?;
        ensure(d.kind == kind, "reference category")?;
        Ok(d)
    }

    fn ti(&self, c: &Ctx, t: &R, d: usize) -> Res<u64> {
        let d = depth(d)?;
        let a = fields(t);
        match op(t) {
            "tvar" => c
                .locals
                .get(nat(&a[0]) as usize)
                .copied()
                .ok_or_else(|| "unbound local".into()),
            "tparam" => {
                c.fs.get(nat(&a[0]) as usize)
                    .copied()
                    .ok_or_else(|| "unbound function parameter".into())
            }
            "zero" => Ok(0),
            "succ" => Ok(1),
            "tlam" => Ok(self.ti(&c.expression_local(0), &a[1], d)? + 1),
            "tapp" => {
                let k = self.ti(c, &a[0], d)?;
                self.tc(c, &a[1], 0, d)?;
                k.checked_sub(1)
                    .ok_or_else(|| "application of number".into())
            }
            "tlet" => {
                let k = self.ti(c, &a[1], d)?;
                self.ti(&c.expression_local(k), &a[2], d)
            }
            "rec" => {
                self.tc(c, &a[0], 0, d)?;
                self.tc(c, &a[1], 2, d)?;
                Ok(1)
            }
            "tdef" => {
                let e = self.get(&a[0], "function")?;
                self.args(c, e, list(&a[1]), &[], d)?;
                Ok(e.sig.0)
            }
            _ => Err("term constructor".into()),
        }
    }

    fn tc(&self, c: &Ctx, t: &R, k: u64, d: usize) -> Res<()> {
        ensure(self.ti(c, t, d)? == k, "term arity")
    }

    fn pi(&self, c: &Ctx, p: &R, d: usize) -> Res<(u64, bool)> {
        let d = depth(d)?;
        let a = fields(p);
        match op(p) {
            "false" | "true" => Ok((0, false)),
            "eq" => {
                self.tc(c, &a[0], 0, d)?;
                self.tc(c, &a[1], 0, d)?;
                Ok((0, false))
            }
            "imp" | "and" | "or" => {
                let l = self.form(c, &a[0], d)?;
                let r = self.form(c, &a[1], d)?;
                Ok((0, l || r))
            }
            "all" | "ex" => {
                self.pc(c, &a[0], (1, true), d)?;
                Ok((0, true))
            }
            "pparam" => {
                c.ps.get(nat(&a[0]) as usize)
                    .copied()
                    .ok_or_else(|| "unbound predicate parameter".into())
            }
            "plam" => {
                let (k, s) = self.pi(&c.expression_local(0), &a[1], d)?;
                Ok((k + 1, s))
            }
            "papp" => {
                let (k, s) = self.pi(c, &a[0], d)?;
                self.tc(c, &a[1], 0, d)?;
                Ok((k.checked_sub(1).ok_or("application of formula")?, s))
            }
            "pletTerm" => {
                self.ti(c, &a[1], d)?;
                self.pi(c, &a[2], d)
            }
            "pletPred" => {
                self.pi(c, &a[1], d)?;
                self.pi(c, &a[2], d)
            }
            "pdef" => {
                let e = self.get(&a[0], "predicate")?;
                self.args(c, e, list(&a[1]), list(&a[2]), d)?;
                Ok(e.sig)
            }
            _ => Err("predicate constructor".into()),
        }
    }

    fn pc(&self, c: &Ctx, p: &R, s: (u64, bool), d: usize) -> Res<()> {
        let a = self.pi(c, p, d)?;
        ensure(a.0 == s.0 && (s.1 || !a.1), "predicate arity or sort")
    }

    fn form(&self, c: &Ctx, p: &R, d: usize) -> Res<bool> {
        let (k, s) = self.pi(c, p, d)?;
        ensure(k == 0, "formula arity")?;
        Ok(s)
    }

    fn args(&self, c: &Ctx, e: &Decl, fs: &[R], ps: &[R], d: usize) -> Res<()> {
        ensure(
            fs.len() == e.fs.len() && ps.len() == e.ps.len(),
            "argument count",
        )?;
        for (a, k) in fs.iter().zip(&e.fs) {
            self.tc(c, a, *k, d)?;
        }
        for (a, k) in ps.iter().zip(&e.ps) {
            self.pc(c, a, *k, d)?;
        }
        Ok(())
    }

    fn wh(&self, x: &R, pred: bool, d: usize) -> Res<R> {
        let d = depth(d)?;
        let a = fields(x);
        match op(x) {
            "tdef" => self.wh(
                &inst(&self.get(&a[0], "function")?.value, list(&a[1]), &[]),
                false,
                d,
            ),
            "pdef" => self.wh(
                &inst(
                    &self.get(&a[0], "predicate")?.value,
                    list(&a[1]),
                    list(&a[2]),
                ),
                true,
                d,
            ),
            "tlet" => self.wh(&subst(&a[2], &a[1]), false, d),
            "pletTerm" | "pletPred" => self.wh(&a[2], true, d),
            "tapp" | "papp" => {
                let f = self.wh(&a[0], pred, d)?;
                if matches!(op(&f), "tlam" | "plam") {
                    self.wh(&subst(&fields(&f)[1], &a[1]), pred, d)
                } else if !pred && op(&f) == "rec" {
                    let rec = fields(&f);
                    let n = self.wh(&a[1], false, d)?;
                    if op(&n) == "zero" {
                        self.wh(&rec[0], false, d)
                    } else if op(&n) == "tapp" && op(&fields(&n)[0]) == "succ" {
                        let m = fields(&n)[1].clone();
                        let r = n2("tapp", f.clone(), m.clone());
                        self.wh(&n2("tapp", n2("tapp", rec[1].clone(), m), r), false, d)
                    } else if Rc::ptr_eq(&f, &a[0]) && Rc::ptr_eq(&n, &a[1]) {
                        Ok(x.clone())
                    } else {
                        Ok(n2("tapp", f, n))
                    }
                } else if Rc::ptr_eq(&f, &a[0]) {
                    Ok(x.clone())
                } else {
                    Ok(n2(op(x), f, a[1].clone()))
                }
            }
            _ => Ok(x.clone()),
        }
    }

    fn expose(&self, x: &R, p: bool, d: usize) -> Res<R> {
        let d = depth(d)?;
        let a = fields(x);
        match op(x) {
            "tlet" => self.expose(&subst(&a[2], &a[1]), p, d),
            "pletTerm" | "pletPred" => self.expose(&a[2], p, d),
            "tapp" if op(&a[0]) == "rec" && op(&a[1]) == "zero" => {
                self.expose(&fields(&a[0])[0], p, d)
            }
            "tapp" | "papp" => {
                let f = self.expose(&a[0], p, d)?;
                if matches!(op(&f), "tlam" | "plam") {
                    self.expose(&subst(&fields(&f)[1], &a[1]), p, d)
                } else if f == a[0] {
                    Ok(x.clone())
                } else {
                    Ok(n2(op(x), f, a[1].clone()))
                }
            }
            _ => Ok(x.clone()),
        }
    }

    fn unfold(&self, x: &R) -> Res<R> {
        let a = fields(x);
        match op(x) {
            "tdef" => Ok(inst(&self.get(&a[0], "function")?.value, list(&a[1]), &[])),
            "pdef" => Ok(inst(
                &self.get(&a[0], "predicate")?.value,
                list(&a[1]),
                list(&a[2]),
            )),
            "tapp" | "papp" => {
                let f = self.unfold(&a[0])?;
                if f == a[0] {
                    Ok(x.clone())
                } else {
                    Ok(n2(op(x), f, a[1].clone()))
                }
            }
            _ => Ok(x.clone()),
        }
    }

    fn eqargs(&self, e: &Decl, a: &[R], b: &[R], p: &[R], q: &[R], d: usize) -> Res<bool> {
        if a.len() != b.len()
            || a.len() != e.fs.len()
            || p.len() != q.len()
            || p.len() != e.ps.len()
        {
            return Ok(false);
        }
        for ((x, y), k) in a.iter().zip(b).zip(&e.fs) {
            if !self.eq(x, y, false, *k, d)? {
                return Ok(false);
            }
        }
        for ((x, y), k) in p.iter().zip(q).zip(&e.ps) {
            if !self.eq(x, y, true, k.0, d)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn spine(&self, x: &R, y: &R, p: bool, k: u64, d: usize) -> Res<bool> {
        let d = depth(d)?;
        if x == y {
            return Ok(true);
        }
        let a = fields(x);
        let b = fields(y);
        if op(x) != op(y) {
            return Ok(false);
        }
        match op(x) {
            "tapp" | "papp" => {
                Ok(self.spine(&a[0], &b[0], p, k + 1, d)? && self.eq(&a[1], &b[1], false, 0, d)?)
            }
            "rec" => Ok(self.eq(&a[0], &b[0], false, 0, d)? && self.eq(&a[1], &b[1], false, 2, d)?),
            "tdef" if a[0] == b[0] => self.eqargs(
                self.get(&a[0], "function")?,
                list(&a[1]),
                list(&b[1]),
                &[],
                &[],
                d,
            ),
            "pdef" if a[0] == b[0] => self.eqargs(
                self.get(&a[0], "predicate")?,
                list(&a[1]),
                list(&b[1]),
                list(&a[2]),
                list(&b[2]),
                d,
            ),
            _ => Ok(false),
        }
    }

    fn recstep(&self, x: &R, d: usize) -> Res<R> {
        let a = fields(x);
        let rec = fields(&a[0]);
        let n = self.wh(&a[1], false, d)?;
        if op(&n) == "zero" {
            return self.expose(&rec[0], false, d);
        }
        if op(&n) == "tapp" && op(&fields(&n)[0]) == "succ" {
            let m = fields(&n)[1].clone();
            let r = n2("tapp", a[0].clone(), m.clone());
            self.expose(&n2("tapp", n2("tapp", rec[1].clone(), m), r), false, d)
        } else if Rc::ptr_eq(&n, &a[1]) {
            Ok(x.clone())
        } else {
            Ok(n2("tapp", a[0].clone(), n))
        }
    }

    fn eq(&self, x: &R, y: &R, p: bool, k: u64, d: usize) -> Res<bool> {
        let d = depth(d)?;
        if x == y {
            return Ok(true);
        }
        let a = fields(x);
        let b = fields(y);
        let tag = op(x);
        if tag == op(y) {
            match tag {
                "tvar" | "tparam" | "pparam" => return Ok(false),
                "tlam" | "plam" => {
                    return if k > 0 {
                        self.eq(&a[1], &b[1], p, k - 1, d)
                    } else {
                        Ok(false)
                    }
                }
                "eq" => {
                    return Ok(self.eq(&a[0], &b[0], false, 0, d)?
                        && self.eq(&a[1], &b[1], false, 0, d)?)
                }
                "imp" | "and" | "or" => {
                    return Ok(
                        self.eq(&a[0], &b[0], true, 0, d)? && self.eq(&a[1], &b[1], true, 0, d)?
                    )
                }
                "all" | "ex" => return self.eq(&a[0], &b[0], true, 1, d),
                "tapp"
                    if is_rec_app(x)
                        && is_rec_app(y)
                        && op(&a[1]) == "zero"
                        && op(&b[1]) == "zero" =>
                {
                    return self.eq(&fields(&a[0])[0], &fields(&b[0])[0], false, 0, d)
                }
                _ => {}
            }
        }
        let structural = self.spine(x, y, p, k, d);
        if matches!(structural, Ok(true)) {
            return Ok(true);
        }
        if k > 0 {
            let app = if p { "papp" } else { "tapp" };
            return self.eq(
                &n2(app, shift(x), var(0)),
                &n2(app, shift(y), var(0)),
                p,
                k - 1,
                d,
            );
        }
        let l = self.expose(x, p, d + 1)?;
        let r = self.expose(y, p, d + 1)?;
        if l != *x || r != *y {
            return self.eq(&l, &r, p, 0, d);
        }
        let l = self.unfold(x)?;
        let r = self.unfold(y)?;
        if l != *x || r != *y {
            return self.eq(&l, &r, p, 0, d);
        }
        let (l, r) = if is_rec_app(x) && is_rec_app(y) {
            (self.recstep(x, d + 1)?, self.recstep(y, d + 1)?)
        } else if is_rec_app(x) {
            (self.wh(x, false, d + 1)?, y.clone())
        } else if is_rec_app(y) {
            (x.clone(), self.wh(y, false, d + 1)?)
        } else {
            return structural;
        };
        if l == *x && r == *y {
            structural
        } else {
            self.eq(&l, &r, p, 0, d)
        }
    }

    fn check(&self, c: &Ctx, h: &R, p: &R, d: usize) -> Res<()> {
        let actual = self.hi(c, h, depth(d)?)?;
        ensure(self.eq(&actual, p, true, 0, d)?, "proof type mismatch")
    }

    fn head(&self, c: &Ctx, h: &R, tag: &str, d: usize) -> Res<R> {
        let p = self.wh(&self.hi(c, h, d)?, true, d)?;
        if op(&p) != tag {
            return Err(format!("expected {tag}, got {}", op(&p)));
        }
        Ok(p)
    }

    fn hi(&self, c: &Ctx, h: &R, d: usize) -> Res<R> {
        let d = depth(d)?;
        let a = fields(h);
        match op(h) {
            "hyp" => c.hypothesis(nat(&a[0]) as usize),
            "trueIntro" => Ok(n0("true")),
            "thm" => {
                let e = self.get(&a[0], "theorem")?;
                self.args(c, e, list(&a[1]), list(&a[2]), d)?;
                Ok(inst(&e.value, list(&a[1]), list(&a[2])))
            }
            "impIntro" => {
                self.form(c, &a[1], d)?;
                Ok(n2(
                    "imp",
                    a[1].clone(),
                    self.hi(&c.hyp(a[1].clone()), &a[2], d)?,
                ))
            }
            "impElim" => {
                let p = self.head(c, &a[0], "imp", d)?;
                self.check(c, &a[1], &fields(&p)[0], d)?;
                Ok(fields(&p)[1].clone())
            }
            "andIntro" => Ok(n2("and", self.hi(c, &a[0], d)?, self.hi(c, &a[1], d)?)),
            "andLeft" | "andRight" => {
                self.form(c, &a[0], d)?;
                self.form(c, &a[1], d)?;
                Ok(n2(
                    "imp",
                    n2("and", a[0].clone(), a[1].clone()),
                    a[usize::from(op(h) == "andRight")].clone(),
                ))
            }
            "orLeft" | "orRight" => {
                self.form(c, &a[0], d)?;
                self.form(c, &a[1], d)?;
                Ok(n2(
                    "imp",
                    a[usize::from(op(h) == "orRight")].clone(),
                    n2("or", a[0].clone(), a[1].clone()),
                ))
            }
            "orElim" => {
                for p in a {
                    self.form(c, p, d)?;
                }
                Ok(n2(
                    "imp",
                    n2("or", a[0].clone(), a[1].clone()),
                    n2(
                        "imp",
                        n2("imp", a[0].clone(), a[2].clone()),
                        n2("imp", n2("imp", a[1].clone(), a[2].clone()), a[2].clone()),
                    ),
                ))
            }
            "falseElim" => {
                self.form(c, &a[0], d)?;
                Ok(n2("imp", n0("false"), a[0].clone()))
            }
            "forallIntro" => {
                self.pc(c, &a[1], (1, true), d)?;
                self.check(&c.local(0), &a[2], &n2("papp", shift(&a[1]), var(0)), d)?;
                Ok(n1("all", a[1].clone()))
            }
            "forallElim" => {
                self.tc(c, &a[1], 0, d)?;
                let p = self.head(c, &a[0], "all", d)?;
                Ok(n2("papp", fields(&p)[0].clone(), a[1].clone()))
            }
            "existsIntro" => {
                self.pc(c, &a[0], (1, true), d)?;
                self.tc(c, &a[1], 0, d)?;
                self.check(c, &a[2], &n2("papp", a[0].clone(), a[1].clone()), d)?;
                Ok(n1("ex", a[0].clone()))
            }
            "existsElim" => {
                self.pc(c, &a[0], (1, true), d)?;
                self.form(c, &a[1], d)?;
                Ok(n2(
                    "imp",
                    n1("ex", a[0].clone()),
                    n2(
                        "imp",
                        all(n2("imp", n2("papp", shift(&a[0]), var(0)), shift(&a[1]))),
                        a[1].clone(),
                    ),
                ))
            }
            "hlet" => {
                self.form(c, &a[1], d)?;
                self.check(c, &a[2], &a[1], d)?;
                self.hi(&c.hyp(a[1].clone()), &a[3], d)
            }
            "hletTerm" => {
                self.ti(c, &a[1], d)?;
                self.hi(c, &a[2], d)
            }
            "hletPred" => {
                self.pi(c, &a[1], d)?;
                self.hi(c, &a[2], d)
            }
            "ascribe" => {
                self.form(c, &a[0], d)?;
                self.check(c, &a[1], &a[0], d)?;
                Ok(a[0].clone())
            }
            "refl" => Ok(all(n2("eq", var(0), var(0)))),
            "subst" => {
                self.pc(c, &a[0], (1, true), d)?;
                let motive = shift(&shift(&a[0]));
                Ok(all(all(n2(
                    "imp",
                    n2("eq", var(1), var(0)),
                    n2(
                        "imp",
                        n2("papp", motive.clone(), var(1)),
                        n2("papp", motive, var(0)),
                    ),
                ))))
            }
            "succNeZero" => Ok(all(n2(
                "imp",
                n2("eq", n2("tapp", n0("succ"), var(0)), n0("zero")),
                n0("false"),
            ))),
            "succInj" => Ok(all(all(n2(
                "imp",
                n2(
                    "eq",
                    n2("tapp", n0("succ"), var(1)),
                    n2("tapp", n0("succ"), var(0)),
                ),
                n2("eq", var(1), var(0)),
            )))),
            "lem" => {
                self.form(c, &a[0], d)?;
                Ok(n2("or", a[0].clone(), n2("imp", a[0].clone(), n0("false"))))
            }
            "ind" => {
                self.pc(c, &a[0], (1, false), d)?;
                let motive = shift(&a[0]);
                Ok(n2(
                    "imp",
                    n2("papp", a[0].clone(), n0("zero")),
                    n2(
                        "imp",
                        all(n2(
                            "imp",
                            n2("papp", motive.clone(), var(0)),
                            n2("papp", motive, n2("tapp", n0("succ"), var(0))),
                        )),
                        n1("all", a[0].clone()),
                    ),
                ))
            }
            _ => Err("proof constructor".into()),
        }
    }

    pub fn admit(&mut self, x: &R) -> Res<()> {
        shape(x, "decl", 2048)?;
        let a = fields(x);
        ensure(!self.env.contains_key(&a[0]), "duplicate declaration")?;
        let mut c = Ctx::default();
        for p in list(&a[1]) {
            if op(p) == "funparam" {
                c.fs.push(nat(&fields(p)[1]))
            } else {
                c.ps.push(signature(&fields(p)[1]))
            }
        }
        let (sig, value) = match op(x) {
            "function" => {
                ensure(c.ps.is_empty(), "function has predicate parameters")?;
                let k = nat(&a[2]);
                self.tc(&c, &a[3], k, 2048)?;
                ((k, false), a[3].clone())
            }
            "predicate" => {
                let s = signature(&a[2]);
                self.pc(&c, &a[3], s, 2048)?;
                (s, a[3].clone())
            }
            "theorem" => {
                self.form(&c, &a[2], 2048)?;
                self.check(&c, &a[3], &a[2], 2048)?;
                self.proof_nodes += count(&a[3]);
                ((0, true), a[2].clone())
            }
            _ => return Err("declaration constructor".into()),
        };
        self.env.insert(
            a[0].clone(),
            Decl {
                kind: op(x).into(),
                fs: c.fs,
                ps: c.ps,
                sig,
                value,
            },
        );
        self.admitted += 1;
        Ok(())
    }
}

pub fn count(x: &R) -> usize {
    fn visit(x: &R, cache: &mut HashMap<usize, usize>) -> usize {
        let key = Rc::as_ptr(x) as usize;
        let shared = matches!(**x, X::L(..)) && Rc::strong_count(x) > 1;
        if shared {
            if let Some(&size) = cache.get(&key) {
                return size;
            }
        }
        let size = 1 + list(x)
            .iter()
            .map(|child| visit(child, cache))
            .sum::<usize>();
        if shared {
            cache.insert(key, size);
        }
        size
    }
    visit(x, &mut HashMap::new())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lambdas(depth: u64, mut body: R) -> R {
        for _ in 0..depth {
            body = n2("tlam", n0("name"), body);
        }
        body
    }

    #[test]
    fn hypotheses_use_their_introduction_scope() {
        let outer = Ctx::default().local(0).hyp(n2("eq", var(0), n0("zero")));
        let inner = outer
            .local(0)
            .hyp(n2("eq", var(0), var(1)))
            .local(0)
            .local(0);
        assert_eq!(inner.hypothesis(0).unwrap(), n2("eq", var(2), var(3)));
        assert_eq!(inner.hypothesis(1).unwrap(), n2("eq", var(3), n0("zero")));
        assert_eq!(outer.hypothesis(0).unwrap(), n2("eq", var(0), n0("zero")));
        assert!(inner.hypothesis(2).is_err());
    }

    #[test]
    fn substitution_respects_nested_binders() {
        for depth in 0..5 {
            for index in 0..9 {
                let term = lambdas(depth, var(index));
                let shifted = if index < depth { index } else { index + 2 };
                assert_eq!(shift_by(&term, 2), lambdas(depth, var(shifted)));
                for actual in 0..4 {
                    let replaced = if index < depth {
                        index
                    } else if index == depth {
                        actual + depth
                    } else {
                        index - 1
                    };
                    assert_eq!(subst(&term, &var(actual)), lambdas(depth, var(replaced)));
                }
            }
            let formal = lambdas(depth, n1("tparam", num(0)));
            assert_eq!(
                inst(&formal, &[var(3)], &[]),
                lambdas(depth, var(3 + depth))
            );
        }
    }

    #[test]
    fn substitution_respects_let_and_predicate_scopes() {
        let term = node("tlet", vec![n0("name"), var(0), var(1)]);
        assert_eq!(
            subst(&term, &var(2)),
            node("tlet", vec![n0("name"), var(2), var(3)])
        );
        let binder = node("binder", vec![n0("name"), num(0)]);
        let formal = n2("plam", binder.clone(), n1("pparam", num(0)));
        let actual = n2("eq", var(0), n0("zero"));
        assert_eq!(
            inst(&formal, &[], &[actual]),
            n2("plam", binder, n2("eq", var(1), n0("zero")))
        );
        let expanded = node(
            "pletTerm",
            vec![n0("name"), var(0), n2("eq", var(0), var(1))],
        );
        assert_eq!(
            subst(&expanded, &n0("zero")),
            node(
                "pletTerm",
                vec![n0("name"), n0("zero"), n2("eq", n0("zero"), var(0))]
            )
        );
    }
}
