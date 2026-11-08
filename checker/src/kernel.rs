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

fn ensure(b: bool, msg: &str) -> Res<()> {
    if b {
        Ok(())
    } else {
        Err(msg.into())
    }
}

fn depth(d: usize) -> Res<usize> {
    d.checked_sub(1).ok_or("resource depth exhausted".into())
}

/// Check constructor categories and field counts before type checking.
pub fn shape(x: &R, category: &str, d: usize) -> Res<()> {
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
            ensure(matches!(**x, X::L(_)), "expected list")?;
            let cat = match category {
                "terms" => "term",
                "preds" => "pred",
                _ => "param",
            };
            for a in list(x) {
                shape(a, cat, d)?;
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
        "rec" => ("term", &["term", "term", "term"]),
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
        "andLeft" | "andRight" | "succInj" => ("proof", &["proof"]),
        "orLeft" | "orRight" | "falseElim" | "ascribe" => ("proof", &["pred", "proof"]),
        "orElim" => (
            "proof",
            &["name", "name", "pred", "proof", "proof", "proof"],
        ),
        "forallIntro" => ("proof", &["name", "pred", "proof"]),
        "forallElim" => ("proof", &["proof", "term"]),
        "existsIntro" => ("proof", &["pred", "term", "proof"]),
        "existsElim" => ("proof", &["name", "name", "pred", "proof", "proof"]),
        "hlet" => ("proof", &["name", "pred", "proof", "proof"]),
        "hletTerm" => ("proof", &["name", "term", "proof"]),
        "hletPred" => ("proof", &["name", "pred", "proof"]),
        "refl" | "succNeZero" => ("proof", &["term"]),
        "subst" => ("proof", &["pred", "proof", "proof"]),
        "lem" => ("proof", &["pred"]),
        "ind" => ("proof", &["name", "name", "pred", "proof", "proof", "term"]),
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
        shape(a, c, d)?;
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
        let mut changed = false;
        let ys = xs
            .iter()
            .enumerate()
            .map(|(i, a)| {
                let bind = matches!(tag, "tlam" | "plam") && i == 2 || tag == "tlet" && i == 3;
                let b = transform(a, tr, k + u64::from(bind));
                changed |= !Rc::ptr_eq(a, &b);
                b
            })
            .collect();
        if changed {
            Rc::new(X::L(ys))
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
    transform(x, &Transform::Inst(fs, ps), 0)
}

#[derive(Clone, Default)]
struct Ctx {
    locals: Vec<u64>,
    fs: Vec<u64>,
    ps: Vec<(u64, bool)>,
    hs: Vec<R>,
}

impl Ctx {
    fn local(&self, k: u64) -> Self {
        let mut c = self.clone();
        c.locals.insert(0, k);
        c.hs = c.hs.iter().map(shift).collect();
        c
    }

    fn hyp(&self, p: R) -> Self {
        let mut c = self.clone();
        c.hs.insert(0, p);
        c
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
                .ok_or("unbound local".into()),
            "tparam" => {
                c.fs.get(nat(&a[0]) as usize)
                    .copied()
                    .ok_or("unbound function parameter".into())
            }
            "zero" => Ok(0),
            "succ" => Ok(1),
            "tlam" => Ok(self.ti(&c.local(0), &a[1], d)? + 1),
            "tapp" => {
                let k = self.ti(c, &a[0], d)?;
                self.tc(c, &a[1], 0, d)?;
                k.checked_sub(1).ok_or("application of number".into())
            }
            "tlet" => {
                let k = self.ti(c, &a[1], d)?;
                self.ti(&c.local(k), &a[2], d)
            }
            "rec" => {
                self.tc(c, &a[0], 0, d)?;
                self.tc(c, &a[1], 2, d)?;
                self.tc(c, &a[2], 0, d)?;
                Ok(0)
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
                    .ok_or("unbound predicate parameter".into())
            }
            "plam" => {
                let (k, s) = self.pi(&c.local(0), &a[1], d)?;
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
                } else {
                    Ok(n2(op(x), f, a[1].clone()))
                }
            }
            "rec" => {
                let n = self.wh(&a[2], false, d)?;
                if op(&n) == "zero" {
                    self.wh(&a[0], false, d)
                } else if op(&n) == "tapp" && op(&fields(&n)[0]) == "succ" {
                    let m = fields(&n)[1].clone();
                    let r = node("rec", vec![a[0].clone(), a[1].clone(), m.clone()]);
                    self.wh(&n2("tapp", n2("tapp", a[1].clone(), m), r), false, d)
                } else {
                    Ok(node("rec", vec![a[0].clone(), a[1].clone(), n]))
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
            "rec" if op(&a[2]) == "zero" => self.expose(&a[0], p, d),
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
        let n = self.wh(&a[2], false, d)?;
        if op(&n) == "zero" {
            return self.expose(&a[0], false, d);
        }
        if op(&n) == "tapp" && op(&fields(&n)[0]) == "succ" {
            let m = fields(&n)[1].clone();
            let r = node("rec", vec![a[0].clone(), a[1].clone(), m.clone()]);
            self.expose(&n2("tapp", n2("tapp", a[1].clone(), m), r), false, d)
        } else {
            Ok(node("rec", vec![a[0].clone(), a[1].clone(), n]))
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
                "rec" if op(&a[2]) == "zero" && op(&b[2]) == "zero" => {
                    return self.eq(&a[0], &b[0], false, 0, d)
                }
                _ => {}
            }
        }
        let structural = (|| {
            if tag == "rec" && op(y) == "rec" {
                Ok(self.eq(&a[0], &b[0], false, 0, d)?
                    && self.eq(&a[1], &b[1], false, 2, d)?
                    && self.eq(&a[2], &b[2], false, 0, d)?)
            } else {
                self.spine(x, y, p, k, d)
            }
        })();
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
        let (l, r) = if tag == "rec" && op(y) == "rec" {
            (self.recstep(x, d + 1)?, self.recstep(y, d + 1)?)
        } else if tag == "rec" {
            (self.wh(x, false, d + 1)?, y.clone())
        } else if op(y) == "rec" {
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
        ensure(op(&p) == tag, &format!("expected {tag}, got {}", op(&p)))?;
        Ok(p)
    }

    fn hi(&self, c: &Ctx, h: &R, d: usize) -> Res<R> {
        let d = depth(d)?;
        let a = fields(h);
        match op(h) {
            "hyp" => {
                c.hs.get(nat(&a[0]) as usize)
                    .cloned()
                    .ok_or("unbound hypothesis".into())
            }
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
                let p = self.head(c, &a[0], "and", d)?;
                Ok(fields(&p)[usize::from(op(h) == "andRight")].clone())
            }
            "orLeft" | "orRight" => {
                self.form(c, &a[0], d)?;
                let p = self.hi(c, &a[1], d)?;
                Ok(if op(h) == "orLeft" {
                    n2("or", p, a[0].clone())
                } else {
                    n2("or", a[0].clone(), p)
                })
            }
            "orElim" => {
                self.form(c, &a[2], d)?;
                let p = self.head(c, &a[3], "or", d)?;
                self.check(&c.hyp(fields(&p)[0].clone()), &a[4], &a[2], d)?;
                self.check(&c.hyp(fields(&p)[1].clone()), &a[5], &a[2], d)?;
                Ok(a[2].clone())
            }
            "falseElim" => {
                self.form(c, &a[0], d)?;
                self.check(c, &a[1], &n0("false"), d)?;
                Ok(a[0].clone())
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
                self.form(c, &a[2], d)?;
                let p = self.head(c, &a[3], "ex", d)?;
                let cc = c.local(0).hyp(n2("papp", shift(&fields(&p)[0]), var(0)));
                self.check(&cc, &a[4], &shift(&a[2]), d)?;
                Ok(a[2].clone())
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
            "refl" => {
                self.tc(c, &a[0], 0, d)?;
                Ok(n2("eq", a[0].clone(), a[0].clone()))
            }
            "subst" => {
                self.pc(c, &a[0], (1, true), d)?;
                let e = self.head(c, &a[1], "eq", d)?;
                self.check(
                    c,
                    &a[2],
                    &n2("papp", a[0].clone(), fields(&e)[0].clone()),
                    d,
                )?;
                Ok(n2("papp", a[0].clone(), fields(&e)[1].clone()))
            }
            "succNeZero" => {
                self.tc(c, &a[0], 0, d)?;
                Ok(n2(
                    "imp",
                    n2("eq", n2("tapp", n0("succ"), a[0].clone()), n0("zero")),
                    n0("false"),
                ))
            }
            "succInj" => {
                let e = self.head(c, &a[0], "eq", d)?;
                let l = self.wh(&fields(&e)[0], false, d)?;
                let r = self.wh(&fields(&e)[1], false, d)?;
                ensure(
                    op(&l) == "tapp"
                        && op(&r) == "tapp"
                        && op(&fields(&l)[0]) == "succ"
                        && op(&fields(&r)[0]) == "succ",
                    "expected successors",
                )?;
                Ok(n2("eq", fields(&l)[1].clone(), fields(&r)[1].clone()))
            }
            "lem" => {
                self.form(c, &a[0], d)?;
                Ok(n2("or", a[0].clone(), n2("imp", a[0].clone(), n0("false"))))
            }
            "ind" => {
                self.pc(c, &a[2], (1, false), d)?;
                self.tc(c, &a[5], 0, d)?;
                self.check(c, &a[3], &n2("papp", a[2].clone(), n0("zero")), d)?;
                let m = shift(&a[2]);
                let cc = c.local(0).hyp(n2("papp", m.clone(), var(0)));
                self.check(
                    &cc,
                    &a[4],
                    &n2("papp", m, n2("tapp", n0("succ"), var(0))),
                    d,
                )?;
                Ok(n2("papp", a[2].clone(), a[5].clone()))
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
    1 + list(x).iter().map(count).sum::<usize>()
}
