//! Constructor trees and tags shared by the parsers, specification matching, and the kernel.

use std::rc::Rc;

pub(crate) type R = Rc<X>;
pub(crate) type Res<T> = Result<T, String>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum X {
    A(u8),
    N(u64),
    S(String),
    L(Vec<R>),
}

pub(crate) const TAGS: &[&str] = &[
    "name",
    "binder",
    "sig",
    "qf",
    "prop",
    "funparam",
    "predparam",
    "tvar",
    "tparam",
    "zero",
    "succ",
    "tlam",
    "tapp",
    "tlet",
    "rec",
    "tdef",
    "false",
    "true",
    "eq",
    "imp",
    "and",
    "or",
    "all",
    "ex",
    "pparam",
    "plam",
    "papp",
    "pletTerm",
    "pletPred",
    "pdef",
    "hyp",
    "trueIntro",
    "thm",
    "impIntro",
    "impElim",
    "andIntro",
    "andLeft",
    "andRight",
    "orLeft",
    "orRight",
    "orElim",
    "falseElim",
    "forallIntro",
    "forallElim",
    "existsIntro",
    "existsElim",
    "hlet",
    "hletTerm",
    "hletPred",
    "ascribe",
    "refl",
    "subst",
    "succNeZero",
    "succInj",
    "lem",
    "ind",
    "function",
    "predicate",
    "theorem",
];

pub(crate) fn list(x: &R) -> &[R] {
    if let X::L(xs) = &**x {
        xs
    } else {
        &[]
    }
}

pub(crate) fn op(x: &R) -> &str {
    match list(x).first().map(|x| &**x) {
        Some(X::A(i)) => TAGS[*i as usize],
        _ => "",
    }
}

pub(crate) fn fields(x: &R) -> &[R] {
    &list(x)[1..]
}

pub(crate) fn nat(x: &R) -> u64 {
    if let X::N(n) = **x {
        n
    } else {
        panic!("validated natural")
    }
}

pub(crate) fn num(n: u64) -> R {
    Rc::new(X::N(n))
}

pub(crate) fn node(tag: &str, xs: Vec<R>) -> R {
    let mut out = vec![Rc::new(X::A(
        TAGS.iter().position(|x| *x == tag).unwrap() as u8
    ))];
    out.extend(xs);
    Rc::new(tree(out))
}

pub(crate) fn tree(xs: Vec<R>) -> X {
    X::L(xs)
}
