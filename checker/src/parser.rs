//! Decode object records into constructor trees for the kernel.

use crate::syntax::{tree, Res, R, TAGS, X};
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader, Read};
use std::path::Path;
use std::rc::Rc;

pub(crate) const DEFAULT_LIMIT: usize = 256 * 1024 * 1024;

#[derive(PartialEq, Eq, Hash)]
enum Key {
    Number(u64),
    String(String),
    Empty,
    One(usize),
    Two([usize; 2]),
    Three([usize; 3]),
    Four([usize; 4]),
    List(Vec<usize>),
}

struct Span {
    start: usize,
    end: usize,
    height: usize,
    value: R,
}

struct Parser<'a> {
    data: &'a [u8],
    pos: usize,
    nodes: HashMap<Key, R>,
    spans: HashMap<[u8; 32], Span>,
    atoms: [Option<R>; TAGS.len()],
    numbers: [Option<R>; 32],
}

impl<'a> Parser<'a> {
    fn new(data: &'a [u8]) -> Self {
        Self {
            data,
            pos: 0,
            nodes: HashMap::new(),
            spans: HashMap::new(),
            atoms: std::array::from_fn(|_| None),
            numbers: std::array::from_fn(|_| None),
        }
    }

    fn intern(&mut self, value: X) -> R {
        let slot = match &value {
            X::A(tag) => Some(&mut self.atoms[*tag as usize]),
            X::N(n) if *n < self.numbers.len() as u64 => Some(&mut self.numbers[*n as usize]),
            _ => None,
        };
        if let Some(slot) = slot {
            return slot.get_or_insert_with(|| Rc::new(value)).clone();
        }
        // Children have already been interned. The cache keeps them alive for this record.
        let key = match &value {
            X::A(_) => unreachable!(),
            X::N(n) => Key::Number(*n),
            X::S(s) => Key::String(s.clone()),
            X::L(children) => {
                let id = |x: &R| Rc::as_ptr(x) as usize;
                match children.as_slice() {
                    [] => Key::Empty,
                    [a] => Key::One(id(a)),
                    [a, b] => Key::Two([id(a), id(b)]),
                    [a, b, c] => Key::Three([id(a), id(b), id(c)]),
                    [a, b, c, d] => Key::Four([id(a), id(b), id(c), id(d)]),
                    _ => Key::List(children.iter().map(id).collect()),
                }
            }
        };
        if let Some(node) = self.nodes.get(&key) {
            return node.clone();
        }
        let node = Rc::new(value);
        self.nodes.insert(key, node.clone());
        node
    }

    fn byte(&mut self) -> Res<u8> {
        let b = *self.data.get(self.pos).ok_or("truncated input")?;
        self.pos += 1;
        Ok(b)
    }

    fn vi(&mut self) -> Res<u64> {
        let mut n = 0u64;
        for i in 0..10 {
            let b = self.byte()?;
            if i == 9 && b > 1 {
                return Err("integer overflow".into());
            }
            n |= u64::from(b & 127) << (7 * i);
            if b < 128 {
                if i > 0 && b == 0 {
                    return Err("noncanonical integer".into());
                }
                return Ok(n);
            }
        }
        Err("integer overflow".into())
    }

    fn read(&mut self, d: usize) -> Res<(R, usize)> {
        if d == 0 {
            return Err("syntax depth exhausted".into());
        }
        let start = self.pos;
        let prefix: Option<[u8; 32]> = if self.data.get(start) == Some(&0) {
            self.data
                .get(start..start + 32)
                .map(|bytes| bytes.try_into().unwrap())
        } else {
            None
        };
        if let Some(span) = prefix.as_ref().and_then(|key| self.spans.get(key)) {
            let end = start + (span.end - span.start);
            // Reuse only a byte-for-byte match of a previously decoded complete value. The
            // prefix selects a candidate; it never establishes equality or skips depth checks.
            if self.data.get(start..end) == Some(&self.data[span.start..span.end]) {
                if span.height > d {
                    return Err("syntax depth exhausted".into());
                }
                self.pos = end;
                return Ok((span.value.clone(), span.height));
            }
        }
        let mut height = 1;
        let value = match self.byte()? {
            0 => {
                let n = usize::try_from(self.vi()?).map_err(|_| "length overflow")?;
                if n > self.data.len() - self.pos {
                    return Err("list exceeds frame".into());
                }
                let mut a = Vec::with_capacity(n);
                for _ in 0..n {
                    let (child, child_height) = self.read(d - 1)?;
                    height = height.max(child_height + 1);
                    a.push(child);
                }
                tree(a)
            }
            1 => {
                let n = usize::try_from(self.vi()?).map_err(|_| "length overflow")?;
                let end = self.pos.checked_add(n).ok_or("length overflow")?;
                let s = self.data.get(self.pos..end).ok_or("truncated string")?;
                let s = std::str::from_utf8(s)
                    .map_err(|_| "invalid UTF-8")?
                    .to_string();
                self.pos = end;
                X::S(s)
            }
            2 => X::N(self.vi()?),
            b if b >= 16 && (b - 16) < TAGS.len() as u8 => X::A(b - 16),
            _ => return Err("unknown object tag".into()),
        };
        let value = self.intern(value);
        if self.pos - start >= 32 {
            if let Some(prefix) = prefix {
                // Bound auxiliary storage for records containing many distinct subtrees.
                if self.spans.len() == 8192 {
                    self.spans.clear();
                }
                self.spans.insert(
                    prefix,
                    Span {
                        start,
                        end: self.pos,
                        height,
                        value: value.clone(),
                    },
                );
            }
        }
        Ok((value, height))
    }
}

fn parse(data: &[u8]) -> Res<R> {
    let mut p = Parser::new(data);
    let (r, _) = p.read(2048)?;
    if p.pos != data.len() {
        return Err("trailing data in record".into());
    }
    Ok(r)
}

pub(crate) struct Records {
    r: BufReader<File>,
    limit: usize,
    remaining: u64,
}

impl Records {
    pub(crate) fn open(p: &Path, limit: usize) -> Res<Self> {
        let mut r = BufReader::new(File::open(p).map_err(|e| format!("{}: {e}", p.display()))?);
        let size = r.get_ref().metadata().map_err(|e| e.to_string())?.len();
        let mut magic = [0; 4];
        r.read_exact(&mut magic).map_err(|e| e.to_string())?;
        if &magic != b"PRAO" {
            return Err("object magic".into());
        }
        Ok(Self {
            r,
            limit,
            remaining: size.saturating_sub(4),
        })
    }

    pub(crate) fn next(&mut self) -> Res<Option<R>> {
        if self.r.fill_buf().map_err(|e| e.to_string())?.is_empty() {
            return Ok(None);
        }
        let mut data = Vec::new();
        let mut len = Vec::new();
        loop {
            let mut b = [0];
            self.r.read_exact(&mut b).map_err(|_| "truncated frame")?;
            self.remaining = self.remaining.checked_sub(1).ok_or("truncated frame")?;
            len.push(b[0]);
            if b[0] < 128 {
                break;
            }
            if len.len() == 10 {
                return Err("frame overflow".into());
            }
        }
        let mut p = Parser::new(&len);
        let n = usize::try_from(p.vi()?).map_err(|_| "frame overflow")?;
        if n > self.limit {
            return Err(format!(
                "record too large: {n} bytes exceeds {}; use --max-record-mib to adjust the limit",
                self.limit
            ));
        }
        if n as u64 > self.remaining {
            return Err("truncated frame".into());
        }
        data.try_reserve_exact(n)
            .map_err(|e| format!("cannot allocate object record: {e}"))?;
        data.resize(n, 0);
        self.r
            .read_exact(&mut data)
            .map_err(|_| "truncated frame")?;
        self.remaining -= n as u64;
        parse(&data).map(Some)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::list;

    #[test]
    fn repeated_subtrees_share_storage() {
        let atom = 16 + TAGS.iter().position(|&tag| tag == "zero").unwrap() as u8;
        let tree = parse(&[0, 2, 0, 1, atom, 0, 1, atom]).unwrap();
        assert!(Rc::ptr_eq(&list(&tree)[0], &list(&tree)[1]));
        let different = parse(&[0, 2, 0, 1, atom, 0, 1, atom + 1]).unwrap();
        assert!(!Rc::ptr_eq(&list(&different)[0], &list(&different)[1]));
        assert_ne!(list(&different)[0], list(&different)[1]);
        for width in 0..7 {
            let mut child = vec![0, width];
            for n in 0..width {
                child.extend([2, n + 64]);
            }
            let mut bytes = vec![0, 2];
            bytes.extend(&child);
            bytes.extend(&child);
            let tree = parse(&bytes).unwrap();
            assert!(Rc::ptr_eq(&list(&tree)[0], &list(&tree)[1]));
        }
    }
}
