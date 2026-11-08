//! Decode object records into constructor trees for the kernel.

use crate::syntax::{Res, R, TAGS, X};
use std::fs::File;
use std::io::{BufRead, BufReader, Read};
use std::path::Path;
use std::rc::Rc;

pub(crate) const LIMIT: usize = 256 * 1024 * 1024;

struct Parser<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> Parser<'a> {
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

    fn read(&mut self, d: usize) -> Res<R> {
        if d == 0 {
            return Err("syntax depth exhausted".into());
        }
        Ok(Rc::new(match self.byte()? {
            0 => {
                let n = usize::try_from(self.vi()?).map_err(|_| "length overflow")?;
                if n > self.data.len() - self.pos {
                    return Err("list exceeds frame".into());
                }
                let mut a = Vec::with_capacity(n);
                for _ in 0..n {
                    a.push(self.read(d - 1)?)
                }
                X::L(a)
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
        }))
    }
}

fn parse(data: &[u8]) -> Res<R> {
    let mut p = Parser { data, pos: 0 };
    let r = p.read(2048)?;
    if p.pos != data.len() {
        return Err("trailing data in record".into());
    }
    Ok(r)
}

pub(crate) struct Records {
    r: BufReader<File>,
}

impl Records {
    pub(crate) fn open(p: &Path) -> Res<Self> {
        let mut r = BufReader::new(File::open(p).map_err(|e| format!("{}: {e}", p.display()))?);
        let mut magic = [0; 4];
        r.read_exact(&mut magic).map_err(|e| e.to_string())?;
        if &magic != b"PRAO" {
            return Err("object magic".into());
        }
        Ok(Self { r })
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
            len.push(b[0]);
            if b[0] < 128 {
                break;
            }
            if len.len() == 10 {
                return Err("frame overflow".into());
            }
        }
        let mut p = Parser { data: &len, pos: 0 };
        let n = usize::try_from(p.vi()?).map_err(|_| "frame overflow")?;
        if n > LIMIT {
            return Err("record too large".into());
        }
        data.resize(n, 0);
        self.r
            .read_exact(&mut data)
            .map_err(|_| "truncated frame")?;
        parse(&data).map(Some)
    }
}
