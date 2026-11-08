//! Parse readable specifications into the same constructor trees as object declarations.

use crate::parser::LIMIT;
use crate::syntax::{node, num, Res, R, TAGS, X};
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;
use std::rc::Rc;

#[derive(Clone, PartialEq)]
enum Token {
    Word(String),
    String(String),
    Number(u64),
    Symbol(String),
    End,
}

struct Lexer<'a> {
    data: &'a [u8],
    pos: usize,
    look: Option<Token>,
}

impl Lexer<'_> {
    fn byte(&mut self) -> Res<u8> {
        let b = *self.data.get(self.pos).ok_or("truncated input")?;
        self.pos += 1;
        Ok(b)
    }

    fn hex4(&mut self) -> Res<u32> {
        let mut n = 0;
        for _ in 0..4 {
            n = 16 * n + (self.byte()? as char).to_digit(16).ok_or("bad escape")?;
        }
        Ok(n)
    }

    fn string(&mut self) -> Res<String> {
        let mut s = Vec::new();
        loop {
            match self.byte()? {
                b'"' => return String::from_utf8(s).map_err(|_| "invalid UTF-8".into()),
                b'\\' => match self.byte()? {
                    b'"' => s.push(b'"'),
                    b'\\' => s.push(b'\\'),
                    b'/' => s.push(b'/'),
                    b'n' => s.push(b'\n'),
                    b'r' => s.push(b'\r'),
                    b't' => s.push(b'\t'),
                    b'b' => s.push(8),
                    b'f' => s.push(12),
                    b'u' => {
                        let mut n = self.hex4()?;
                        if (0xd800..=0xdbff).contains(&n) {
                            if self.byte()? != b'\\' || self.byte()? != b'u' {
                                return Err("surrogate".into());
                            }
                            let low = self.hex4()?;
                            if !(0xdc00..=0xdfff).contains(&low) {
                                return Err("surrogate".into());
                            }
                            n = 0x10000 + (n - 0xd800) * 1024 + low - 0xdc00;
                        }
                        let c = char::from_u32(n).ok_or("invalid unicode")?;
                        s.extend(c.encode_utf8(&mut [0; 4]).as_bytes());
                    }
                    _ => return Err("invalid escape".into()),
                },
                b if b < 32 => return Err("control character in string".into()),
                b => s.push(b),
            }
        }
    }

    fn read(&mut self) -> Res<Token> {
        loop {
            while self.data.get(self.pos).is_some_and(u8::is_ascii_whitespace) {
                self.pos += 1;
            }
            if self.data.get(self.pos..self.pos + 2) == Some(b"--") {
                while self.data.get(self.pos).is_some_and(|b| *b != b'\n') {
                    self.pos += 1;
                }
            } else {
                break;
            }
        }
        let Some(&b) = self.data.get(self.pos) else {
            return Ok(Token::End);
        };
        self.pos += 1;
        if b == b'"' {
            return self.string().map(Token::String);
        }
        if b.is_ascii_digit() {
            let mut n = u64::from(b - b'0');
            while let Some(b @ b'0'..=b'9') = self.data.get(self.pos) {
                n = n
                    .checked_mul(10)
                    .and_then(|n| n.checked_add(u64::from(b - b'0')))
                    .ok_or("specification integer overflow")?;
                self.pos += 1;
            }
            return Ok(Token::Number(n));
        }
        if b.is_ascii_alphabetic() || b == b'_' {
            let start = self.pos - 1;
            while self
                .data
                .get(self.pos)
                .is_some_and(|b| b.is_ascii_alphanumeric() || matches!(*b, b'_' | b'\''))
            {
                self.pos += 1;
            }
            return Ok(Token::Word(
                std::str::from_utf8(&self.data[start..self.pos])
                    .unwrap()
                    .into(),
            ));
        }
        if matches!(b, b'-' | b':' | b'=') {
            if let Some(&next) = self.data.get(self.pos) {
                if matches!((b, next), (b'-', b'>') | (b':', b'=') | (b'=', b'>')) {
                    self.pos += 1;
                    return Ok(Token::Symbol(String::from_utf8(vec![b, next]).unwrap()));
                }
            }
        }
        if b"()[]{},;:.@#".contains(&b) {
            return Ok(Token::Symbol((b as char).to_string()));
        }
        Err("invalid specification character".into())
    }

    fn peek(&mut self) -> Res<&Token> {
        if self.look.is_none() {
            self.look = Some(self.read()?);
        }
        Ok(self.look.as_ref().unwrap())
    }

    fn take(&mut self) -> Res<Token> {
        self.peek()?;
        Ok(self.look.take().unwrap())
    }

    fn eat(&mut self, text: &str) -> Res<bool> {
        if matches!(self.peek()?, Token::Word(s) | Token::Symbol(s) if s == text) {
            self.take()?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn expect(&mut self, text: &str) -> Res<()> {
        if self.eat(text)? {
            Ok(())
        } else {
            Err(format!("expected `{text}`"))
        }
    }

    fn number(&mut self) -> Res<u64> {
        match self.take()? {
            Token::Number(n) => Ok(n),
            _ => Err("expected natural number".into()),
        }
    }

    fn name(&mut self) -> Res<R> {
        if self.eat("_")? {
            return Ok(node("name", vec![]));
        }
        let mut parts = Vec::new();
        loop {
            if self.eat("#")? {
                parts.push(num(self.number()?));
            } else {
                match self.take()? {
                    Token::Word(s) | Token::String(s) => parts.push(Rc::new(X::S(s))),
                    _ => return Err("expected name component".into()),
                }
            }
            if !self.eat(".")? {
                break;
            }
        }
        Ok(node("name", parts))
    }
}

fn atom(tag: &str) -> R {
    Rc::new(X::A(TAGS.iter().position(|s| *s == tag).unwrap() as u8))
}

fn signature(arity: u64, sort: bool) -> R {
    node(
        "sig",
        vec![num(arity), atom(if sort { "prop" } else { "qf" })],
    )
}

struct Expression {
    value: R,
    height: usize,
}

impl Expression {
    fn leaf(value: R) -> Self {
        Self { value, height: 1 }
    }

    fn build(tag: &str, children: Vec<Self>) -> Res<Self> {
        let height = children.iter().map(|x| x.height).max().unwrap_or(0) + 1;
        if height > 2048 {
            return Err("specification tree depth exhausted".into());
        }
        Ok(Self {
            value: node(tag, children.into_iter().map(|x| x.value).collect()),
            height,
        })
    }
}

#[derive(Default)]
struct Context {
    locals: Vec<R>,
    functions: Vec<R>,
    predicates: Vec<R>,
}

struct Parser<'a> {
    lex: Lexer<'a>,
    context: Context,
}

impl Parser<'_> {
    fn typ(&mut self) -> Res<(u64, Option<bool>)> {
        let mut arity = 0;
        loop {
            if self.lex.eat("Nat")? {
                if self.lex.eat("->")? {
                    arity += 1;
                    if arity > 1_000_000 {
                        return Err("arity exceeds limit".into());
                    }
                } else {
                    return Ok((arity, None));
                }
            } else if self.lex.eat("QFProp")? {
                return Ok((arity, Some(false)));
            } else if self.lex.eat("Prop")? {
                return Ok((arity, Some(true)));
            } else {
                return Err("expected Nat, QFProp, or Prop type".into());
            }
        }
    }

    fn binder(&mut self) -> Res<(R, bool)> {
        let implicit = self.lex.eat("{")?;
        if !implicit {
            self.lex.expect("(")?;
        }
        let name = self.lex.name()?;
        self.lex.expect(":")?;
        Ok((name, implicit))
    }

    fn finish_binder(&mut self, implicit: bool) -> Res<()> {
        self.lex.expect(if implicit { "}" } else { ")" })
    }

    fn declaration(&mut self) -> Res<R> {
        let theorem = self.lex.eat("theorem")?;
        if !theorem {
            self.lex.expect("def")?;
        }
        let name = self.lex.name()?;
        let mut parameters = Vec::new();
        while matches!(self.lex.peek()?, Token::Symbol(s) if s == "(" || s == "{") {
            let (name, implicit) = self.binder()?;
            let (arity, sort) = self.typ()?;
            self.finish_binder(implicit)?;
            let binder = node("binder", vec![name.clone(), num(u64::from(implicit))]);
            if let Some(sort) = sort {
                self.context.predicates.push(name);
                parameters.push(node("predparam", vec![binder, signature(arity, sort)]));
            } else {
                self.context.functions.push(name);
                parameters.push(node("funparam", vec![binder, num(arity)]));
            }
        }
        self.lex.expect(":")?;
        let parameters = Rc::new(X::L(parameters));
        let result = if theorem {
            node(
                "theorem",
                vec![name, parameters, self.expression(true, 2048)?.value],
            )
        } else {
            let (arity, sort) = self.typ()?;
            self.lex.expect(":=")?;
            let body = self.expression(sort.is_some(), 2048)?.value;
            if let Some(sort) = sort {
                node(
                    "predicate",
                    vec![name, parameters, signature(arity, sort), body],
                )
            } else {
                node("function", vec![name, parameters, num(arity), body])
            }
        };
        self.lex.expect(";")?;
        Ok(result)
    }

    fn term_start(&mut self) -> Res<bool> {
        Ok(match self.lex.peek()? {
            Token::Symbol(s) => s == "(" || s == "@" || s == "#",
            Token::String(_) | Token::Number(_) => true,
            Token::Word(s) => !matches!(
                s.as_str(),
                "True"
                    | "False"
                    | "Eq"
                    | "And"
                    | "Or"
                    | "Imp"
                    | "Forall"
                    | "Exists"
                    | "fun"
                    | "let"
                    | "check_term"
                    | "check_predicate"
                    | "predarg"
                    | "Nat"
                    | "Prop"
                    | "QFProp"
                    | "def"
                    | "theorem"
            ),
            _ => false,
        })
    }

    fn expression(&mut self, predicate: bool, depth: usize) -> Res<Expression> {
        let depth = depth
            .checked_sub(1)
            .ok_or("specification depth exhausted")?;
        let mut result = self.primary(predicate, depth)?;
        while self.term_start()? {
            let argument = self.primary(false, depth)?;
            result = Expression::build(
                if predicate { "papp" } else { "tapp" },
                vec![result, argument],
            )?;
        }
        Ok(result)
    }

    fn actuals(&mut self, predicate: bool, depth: usize) -> Res<Expression> {
        let mut args = Vec::new();
        if self.lex.eat("[")? && !self.lex.eat("]")? {
            loop {
                args.push(self.expression(predicate, depth)?);
                if self.lex.eat("]")? {
                    break;
                }
                self.lex.expect(",")?;
            }
        }
        Ok(Expression {
            height: args.iter().map(|x| x.height).max().unwrap_or(0) + 1,
            value: Rc::new(X::L(args.into_iter().map(|x| x.value).collect())),
        })
    }

    fn primary(&mut self, predicate: bool, depth: usize) -> Res<Expression> {
        let depth = depth
            .checked_sub(1)
            .ok_or("specification depth exhausted")?;
        if self.lex.eat("(")? {
            let result = if self.lex.eat("fun")? {
                let (name, implicit) = self.binder()?;
                if implicit && !predicate {
                    return Err("implicit term lambda".into());
                }
                self.lex.expect("Nat")?;
                self.finish_binder(implicit)?;
                self.lex.expect("=>")?;
                self.context.locals.insert(0, name.clone());
                let body = self.expression(predicate, depth)?;
                self.context.locals.remove(0);
                if predicate {
                    Expression::build(
                        "plam",
                        vec![
                            Expression::leaf(node("binder", vec![name, num(u64::from(implicit))])),
                            body,
                        ],
                    )?
                } else {
                    Expression::build("tlam", vec![Expression::leaf(name), body])?
                }
            } else if !predicate && self.lex.eat("let")? {
                let name = self.lex.name()?;
                self.lex.expect(":=")?;
                let value = self.expression(false, depth)?;
                self.lex.expect(";")?;
                self.context.locals.insert(0, name.clone());
                let body = self.expression(false, depth)?;
                self.context.locals.remove(0);
                Expression::build("tlet", vec![Expression::leaf(name), value, body])?
            } else if predicate && self.lex.eat("check_term")? {
                self.checked_value(false, depth)?
            } else if predicate && self.lex.eat("check_predicate")? {
                self.checked_value(true, depth)?
            } else {
                self.expression(predicate, depth)?
            };
            self.lex.expect(")")?;
            return Ok(result);
        }
        if self.lex.eat("@")? {
            let name = self.lex.name()?;
            let functions = self.actuals(false, depth)?;
            return if predicate {
                let predicates = self.actuals(true, depth)?;
                Expression::build("pdef", vec![Expression::leaf(name), functions, predicates])
            } else {
                Expression::build("tdef", vec![Expression::leaf(name), functions])
            };
        }
        for (word, tag) in if predicate {
            &[("predarg", "pparam")][..]
        } else {
            &[("local", "tvar"), ("fnarg", "tparam")][..]
        } {
            if self.lex.eat(word)? {
                self.lex.expect("[")?;
                let index = self.lex.number()?;
                self.lex.expect("]")?;
                return Ok(Expression::leaf(node(tag, vec![num(index)])));
            }
        }
        if predicate {
            for (word, tag, count, terms) in [
                ("True", "true", 0, false),
                ("False", "false", 0, false),
                ("Eq", "eq", 2, true),
                ("And", "and", 2, false),
                ("Or", "or", 2, false),
                ("Imp", "imp", 2, false),
                ("Forall", "all", 1, false),
                ("Exists", "ex", 1, false),
            ] {
                if self.lex.eat(word)? {
                    let mut args = Vec::new();
                    for _ in 0..count {
                        args.push(self.primary(!terms, depth)?);
                    }
                    return Expression::build(tag, args);
                }
            }
        } else {
            if matches!(self.lex.peek()?, Token::Number(0)) {
                self.lex.take()?;
                return Ok(Expression::leaf(node("zero", vec![])));
            }
            if self.lex.eat("succ")? {
                return Ok(Expression::leaf(node("succ", vec![])));
            }
            if self.lex.eat("primrec")? {
                let mut args = Vec::new();
                for _ in 0..3 {
                    args.push(self.primary(false, depth)?);
                }
                return Expression::build("rec", args);
            }
        }
        if self.lex.eat("_")? {
            return Err("anonymous variables require an explicit index".into());
        }
        let name = self.lex.name()?;
        let found = if predicate {
            self.context
                .predicates
                .iter()
                .position(|n| n == &name)
                .map(|i| ("pparam", i))
        } else {
            self.context
                .locals
                .iter()
                .position(|n| n == &name)
                .map(|i| ("tvar", i))
                .or_else(|| {
                    self.context
                        .functions
                        .iter()
                        .position(|n| n == &name)
                        .map(|i| ("tparam", i))
                })
        };
        match found {
            Some((tag, i)) => Ok(Expression::leaf(node(tag, vec![num(i as u64)]))),
            None => Err("unbound specification name; global references require @".into()),
        }
    }

    fn checked_value(&mut self, predicate: bool, depth: usize) -> Res<Expression> {
        let name = self.lex.name()?;
        self.lex.expect(":=")?;
        let value = self.expression(predicate, depth)?;
        self.lex.expect(";")?;
        let body = self.expression(true, depth)?;
        Expression::build(
            if predicate { "pletPred" } else { "pletTerm" },
            vec![Expression::leaf(name), value, body],
        )
    }
}

pub(crate) struct Specifications {
    reader: BufReader<File>,
    path: String,
    records: usize,
}

impl Specifications {
    pub(crate) fn open(path: &Path) -> Res<Self> {
        Ok(Self {
            reader: BufReader::new(
                File::open(path).map_err(|e| format!("{}: {e}", path.display()))?,
            ),
            path: path.display().to_string(),
            records: 0,
        })
    }

    fn frame(&mut self) -> Res<Vec<u8>> {
        let mut data = Vec::new();
        let mut brackets = Vec::new();
        let (mut quoted, mut escaped, mut comment, mut dash) = (false, false, false, false);
        loop {
            let input = self.reader.fill_buf().map_err(|e| e.to_string())?;
            if input.is_empty() {
                return Ok(data);
            }
            let mut used = 0;
            let mut finished = false;
            for &b in input {
                used += 1;
                if comment {
                    if b == b'\n' {
                        comment = false;
                    }
                } else if quoted {
                    if escaped {
                        escaped = false;
                    } else if b == b'\\' {
                        escaped = true;
                    } else if b == b'"' {
                        quoted = false;
                    }
                } else if dash && b == b'-' {
                    comment = true;
                    dash = false;
                } else {
                    dash = b == b'-';
                    match b {
                        b'"' => quoted = true,
                        b'(' | b'[' | b'{' => brackets.push(b),
                        b')' | b']' | b'}' => {
                            let expected = match b {
                                b')' => b'(',
                                b']' => b'[',
                                _ => b'{',
                            };
                            if brackets.pop() != Some(expected) {
                                return Err("mismatched specification delimiter".into());
                            }
                        }
                        b';' if brackets.is_empty() => {
                            finished = true;
                            break;
                        }
                        _ => {}
                    }
                    if brackets.len() > 2048 {
                        return Err("specification depth exhausted".into());
                    }
                }
            }
            if data.len() + used > LIMIT {
                return Err("specification record too large".into());
            }
            data.extend_from_slice(&input[..used]);
            self.reader.consume(used);
            if finished {
                return Ok(data);
            }
        }
    }

    pub(crate) fn next(&mut self) -> Res<Option<R>> {
        let data = self.frame()?;
        let mut parser = Parser {
            lex: Lexer {
                data: &data,
                pos: 0,
                look: None,
            },
            context: Context::default(),
        };
        let read = (|| {
            if parser.lex.peek()? == &Token::End {
                return Ok(None);
            }
            let result = parser.declaration()?;
            if parser.lex.peek()? != &Token::End {
                return Err("trailing specification data".into());
            }
            Ok(Some(result))
        })();
        let result = read.map_err(|e: String| {
            format!(
                "{}, record {}, byte {}: {e}",
                self.path, self.records, parser.lex.pos
            )
        })?;
        if result.is_some() {
            self.records += 1;
        }
        Ok(result)
    }
}
