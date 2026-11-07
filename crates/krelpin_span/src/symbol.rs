use std::collections::HashMap;
use std::fmt;
use std::sync::{LazyLock, PoisonError, RwLock};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(u32);

macro_rules! keywords {
    (
        reserved { $($name:ident: $text:literal,)* }
        contextual { $($cname:ident: $ctext:literal,)* }
    ) => {
        #[repr(u32)]
        enum KeywordIndex {
            $($name,)*
            $($cname,)*
        }

        #[allow(non_upper_case_globals)]
        pub mod kw {
            use super::{KeywordIndex, Symbol};

            $(pub const $name: Symbol = Symbol(KeywordIndex::$name as u32);)*
            $(pub const $cname: Symbol = Symbol(KeywordIndex::$cname as u32);)*
        }

        const KEYWORDS: &[&str] = &[$($text,)* $($ctext,)*];
        const RESERVED: usize = [$($text,)*].len();
    };
}

keywords! {
    reserved {
        Abstract: "abstract",
        Assert: "assert",
        Async: "async",
        Await: "await",
        Boolean: "boolean",
        Break: "break",
        Byte: "byte",
        Case: "case",
        Catch: "catch",
        Char: "char",
        Class: "class",
        Const: "const",
        Continue: "continue",
        Default: "default",
        Do: "do",
        Double: "double",
        Else: "else",
        Enum: "enum",
        Extends: "extends",
        False: "false",
        Final: "final",
        Finally: "finally",
        Float: "float",
        For: "for",
        If: "if",
        Implements: "implements",
        Import: "import",
        Instanceof: "instanceof",
        Int: "int",
        Interface: "interface",
        Long: "long",
        Macro: "macro",
        Mut: "mut",
        New: "new",
        Null: "null",
        Package: "package",
        Private: "private",
        Protected: "protected",
        Record: "record",
        Public: "public",
        Return: "return",
        Short: "short",
        Static: "static",
        Struct: "struct",
        Super: "super",
        Switch: "switch",
        This: "this",
        Throw: "throw",
        Throws: "throws",
        True: "true",
        Try: "try",
        Underscore: "_",
        Void: "void",
        When: "when",
        Where: "where",
        While: "while",
        With: "with",
        Yield: "yield",
    }
    contextual {
        Borrows: "borrows",
        Keeps: "keeps",
        Move: "move",
    }
}

impl Symbol {
    pub fn intern(string: &str) -> Symbol {
        let interner = INTERNER.read().unwrap_or_else(PoisonError::into_inner);
        if let Some(&symbol) = interner.names.get(string) {
            return symbol;
        }
        drop(interner);

        INTERNER
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .intern(string)
    }

    pub fn as_str(self) -> &'static str {
        INTERNER
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .get(self)
    }

    pub fn is_keyword(self) -> bool {
        (self.0 as usize) < RESERVED
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

static INTERNER: LazyLock<RwLock<Interner>> =
    LazyLock::new(|| RwLock::new(Interner::prefill(KEYWORDS)));

struct Interner {
    names: HashMap<&'static str, Symbol>,
    strings: Vec<&'static str>,
}

impl Interner {
    fn prefill(init: &[&'static str]) -> Interner {
        let strings = init.to_vec();
        let names = strings.iter().copied().zip((0..).map(Symbol)).collect();
        Interner { names, strings }
    }

    fn intern(&mut self, string: &str) -> Symbol {
        if let Some(&symbol) = self.names.get(string) {
            return symbol;
        }

        let symbol = Symbol(self.strings.len() as u32);
        let string: &'static str = Box::leak(Box::from(string));
        self.strings.push(string);
        self.names.insert(string, symbol);
        symbol
    }

    fn get(&self, symbol: Symbol) -> &'static str {
        self.strings[symbol.0 as usize]
    }
}

#[cfg(test)]
pub(crate) fn keyword_texts() -> &'static [&'static str] {
    KEYWORDS
}
