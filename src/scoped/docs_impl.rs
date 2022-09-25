#![allow(dead_code)]

use crate::{AsThinScoped, AsThinScopedMut, IntoScoped};

#[doc(hidden)]
#[derive(Debug, PartialEq, Eq)]
pub struct __Prefixed {
    pub prefix: Option<&'static str>,
    pub content: &'static str,
}

impl __Prefixed {
    pub fn new(s: &'static str) -> Self {
        let parts = s.split_once(':');

        Self {
            prefix: parts.map(|(p, _)| p),
            content: parts.map(|(_, c)| c).unwrap_or(s),
        }
    }
}

impl IntoScoped for __Prefixed {
    type Scope = &'static str;
    type Ignored = Option<&'static str>;

    fn into_scoped(self) -> (Self::Scope, Self::Ignored) {
        (self.content, self.prefix)
    }

    fn from_scoped(scope: Self::Scope, ignored: Self::Ignored) -> Self {
        Self {
            prefix: ignored,
            content: scope,
        }
    }
}

#[derive(Debug)]
pub struct Ref<'p> {
    prefix: &'p Option<&'static str>,
    content: &'p &'static str,
}

impl<'p> PartialEq<&__Prefixed> for Ref<'p> {
    fn eq(&self, other: &&__Prefixed) -> bool {
        *self.prefix == other.prefix && *self.content == other.content
    }
}

#[derive(Debug)]
pub struct RefMut<'p> {
    prefix: &'p mut Option<&'static str>,
    content: &'p mut &'static str,
}

impl<'p> PartialEq<&__Prefixed> for RefMut<'p> {
    fn eq(&self, other: &&__Prefixed) -> bool {
        *self.prefix == other.prefix && *self.content == other.content
    }
}

impl AsThinScoped for __Prefixed {
    type ThinScoped<'this> = Ref<'this>;

    fn as_thin_scoped<'a>(
        scope: &'a Self::Scope,
        ignored: &'a Self::Ignored,
    ) -> Self::ThinScoped<'a> {
        Ref {
            content: scope,
            prefix: ignored,
        }
    }
}

impl AsThinScopedMut for __Prefixed {
    type ThinScopedMut<'this> = RefMut<'this>;

    fn as_thin_scoped_mut<'a>(
        scope: &'a mut Self::Scope,
        ignored: &'a mut Self::Ignored,
    ) -> Self::ThinScopedMut<'a> {
        RefMut {
            content: scope,
            prefix: ignored,
        }
    }
}
