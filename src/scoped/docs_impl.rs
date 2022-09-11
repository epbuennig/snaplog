use super::IntoScoped;

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
