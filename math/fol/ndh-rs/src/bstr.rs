
use std::rc::Rc;

#[derive(Clone, PartialEq, Eq)]
pub enum Bstr {
    Small([u8; 15]), Ref(Rc<Box<[u8]>>)
}

impl From<&[u8]> for Bstr {
    fn from(s: &[u8]) -> Self {
        let n = s.len();
        if n < 15 {
            let mut a = [0; 15];
            a[14] = n as u8;
            a[0..n].copy_from_slice(&s[0..n]);
            Bstr::Small(a)
        } else {
            Bstr::Ref(Rc::new(Box::from(s)))
        }
    }
}

impl From<&str> for Bstr {
    fn from(s: &str) -> Self {
        Self::from(s.as_bytes())
    }
}

impl Bstr {
    pub fn as_slice(&self) -> &[u8] {
        match self {
            Bstr::Small(a) => &a[0..a[14] as usize],
            Bstr::Ref(x) => x.as_ref()
        }
    }
}

impl std::fmt::Display for Bstr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match std::str::from_utf8(self.as_slice()) {
            Ok(s) => s,
            Err(_) => "ERROR" 
        })
    }
}

impl std::fmt::Debug for Bstr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}
