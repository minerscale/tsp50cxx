//! # Uninit
//!
//! Uninit is a safe rust method of keeping track of uninitialised memory
//! In debug mode, uninit keeps track of and will panic if unwrap is called on it.
//! In release mode, the None variant of the enum disappears. In order to assign
//! values to their uninitialised state, Default is used.

use std::fmt::{Debug, Formatter};

#[cfg(debug_assertions)]
#[derive(Copy, Clone, Default)]
pub enum Uninit<T> {
    Some(T),
    #[default]
    None,
}

#[cfg(debug_assertions)]
impl<T> Uninit<T> {
    pub fn unwrap(self) -> T {
        match self {
            Uninit::Some(val) => val,
            Uninit::None => panic!("attempt to access uninitialised value"),
        }
    }
}

#[cfg(debug_assertions)]
impl<T: Default> Uninit<T> {
    pub fn unwrap_or_default(self) -> T {
        match self {
            Uninit::Some(val) => val,
            Uninit::None => Default::default(),
        }
    }
}

#[cfg(debug_assertions)]
impl<T: Clone + Debug + Default> Debug for Uninit<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self {
            Uninit::Some(x) => f.write_fmt(format_args!("{:?}", x)),
            Uninit::None => f.write_str("---"),
        }
    }
}

#[cfg(not(debug_assertions))]
#[derive(Copy, Clone)]
pub enum Uninit<T> {
    Some(T),
}

#[cfg(not(debug_assertions))]
impl<T: Default> Default for Uninit<T> {
    fn default() -> Self {
        Self::Some(T::default())
    }
}

#[cfg(not(debug_assertions))]
impl<T> Uninit<T> {
    pub fn unwrap(self) -> T {
        match self {
            Uninit::Some(val) => val,
        }
    }
}

#[cfg(not(debug_assertions))]
impl<T: Default> Uninit<T> {
    pub fn unwrap_or_default(self) -> T {
        match self {
            Uninit::Some(val) => val,
        }
    }
}

#[cfg(not(debug_assertions))]
impl<T: Clone + Debug> Debug for Uninit<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "{:?}",
            &<Uninit<T> as Clone>::clone(self).unwrap()
        ))
    }
}
