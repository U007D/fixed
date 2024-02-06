// Copyright © 2018–2024 Trevor Spiteri

// This library is free software: you can redistribute it and/or
// modify it under the terms of either
//
//   * the Apache License, Version 2.0 or
//   * the MIT License
//
// at your option.
//
// You should have recieved copies of the Apache License and the MIT
// License along with the library. If not, see
// <https://www.apache.org/licenses/LICENSE-2.0> and
// <https://opensource.org/licenses/MIT>.

/*!
Extra types that do not need to be handled directly.

These types are used for `where` constraints.
*/

/// Used for constraints conditional on a [`bool`].
///
/// # Examples
///
/// ```rust
/// #![feature(generic_const_exprs)]
/// # #![allow(incomplete_features)]
///
/// use fixed::types::extra::{If, True};
/// fn foo<const U: u32>()
/// where
///     If<{ U > 0 }>: True,
/// {
///     assert!(U > 0);
/// }
///
/// foo::<1>();
/// ```
///
/// This would fail to compile because the constraint is not met:
///
/// ```rust,compile_fail
/// #![feature(generic_const_exprs)]
/// # #![allow(incomplete_features)]
///
/// use fixed::types::extra::{If, True};
/// fn foo<const U: u32>()
/// where
///     If<{ U > 0 }>: True,
/// {
///     assert!(U > 0);
/// }
///
/// foo::<0>();
/// ```
pub struct If<const CONDITION: bool>;

/// This is implemented for [`If`] when the condition is [`true`].
pub trait True {}

impl True for If<true> {}
