# yoke [![crates.io](https://img.shields.io/crates/v/yoke)](https://crates.io/crates/yoke)

<!-- cargo-rdme start -->

This crate provides [`Yoke<Y, C>`][Yoke], which allows one to "yoke" (attach) a zero-copy deserialized
object (say, a `Cow<'a, str>`) to the source it was deserialized from, (say, an [`Rc<[u8]>`](alloc::rc::Rc)),
known in this crate as a "cart", producing a type that looks like `Yoke<Cow<'static, str>, Rc<[u8]>>`
and can be moved around with impunity.

Succinctly, this allows one to "erase" static lifetimes and turn them into dynamic ones, similarly
to how `dyn` allows one to "erase" static types and turn them into dynamic ones.

Most of the time the yokeable `Y` type will be some kind of zero-copy deserializable
abstraction, potentially with an owned variant (like `Cow`,
[`ZeroVec`](https://docs.rs/zerovec), or an aggregate containing such types), and the cart `C` will be some smart pointer like
  `Box<T>`, `Rc<T>`, or `Arc<T>`, potentially wrapped in an `Option<T>`.

The key behind this crate is [`Yoke::get()`], where calling [`.get()`][Yoke::get] on a type like
`Yoke<Cow<'static, str>, _>` will get you a short-lived `&'a Cow<'a, str>`, restricted to the
lifetime of the borrow used during `.get()`. This is entirely safe since the `Cow` borrows from
the cart type `C`, which cannot be interfered with as long as the `Yoke` is borrowed by `.get()`.
`.get()` protects access by essentially reifying the erased lifetime to a safe local one
when necessary.

See the documentation of [`Yoke`] for more details.

<!-- cargo-rdme end -->

## More Information

For more information on development, authorship, contributing etc. please visit [`ICU4X home page`](https://github.com/unicode-org/icu4x).
