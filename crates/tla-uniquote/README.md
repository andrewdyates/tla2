# UniQuote

This crate allows quoting strings for use in output. It works similarly to
[`str::escape_debug`], but the result is meant to be shown to users. Simply
call [`Quote::quote`] on an argument passed to [`println!`] or a similar macro
to quote it.

One of the primary uses for this crate is displaying paths losslessly. Since
[`Path`] has no [`Display`] implementation, it is usually output by calling
[`Path::display`] or [`Path::to_string_lossy`] beforehand. However, both of
those methods are lossy; they replace all invalid characters with
[`REPLACEMENT_CHARACTER`]. This crate escapes those invalid characters instead,
allowing them to always be displayed correctly.

[![GitHub Build Status](https://github.com/dylni/uniquote/workflows/build/badge.svg?branch=master)](https://github.com/dylni/uniquote/actions?query=branch%3Amaster)

## Usage

Add the following lines to your "Cargo.toml" file:

```toml
[dependencies]
uniquote = "3.3"
```

See the [documentation] for available functionality and examples.

## Rust version support

The minimum supported Rust toolchain version is currently Rust 1.64.0.

Minor version updates may increase this version requirement. However, the
previous two Rust releases will always be supported. If the minimum Rust
version must not be increased, use a tilde requirement to prevent updating this
crate's minor version:

```toml
[dependencies]
uniquote = "~3.3"
```

## License

Licensing terms are specified in [COPYRIGHT].

Unless you explicitly state otherwise, any contribution submitted for inclusion
in this crate, as defined in [LICENSE-APACHE], shall be licensed according to
[COPYRIGHT], without any additional terms or conditions.

### Third-party content

This crate includes copies and modifications of content developed by third
parties:

- [src/escape/tables/unprintable.rs] contains structured data defined by
  Unicode, Inc., licensed under the Unicode License.

See that file for more details.

Copies of third-party licenses can be found in [LICENSE-THIRD-PARTY].

[COPYRIGHT]: https://github.com/dylni/uniquote/blob/master/COPYRIGHT
[`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
[documentation]: https://docs.rs/uniquote
[LICENSE-APACHE]: https://github.com/dylni/uniquote/blob/master/LICENSE-APACHE
[LICENSE-THIRD-PARTY]: https://github.com/dylni/uniquote/blob/master/LICENSE-THIRD-PARTY
[`Path`]: https://doc.rust-lang.org/std/path/struct.Path.html
[`Path::display`]: https://doc.rust-lang.org/std/path/struct.Path.html#method.display
[`Path::to_string_lossy`]: https://doc.rust-lang.org/std/path/struct.Path.html#method.to_string_lossy
[`println!`]: https://doc.rust-lang.org/std/macro.println.html
[`Quote::quote`]: https://docs.rs/uniquote/*/uniquote/trait.Quote.html#method.quote
[`REPLACEMENT_CHARACTER`]: https://doc.rust-lang.org/std/char/constant.REPLACEMENT_CHARACTER.html
[src/escape/tables/unprintable.rs]: https://github.com/dylni/uniquote/blob/master/src/escape/tables/unprintable.rs
[`str::escape_debug`]: https://doc.rust-lang.org/std/primitive.str.html#method.escape_debug
