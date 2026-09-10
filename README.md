[![Build](https://github.com/amantoux/quill-delta-rs/actions/workflows/build.yml/badge.svg)](https://github.com/amantoux/quill-delta-rs/actions/workflows/build.yml)
[![codecov](https://codecov.io/gh/amantoux/quill-delta-rs/graph/badge.svg?token=7SKQMTX1L0)](https://codecov.io/gh/amantoux/quill-delta-rs)

Implementation of Quill editor Delta format in Rust. Refer to official
[documentation][] for more details.

[documentation]: https://quilljs.com/docs/delta/

## Usage

```rust
use quill_delta_rs::{
    attributes::{attributes, AttributesMap},
    delta::Delta
};

fn main() {
    let mut doc = Delta::new();
    doc.insert("Hello world\n", Some(attributes!("h" => "1")));
    let change = Delta::new()
        .retain(6, None)
        .delete(6)
        .insert("Earth\n", None);
    let result = doc.try_compose(&change).expect("valid text boundaries");
    println!("Original document:\n{}\n", doc);
    println!("Change:\n{}\n", change);
    println!("Updated document:\n{}\n", result);

    // Prints:
    //
    //  Original document:
    //  ins(Hello world⏎) + {h: 1}}
    //
    //
    //  Change:
    //  ret(6)
    //  ins(Earth⏎)
    //  del(6)
    //
    //
    //  Updated document:
    //  ins(Hello ) + {h: 1}}
    //  ins(Earth⏎)
}
```

## Features and bugs

Please file feature requests and bugs at the [issue tracker][tracker].

[tracker]: https://github.com/amantoux/quill-delta-rs/issues

## Text positions

By default, text lengths and retain/delete/slice positions count Unicode scalar
values, preserving the library's original behavior. They do not count UTF-8 bytes
or grapheme clusters. Embeds always have length 1.

Enable `utf16-positions` for UTF-16 code-unit positions compatible with Quill and
Dart/JavaScript clients:

```toml
[dependencies]
quill-delta-rs = { features = ["utf16-positions"] }
```

For example, `🙄` has length 1 by default and 2 with `utf16-positions`. The feature applies
to text length, slicing, composition, and inversion; it does not change the JSON
format or Rust's UTF-8 string storage. All producers and consumers of a delta
must agree on its position convention.

For recoverable errors, use `try_next_len`, `try_rest`, `try_slice`,
`try_compose`, and `try_invert`. These always return `Result<_, FromUtf16Error>`.
Scalar mode returns `Ok`; UTF-16 mode returns an error if a text boundary splits
a surrogate pair. A failed read leaves the iterator unchanged.

```rust
use quill_delta_rs::{Delta, Iterator};

let base = Delta::new().insert("A🙄B", None);
let mut iter = Iterator::from(base.ops());
let first = iter.try_next_len(1)?;
# Ok::<(), std::string::FromUtf16Error>(())
```
