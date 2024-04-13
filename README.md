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
    let mut change = Delta::new();
    change
        .retain(6, None)
        .delete(6)
        .insert("Earth\n", None);
    let result = doc.compose(&change);
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