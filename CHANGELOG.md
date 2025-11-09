## 2.1.0
- Remove serde_derive dependency from Cargo.toml
- Use references when relevant & avoid cloning
### Breaking changes
 - `OpType` renamed to `OpKind`
  - `INSERT` -> `Insert`
  - `RETAIN` -> `Retain`
  - `DELETE` -> `Delete`
 - ```rust
   - let composed = AttributesMap::compose(a, b, false);
   + let composed = AttributesMap::compose(&a, &b, false);
   ```
 - ```rust
   - let diff = AttributesMap::diff(a, b);
   + let diff = AttributesMap::diff(&a, &b);
   ```
 - ```rust
   - AttributesMap::invert(attributes, base)
   + AttributesMap::invert(&attributes, &base)
   ```

## 2.0.0
- Deserialization with `delta` instead of `ops` property is supported
- Enhanced `Delta` builder functions
- `Delta` implements `Eq`

### Breaking changes
- `insert`, `delete` & `retain` take ownership of `self`.
  Usage:
  ```Rust
  let delta = Delta()::new().insert("i").retain(12).delete(4);
  ```
- JSON serialization of delta will be
  ```JSON
  {
    "delta": [
      ...
    ]
  }
  ```
  instead of

  ```JSON
  {
    "ops": [
      ...
    ]
  }
  ```
  One should use `#[serde(flatten)]` when including a delta in a structure
- `Op::len` returns the number of characters rather than the length of the string when operation is of `INSERT` kind
- `Delta::insert` does NOT trim the supplied string anymore

## 1.2.0
- Rename ops to `delta` in (de)serialization

## 1.1.1
- **Fix** Missing deserialization of `Delta`

## 1.1.0
- Shorthand for attributes
- Creation of `Delta`s less chatty
