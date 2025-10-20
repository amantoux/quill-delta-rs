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
## 1.2.0
- Rename ops to `delta` in (de)serialization

## 1.1.1
- **Fix** Missing deserialization of `Delta`

## 1.1.0
- Shorthand for attributes
- Creation of `Delta`s less chatty
