use std::{iter, string::FromUtf16Error};

use serde_json::Value;

use crate::op::{Op, OpKind};

pub struct Iterator<'it> {
    ops: &'it Vec<Op>,
    // index of current operation in ops
    index: usize,
    // offset within current operation
    offset: usize,
}

impl<'it> Iterator<'it> {
    /// Create an iterator from a list of [Op]s
    pub fn from(operations: &'it Vec<Op>) -> Self {
        Iterator {
            ops: operations,
            index: 0,
            offset: 0,
        }
    }

    /// Get the next [Op] for a given length.
    ///
    /// if `length` falls in the middle of an [Op], returns the [Op] with the
    /// adapted [Op] length otherwise return remaing part of the [Op].
    ///
    /// # Example
    ///
    /// ```
    /// use serde_json::{json, Value};
    ///
    /// use quill_delta_rs::{
    ///     {attributes, AttributesMap},
    ///     Op,
    ///     Iterator
    /// };
    ///
    /// let ops = vec![
    ///     Op::insert("Hello", Some(attributes!("bold" => true))),
    ///     Op::retain(3, None),
    ///     Op::delete(4),
    ///     Op::insert(json!({"key": "value"}), None),
    /// ];
    /// let mut iter = Iterator::from(&ops);
    /// assert_eq!(
    ///     Op::insert("He", Some(attributes!("bold" => true))),
    ///     iter.next_len(2)
    /// );
    /// assert_eq!(
    ///     Op::insert("llo", Some(attributes!("bold" => true))),
    ///     iter.next_len(10)
    /// );
    /// assert_eq!(Op::retain(1, None), iter.next_len(1));
    /// assert_eq!(Op::retain(2, None), iter.next_len(2));
    /// assert_eq!(Op::delete(2), iter.next_len(2));
    /// assert_eq!(Op::delete(2), iter.next_len(2));
    /// assert_eq!(Op::insert(json!({"key": "value"}), None), iter.next_len(10));
    /// assert_eq!(Op::retain_until_end(), iter.next_len(1))
    /// ```
    /// Length and offsets count Unicode scalars by default, or UTF-16 code
    /// units with the `utf16-positions` feature.
    ///
    /// # Panics
    ///
    /// With `utf16-positions`, panics if a boundary splits a surrogate pair. Use
    /// [`Self::try_next_len`] to handle this error without panicking.
    /// The iterator is unchanged on this error.
    pub fn next_len(&mut self, length: usize) -> Op {
        self.try_next_len(length)
            .expect("UTF-16 operation boundary splits a surrogate pair; use try_next_len to handle the error")
    }

    /// Fallible read in either feature mode. A split surrogate pair returns an
    /// error without advancing the iterator. Scalar mode always returns `Ok`.
    ///
    /// # Example
    ///
    /// ```
    /// use quill_delta_rs::{Iterator, Op};
    /// let ops = vec![Op::insert("Hello", None)];
    /// let mut iter = Iterator::from(&ops);
    /// assert_eq!(iter.try_next_len(2)?, Op::insert("He", None));
    /// # Ok::<(), std::string::FromUtf16Error>(())
    /// ```
    pub fn try_next_len(&mut self, length: usize) -> Result<Op, FromUtf16Error> {
        if self.index >= self.ops.len() {
            return Ok(Op::retain_until_end());
        }

        let next_op = self.ops.get(self.index).unwrap();
        let init_offset = self.offset;
        let op_len = next_op.len();
        let length = length.min(op_len - init_offset);

        // Build the operation before advancing: an invalid UTF-16 boundary must
        // not leave the iterator partly consumed when returning an error.
        let op = if next_op.is_delete() {
            Op::delete(length)
        } else if next_op.is_retain() {
            Op::retain(length, next_op.attributes())
        } else if next_op.is_text_insert() {
            #[cfg(feature = "utf16-positions")]
            let sub_string = {
                let units: Vec<u16> = next_op
                    .value_as_string()
                    .encode_utf16()
                    .skip(init_offset)
                    .take(length)
                    .collect();
                String::from_utf16(&units)?
            };
            #[cfg(not(feature = "utf16-positions"))]
            let sub_string: String = next_op
                .value_as_string()
                .chars()
                .skip(init_offset)
                .take(length)
                .collect();
            Op::insert(Value::from(sub_string), next_op.attributes())
        } else {
            Op::insert(next_op.value(), next_op.attributes())
        };

        if length == op_len - init_offset {
            self.index += 1;
            self.offset = 0;
        } else {
            self.offset += length;
        }
        Ok(op)
    }

    /// Get current [Op].
    ///
    /// Returns [None] if list of [Op]s is empty
    pub fn peek(&self) -> Option<&Op> {
        self.ops.get(self.index)
    }

    /// Get the length of the next [Op] without affecting the iterator.
    ///
    /// Returns [usize::MAX] if no more [Op] available.
    pub fn peek_len(&self) -> usize {
        if self.index >= self.ops.len() {
            usize::MAX
        } else {
            self.ops.get(self.index).unwrap().len() - self.offset
        }
    }

    /// Get the [OpType] of the next [Op] without affecting the iterator.
    ///
    /// Returns ```OpType::RETAIN(usize::MAX)``` if no more [Op] available.
    pub fn peek_type(&self) -> OpKind {
        if self.index >= self.ops.len() {
            OpKind::Retain(usize::MAX)
        } else {
            self.ops.get(self.index).unwrap().kind()
        }
    }

    /// Has a next [Op]
    pub fn has_next(&self) -> bool {
        self.peek_len() < usize::MAX
    }

    /// Get the list of remaining [Op]s in the iterator
    ///
    /// # Example
    ///
    /// ```
    /// use serde_json::{json, Value};
    ///
    /// use quill_delta_rs::{
    ///     {attributes, AttributesMap},
    ///     Iterator,
    ///     {Op, OpKind},
    /// };
    ///
    /// let ops = vec![
    ///     Op::insert("Hello", Some(attributes!("bold" => true))),
    ///     Op::retain(3, None),
    ///     Op::delete(4),
    ///     Op::insert(json!({"key": "value"}), None),
    /// ];
    /// let mut iter = Iterator::from(&ops);
    /// let _ = iter.next_len(2);
    /// assert_eq!(
    ///     vec![
    ///         Op::insert("llo",Some(attributes!("bold" => true))),
    ///         Op::retain(3, None),
    ///         Op::delete(4),
    ///         Op::insert(json!({"key": "value"}), None),
    ///     ],
    ///     iter.rest()
    /// );
    /// ```
    /// # Panics
    ///
    /// With `utf16-positions`, panics on a split surrogate pair. Use
    /// [`Self::try_rest`] to handle the decoding error instead.
    pub fn rest(&mut self) -> Vec<Op> {
        self.try_rest().expect(
            "UTF-16 operation boundary splits a surrogate pair; use try_rest to handle the error",
        )
    }

    /// Returns the remaining operations without consuming the iterator.
    ///
    /// # Example
    ///
    /// ```
    /// use quill_delta_rs::{Iterator, Op};
    /// let ops = vec![Op::insert("Hello", None)];
    /// let mut iter = Iterator::from(&ops);
    /// iter.try_next_len(2)?;
    /// assert_eq!(iter.try_rest()?, vec![Op::insert("llo", None)]);
    /// assert_eq!(iter.peek_len(), 3);
    /// # Ok::<(), std::string::FromUtf16Error>(())
    /// ```
    pub fn try_rest(&mut self) -> Result<Vec<Op>, FromUtf16Error> {
        if !self.has_next() {
            return Ok(Vec::new());
        }

        if self.offset == 0 {
            let slice = &self.ops.as_slice()[self.index..self.ops.len()];
            return Ok(Vec::from(slice));
        }

        let init_offset = self.offset;
        let init_index = self.index;
        let next_op = self.try_next_len(usize::MAX)?;
        let mut rest = Vec::from(&self.ops.as_slice()[self.index..self.ops.len()]);
        self.offset = init_offset;
        self.index = init_index;
        let mut returned = vec![next_op];
        returned.append(&mut rest);
        Ok(returned)
    }
}

impl<'it> iter::Iterator for Iterator<'it> {
    type Item = Op;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.next_len(usize::MAX))
    }
}

#[cfg(test)]
mod tests {

    use serde_json::json;

    use crate::{
        AttributesMap,
        op::{Op, OpKind},
    };

    use super::Iterator;

    #[test]
    fn next_len() {
        let ops = vec![
            Op::insert("Hello", Some(attributes!("bold" => true))),
            Op::retain(3, None),
            Op::delete(4),
            Op::insert(json!({"key": "value"}), None),
        ];
        let mut iter = Iterator::from(&ops);
        assert_eq!(
            Op::insert("He", Some(attributes!("bold" => true))),
            iter.next_len(2)
        );
        assert_eq!(
            Op::insert("llo", Some(attributes!("bold" => true))),
            iter.next_len(10)
        );
        assert_eq!(Op::retain(1, None), iter.next_len(1));
        assert_eq!(Op::retain(2, None), iter.next_len(2));
        assert_eq!(Op::delete(2), iter.next_len(2));
        assert_eq!(Op::delete(2), iter.next_len(2));
        assert_eq!(Op::insert(json!({"key": "value"}), None), iter.next_len(10));
        assert_eq!(Op::retain_until_end(), iter.next_len(1))
    }

    #[test]
    fn peek() {
        let ops = vec![Op::insert("Hello", Some(attributes!("bold" => true)))];
        let mut iter = Iterator::from(&ops);
        assert_eq!(
            &Op::insert("Hello", Some(attributes!("bold" => true)),),
            iter.peek().unwrap()
        );
        assert_eq!(
            Op::insert("Hello", Some(attributes!("bold" => true)),),
            iter.next().unwrap()
        );
    }

    #[test]
    fn peek_len() {
        let ops = vec![Op::insert("Hello", Some(attributes!("bold" => true)))];
        let mut iter = Iterator::from(&ops);
        assert_eq!("Hello".len(), iter.peek_len());
        assert_eq!(
            Op::insert("Hello", Some(attributes!("bold" => true)),),
            iter.next().unwrap()
        );
        assert_eq!(usize::MAX, iter.peek_len());
    }

    #[test]
    fn peek_type() {
        let ops = vec![Op::insert("Hello", Some(attributes!("bold" => true)))];
        let mut iter = Iterator::from(&ops);
        assert_eq!(OpKind::Insert("Hello".into()), iter.peek_type());
        assert_eq!(
            Op::insert("Hello", Some(attributes!("bold" => true)),),
            iter.next().unwrap()
        );
        assert_eq!(OpKind::Retain(usize::MAX), iter.peek_type());
    }

    #[test]
    fn has_next() {
        let ops = vec![Op::insert("Hello", Some(attributes!("bold" => true)))];
        let mut iter = Iterator::from(&ops);
        assert_eq!(true, iter.has_next());
        assert_eq!(
            Op::insert("Hello", Some(attributes!("bold" => true)),),
            iter.next().unwrap()
        );
        assert_eq!(false, iter.has_next());
    }

    #[test]
    fn rest() {
        let ops = vec![
            Op::insert("Hello", Some(attributes!("bold" => true))),
            Op::retain(3, None),
            Op::delete(4),
            Op::insert(json!({"key": "value"}), None),
        ];
        let mut iter = Iterator::from(&ops);
        let _ = iter.next_len(2);
        assert_eq!(
            vec![
                Op::insert("llo", Some(attributes!("bold" => true)),),
                Op::retain(3, None),
                Op::delete(4),
                Op::insert(json!({"key": "value"}), None),
            ],
            iter.rest()
        );
        let _ = iter.next_len(10);
        assert_eq!(
            vec![
                Op::retain(3, None),
                Op::delete(4),
                Op::insert(json!({"key": "value"}), None)
            ],
            iter.rest()
        );
        let _ = iter.next_len(1);
        assert_eq!(
            vec![
                Op::retain(2, None),
                Op::delete(4),
                Op::insert(json!({"key": "value"}), None)
            ],
            iter.rest()
        );
        let _ = iter.next_len(2);
        assert_eq!(
            vec![Op::delete(4), Op::insert(json!({"key": "value"}), None)],
            iter.rest()
        );
        let _ = iter.next_len(2);
        assert_eq!(
            vec![Op::delete(2), Op::insert(json!({"key": "value"}), None)],
            iter.rest()
        );
        let _ = iter.next_len(2);
        assert_eq!(vec![Op::insert(json!({"key": "value"}), None)], iter.rest());
        let _ = iter.next_len(10);
        assert_eq!(Vec::<Op>::new(), iter.rest());
        let _ = iter.next_len(2);
        assert_eq!(Vec::<Op>::new(), iter.rest());
    }
}
