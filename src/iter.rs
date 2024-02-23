use std::iter;

use serde_json::Value;

use crate::op::{Op, OpType};

pub struct Iterator {
    ops: Vec<Op>,
    // index of current operation in ops
    index: usize,
    // offset within current operation
    offset: usize,
}

impl Iterator {
    /// Create an iterator from a list of [Op]s
    pub fn from(operations: Vec<Op>) -> Self {
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
    /// use quill_delta_rs::{collections, op::Op, iter::Iterator};
    ///
    /// let ops = vec![
    ///     Op::insert(
    ///         "Hello".into(),
    ///         Some(collections!("bold" => Value::Bool(true))),
    ///     ),
    ///     Op::retain(3, None),
    ///     Op::delete(4),
    ///     Op::insert(json!({"key": "value"}), None),
    /// ];
    /// let mut iter = Iterator::from(ops);
    /// assert_eq!(
    ///     Op::insert("He".into(), Some(collections!("bold" => Value::Bool(true)))),
    ///     iter.next_len(2)
    /// );
    /// assert_eq!(
    ///     Op::insert(
    ///         "llo".into(),
    ///         Some(collections!("bold" => Value::Bool(true)))
    ///     ),
    ///     iter.next_len(10)
    /// );
    /// assert_eq!(Op::retain(1, None), iter.next_len(1));
    /// assert_eq!(Op::retain(2, None), iter.next_len(2));
    /// assert_eq!(Op::delete(2), iter.next_len(2));
    /// assert_eq!(Op::delete(2), iter.next_len(2));
    /// assert_eq!(Op::insert(json!({"key": "value"}), None), iter.next_len(10));
    /// assert_eq!(Op::retain_until_end(), iter.next_len(1))
    /// ```
    pub fn next_len(&mut self, length: usize) -> Op {
        if self.index >= self.ops.len() {
            return Op::retain_until_end();
        }

        let mut length = length;
        let next_op = self.ops.get(self.index).unwrap();
        let init_offset = self.offset;
        let op_len = next_op.len();

        if length >= op_len - init_offset {
            length = op_len - init_offset;
            self.index += 1;
            self.offset = 0;
        } else {
            self.offset += length;
        }

        if next_op.is_delete() {
            Op::delete(length)
        } else if next_op.is_retain() {
            Op::retain(length, next_op.attributes())
        } else if next_op.is_text_insert() {
            let sub_string: String = next_op
                .value_as_string()
                .chars()
                .skip(init_offset)
                .take(length)
                .collect();
            Op::insert(Value::from(sub_string), next_op.attributes())
        } else {
            Op::insert(next_op.value(), next_op.attributes())
        }
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
    pub fn peek_type(&self) -> OpType {
        if self.index >= self.ops.len() {
            OpType::RETAIN(usize::MAX)
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
    ///     collections,
    ///     iter::Iterator,
    ///     op::{Op, OpType},
    /// };
    ///
    /// let ops = vec![
    ///     Op::insert(
    ///         "Hello".into(),
    ///         Some(collections!("bold" => Value::Bool(true))),
    ///     ),
    ///     Op::retain(3, None),
    ///     Op::delete(4),
    ///     Op::insert(json!({"key": "value"}), None),
    /// ];
    /// let mut iter = Iterator::from(ops);
    /// let _ = iter.next_len(2);
    /// assert_eq!(
    ///     vec![
    ///         Op::insert(
    ///             "llo".into(),
    ///             Some(collections!("bold" => Value::Bool(true))),
    ///         ),
    ///         Op::retain(3, None),
    ///         Op::delete(4),
    ///         Op::insert(json!({"key": "value"}), None),
    ///     ],
    ///     iter.rest()
    /// );
    /// ```
    pub fn rest(&mut self) -> Vec<Op> {
        if !self.has_next() {
            return Vec::new();
        }

        if self.offset == 0 {
            let slice = &self.ops.as_slice()[self.index..self.ops.len()];
            return Vec::from(slice);
        }

        let init_offset = self.offset;
        let init_index = self.index;
        let next_op = self.next().unwrap();
        let mut rest = Vec::from(&self.ops.as_slice()[self.index..self.ops.len()]);
        self.offset = init_offset;
        self.index = init_index;
        let mut returned = vec![next_op];
        returned.append(&mut rest);
        returned
    }
}

impl iter::Iterator for Iterator {
    type Item = Op;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.next_len(usize::MAX))
    }
}

#[cfg(test)]
mod tests {

    use serde_json::{json, Value};

    use crate::{
        collections,
        op::{Op, OpType},
    };

    use super::Iterator;

    #[test]
    fn next_len() {
        let ops = vec![
            Op::insert(
                "Hello".into(),
                Some(collections!("bold" => Value::Bool(true))),
            ),
            Op::retain(3, None),
            Op::delete(4),
            Op::insert(json!({"key": "value"}), None),
        ];
        let mut iter = Iterator::from(ops);
        assert_eq!(
            Op::insert("He".into(), Some(collections!("bold" => Value::Bool(true)))),
            iter.next_len(2)
        );
        assert_eq!(
            Op::insert(
                "llo".into(),
                Some(collections!("bold" => Value::Bool(true)))
            ),
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
        let ops = vec![Op::insert(
            "Hello".into(),
            Some(collections!("bold" => Value::Bool(true))),
        )];
        let mut iter = Iterator::from(ops);
        assert_eq!(
            &Op::insert(
                "Hello".into(),
                Some(collections!("bold" => Value::Bool(true))),
            ),
            iter.peek().unwrap()
        );
        assert_eq!(
            Op::insert(
                "Hello".into(),
                Some(collections!("bold" => Value::Bool(true))),
            ),
            iter.next().unwrap()
        );
    }

    #[test]
    fn peek_len() {
        let ops = vec![Op::insert(
            "Hello".into(),
            Some(collections!("bold" => Value::Bool(true))),
        )];
        let mut iter = Iterator::from(ops);
        assert_eq!("Hello".len(), iter.peek_len());
        assert_eq!(
            Op::insert(
                "Hello".into(),
                Some(collections!("bold" => Value::Bool(true))),
            ),
            iter.next().unwrap()
        );
        assert_eq!(usize::MAX, iter.peek_len());
    }

    #[test]
    fn peek_type() {
        let ops = vec![Op::insert(
            "Hello".into(),
            Some(collections!("bold" => Value::Bool(true))),
        )];
        let mut iter = Iterator::from(ops);
        assert_eq!(OpType::INSERT("Hello".into()), iter.peek_type());
        assert_eq!(
            Op::insert(
                "Hello".into(),
                Some(collections!("bold" => Value::Bool(true))),
            ),
            iter.next().unwrap()
        );
        assert_eq!(OpType::RETAIN(usize::MAX), iter.peek_type());
    }

    #[test]
    fn has_next() {
        let ops = vec![Op::insert(
            "Hello".into(),
            Some(collections!("bold" => Value::Bool(true))),
        )];
        let mut iter = Iterator::from(ops);
        assert_eq!(true, iter.has_next());
        assert_eq!(
            Op::insert(
                "Hello".into(),
                Some(collections!("bold" => Value::Bool(true))),
            ),
            iter.next().unwrap()
        );
        assert_eq!(false, iter.has_next());
    }

    #[test]
    fn rest() {
        let ops = vec![
            Op::insert(
                "Hello".into(),
                Some(collections!("bold" => Value::Bool(true))),
            ),
            Op::retain(3, None),
            Op::delete(4),
            Op::insert(json!({"key": "value"}), None),
        ];
        let mut iter = Iterator::from(ops);
        let _ = iter.next_len(2);
        assert_eq!(
            vec![
                Op::insert(
                    "llo".into(),
                    Some(collections!("bold" => Value::Bool(true))),
                ),
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
