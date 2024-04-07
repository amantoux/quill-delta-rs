use std::{cmp::min, fmt::Display};

use serde_derive::Serialize;
use serde_json::Value;

use crate::{
    attributes::AttributesMap,
    iter::Iterator,
    op::{Op, OpType},
};

/// Implementation of Quill editor Delta format
///
/// Refer to official [documentation](https://quilljs.com/docs/delta) for more details.
///
/// > Deltas are a simple, yet expressive format that can be used to describe Quill's contents and changes.
/// > The format is a strict subset of JSON, is human readable, and easily parsible by machines.
/// > Deltas can describe any Quill document, includes all text and formatting information, without the ambiguity and complexity of HTML.
#[derive(Default, Debug, Serialize, Clone, PartialEq)]
pub struct Delta {
    ops: Vec<Op>,
}

impl Delta {
    /// Create an empty [Delta].
    pub fn new() -> Self {
        Delta { ops: Vec::new() }
    }

    pub fn ops(&self) -> &Vec<Op> {
        &self.ops
    }

    /// Push an [Op] in the [Delta].
    ///
    /// Basic compression is applied if delete, retain or insert operation are pushed while
    /// last operation was similar.
    ///
    /// If insert is pushed after a delete, the insert will be inserted before the delete.
    ///
    /// # Example
    ///
    /// ```
    /// use serde_json::Value;
    /// use quill_delta_rs::{delta::Delta, collections, op::Op};
    ///
    /// let mut delta = Delta::new();
    /// delta
    ///     .insert("a".into(), Some(collections!("bold" => Value::Bool(true))))
    ///     .delete(3)
    ///     .push(Op::insert(
    ///         "b".into(),
    ///         Some(collections!("bold"=>Value::Bool(true))),
    ///     ));
    /// assert_eq!(2, delta.ops().len());
    /// assert_eq!(
    ///     Op::insert("ab".into(), Some(collections!("bold" => Value::Bool(true)))),
    ///     delta.ops()[0],
    /// );
    /// ```
    pub fn push(&mut self, new_op: Op) -> &mut Self {
        if self.ops.is_empty() {
            self.ops.push(new_op);
            return self;
        }
        let mut index = self.ops.len();
        let mut last_op = &mut self.ops[index - 1];

        if new_op.is_delete() && last_op.is_delete() {
            let _ = std::mem::replace(last_op, Op::delete(new_op.len() + last_op.len()));
            return self;
        }

        // Since it does not matter if we insert before or after deleting at the same index,
        // always prefer to insert first
        if last_op.is_delete() && new_op.is_insert() {
            index -= 1;
            if index == 0 {
                self.ops.insert(0, new_op);
                return self;
            }
            last_op = &mut self.ops[index - 1];
        }

        if new_op.attributes() == last_op.attributes() {
            if new_op.is_insert()
                && last_op.is_insert()
                && new_op.value().is_string()
                && last_op.value().is_string()
            {
                let mut merged_text = last_op.value_as_string().clone();
                merged_text.push_str(&new_op.value_as_string());
                let merged_op = Op::insert(Value::from(merged_text), new_op.attributes());
                let _ = std::mem::replace(last_op, merged_op);
                return self;
            }
            if last_op.is_retain() && new_op.is_retain() {
                let merged_op = Op::retain(last_op.len() + new_op.len(), new_op.attributes());
                let _ = std::mem::replace(last_op, merged_op);
                return self;
            }
        }

        if index == self.ops.len() {
            self.ops.push(new_op);
        } else {
            self.ops.insert(index, new_op);
        }

        self
    }

    /// Push an insert [Op] in the [Delta].
    pub fn insert(&mut self, value: Value, attributes: Option<AttributesMap>) -> &mut Self {
        if value.is_null() {
            return self;
        }
        if value.is_string() && value.as_str().unwrap().trim().is_empty() {
            return self;
        }

        self.push(Op::insert(value, attributes))
    }

    /// Push a delete [Op] in the [Delta]
    pub fn delete(&mut self, length: usize) -> &mut Self {
        self.push(Op::delete(length))
    }

    /// Push a retain [Op] in the [Delta]
    pub fn retain(&mut self, length: usize, attributes: Option<AttributesMap>) -> &mut Self {
        self.push(Op::retain(length, attributes))
    }

    /// Remove any trail plain retain.
    ///
    /// # Example
    ///
    /// ```
    /// use serde_json::Value;
    /// use quill_delta_rs::{collections, delta::Delta};
    ///
    /// let mut delta = Delta::new();
    /// delta.insert("Test".into(), None).retain(4, None);
    /// let mut exp = Delta::new();
    /// exp.insert("Test".into(), None);
    /// assert_eq!(&exp, delta.chop());
    /// ```
    pub fn chop(&mut self) -> &mut Self {
        if self.ops.is_empty() {
            return self;
        }
        let last_op = self.ops.last().unwrap();
        if last_op.is_retain() && last_op.attributes().is_none() {
            self.ops.remove(self.ops.len() - 1);
        }
        self
    }

    /// Folds every element into an accumulator by applying an operation,
    /// returning the final result.
    ///
    /// `fold()` takes two arguments: an initial value, and a closure with two arguments:
    /// an ‘accumulator’, and an [Op]. The closure returns the value that the accumulator
    /// should have for the next iteration.
    /// The initial value is the value the accumulator will have on the first call.
    ///
    /// After applying this closure to every element of the iterator, fold() returns the accumulator.
    ///
    /// This operation is sometimes called ‘reduce’ or ‘inject’.
    pub fn fold<T, F>(&self, init: T, f: F) -> T
    where
        F: FnMut(T, &Op) -> T,
    {
        self.ops.iter().fold(init, f)
    }

    /// The accumulated length of all [Op]s
    ///
    /// # Example
    ///
    /// ```
    /// use quill_delta_rs::delta::Delta;
    ///
    /// let mut delta = Delta::new();
    /// delta.insert("Text".into(), None).delete(3).retain(4, None);
    /// assert_eq!(11, delta.len());
    /// ```
    pub fn len(&self) -> usize {
        self.fold(0, |length, op| length + op.len())
    }

    /// Whether this contains no non-empty [Op]s
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The length of resulting change if [Delta] were to be applying to a insert-only [Delta]
    ///
    /// # Example
    ///
    /// ```
    /// use quill_delta_rs::delta::Delta;
    ///
    /// let mut delta = Delta::new();
    /// delta.insert("Text".into(), None).delete(3).retain(4, None);
    /// assert_eq!(1, delta.change_len());
    /// ```
    pub fn change_len(&self) -> usize {
        self.fold(0, |length, op| {
            if op.is_insert() {
                return length + op.len();
            }
            if op.is_delete() {
                return length - op.len();
            }
            length
        })
    }

    /// Get plain text of this [Delta]
    pub fn plain_text(&self) -> String {
        let mut plain_text = String::new();
        for op in &self.ops {
            if op.is_text_insert() {
                plain_text.push_str(&op.value_as_string().clone());
            } else {
                plain_text.push('\n');
            }
        }
        plain_text
    }

    /// Get a slice of the [Delta]'s operations between
    /// a [start] inclusive index and [end] exclusive index
    ///
    /// If [end] is not specified, [usize::MAX] will be used
    ///
    /// # Example
    ///
    /// ```
    /// use quill_delta_rs::delta::Delta;
    /// use serde_json::json;
    ///
    /// let mut delta = Delta::new();
    /// delta
    ///     .insert("Text".into(), None)
    ///     .delete(3)
    ///     .retain(4, None)
    ///     .insert(json!({"key": "value"}), None);
    /// let mut expected = Delta::new();
    /// expected.insert("ext".into(), None).delete(2);
    /// assert_eq!(expected, delta.slice(1, Some(6)))
    /// ```
    pub fn slice(&self, start: usize, end: Option<usize>) -> Self {
        let mut ops = Vec::new();
        let mut iter = crate::iter::Iterator::from(self.ops.clone());
        let mut index = 0;
        let end = end.unwrap_or(usize::MAX);
        while index < end && iter.has_next() {
            let next_op: Op;
            if index < start {
                next_op = iter.next_len(start - index);
                index += next_op.len();
            } else {
                next_op = iter.next_len(end - index);
                index += next_op.len();
                ops.push(next_op);
            }
        }
        Delta::from(ops)
    }

    /// Concatenate a [Delta] to the this one.
    ///
    /// First [Op] of other and last [Op] of this delta are merged
    /// when possible.
    ///
    /// # Example
    ///
    /// ```
    /// use quill_delta_rs::delta::Delta;
    /// use quill_delta_rs::attributes::AttributesMap;
    /// use serde_json::json;
    ///
    /// let mut delta = Delta::new();
    /// delta.insert("Test".into(), Some(AttributesMap::from([("bold", true.into())])));
    /// let original = delta.clone();
    /// let mut concat = Delta::new();
    /// concat.insert("!".into(), Some(AttributesMap::from([("bold", true.into())])));
    /// let mut expected = Delta::new();
    /// expected.insert("Test!".into(), Some(AttributesMap::from([("bold", true.into())])));
    /// assert_eq!(expected, delta.concat(concat));
    /// ```
    pub fn concat(&self, other: Delta) -> Self {
        let mut delta = self.clone();
        let mut other = other.clone();
        if !other.is_empty() {
            // benefit from compression on first element of other
            delta.push(other.ops.first().unwrap().clone());
            other.ops.drain(0..1);
            delta.ops.append(&mut other.ops);
        }
        delta
    }

    /// Combines this [Delta] with another [Delta]
    ///
    /// The other [Delta] is applied over this [Delta] resulting in a combined [Delta]
    ///
    /// # Example
    ///
    /// ```
    /// use quill_delta_rs::{
    ///     delta::Delta,
    ///     attributes::AttributesMap,
    ///     op::Op
    /// };
    ///
    /// use serde_json::json;
    ///
    /// let a = Delta::from(vec![
    ///     Op::insert("A".into(), Some(AttributesMap::from([("bold", true.into())]))),
    ///     Op::insert("B".into(), None),
    ///     Op::insert("C".into(), Some(AttributesMap::from([("bold", true.into())]))),
    ///     Op::delete(1),
    /// ]);
    /// let b = Delta::from(vec![
    ///     Op::retain(
    ///         1,
    ///         Some(AttributesMap::from([("color", "red".into())])),
    ///     ),
    ///     Op::retain(2, None),
    ///     Op::insert("D".into(), None)
    /// ]);
    /// let expected = Delta::from(vec![
    ///     Op::insert(
    ///         "A".into(),
    ///         Some(AttributesMap::from([
    ///             ("bold", true.into()),
    ///             ("color", "red".into()),
    ///         ])),
    ///     ),
    ///     Op::insert("B".into(), None),
    ///     Op::insert("C".into(), Some(AttributesMap::from([("bold",true.into())]))),
    ///     Op::insert("D".into(), None),
    ///     Op::delete(1),
    /// ]);
    /// assert_eq!(expected, a.compose(&b));
    /// ```
    pub fn compose(&self, other: &Delta) -> Delta {
        let mut iter = Iterator::from(self.ops.clone());
        let mut other_iter = Iterator::from(other.ops.clone());

        let mut combined_ops = Vec::new();
        let first_other = other_iter.peek();
        if first_other.is_some()
            && first_other.unwrap().is_retain()
            && first_other.unwrap().attributes().is_none()
        {
            // if other first op us is plain retains, use self's ops for the length of the retain
            let first_other = first_other.unwrap();
            let mut first_other_len_left = first_other.len();
            while matches!(iter.peek_type(), OpType::INSERT(_))
                && iter.peek_len() <= first_other_len_left
            {
                first_other_len_left -= iter.peek_len();
                combined_ops.push(iter.next().unwrap());
            }
            if first_other.len() - first_other_len_left > 0 {
                other_iter.next_len(first_other.len() - first_other_len_left);
            }
        }

        let mut delta = Delta::from(combined_ops);

        while iter.has_next() || other_iter.has_next() {
            if matches!(other_iter.peek_type(), OpType::INSERT(_)) {
                let other_next = other_iter.next().unwrap();
                delta.push(other_next);
            } else if matches!(iter.peek_type(), OpType::DELETE(_)) {
                let self_next = iter.next().unwrap();
                delta.push(self_next);
            } else {
                let length = min(iter.peek_len(), other_iter.peek_len());
                let self_op = iter.next_len(length);
                let other_op = other_iter.next_len(length);

                if other_op.is_retain() {
                    // Preserve null when composing with a retain, otherwise remove it for inserts
                    let attributes = AttributesMap::compose(
                        self_op.attributes().unwrap_or_default(),
                        other_op.attributes().unwrap_or_default(),
                        self_op.is_retain(),
                    );
                    let new_op = if self_op.is_retain() {
                        Op::retain(length, attributes)
                    } else {
                        Op::insert(self_op.value(), attributes)
                    };
                    delta.push(new_op.clone());
                    // Optimization if rest of other is just retain
                    if !other_iter.has_next() && delta.ops.last() == Some(&new_op) {
                        let rest = Delta::from(iter.rest());
                        let mut delta = delta.concat(rest);
                        delta.chop();
                        return delta;
                    }
                } else if other_op.is_delete() && self_op.is_retain() {
                    delta.push(other_op);
                }
            }
        }
        delta.chop();
        delta
    }

    /// Get the invert [Delta] of the this [Delta] on a `base` [Delta]
    ///
    /// The invert is such that composing `base` with `this` and composing this result with the
    /// invert results in the `base`
    ///
    /// # Examples
    ///
    /// ## Invert insert
    ///
    /// ```
    /// use quill_delta_rs::{
    ///     delta::Delta,
    ///     attributes::AttributesMap,
    ///     op::Op
    /// };
    ///
    /// use serde_json::json;
    ///
    /// let delta = Delta::from(vec![Op::retain(2, None), Op::insert("A".into(), None)]);
    /// let base = Delta::from(vec![Op::insert("123456".into(), None)]);
    /// let expected = Delta::from(vec![Op::retain(2, None), Op::delete(1)]);
    /// assert_eq!(expected, delta.invert(&base));
    /// let inverted = delta.invert(&base);
    /// assert_eq!(base, base.compose(&delta).compose(&inverted))
    /// ```
    ///
    /// ## Invert delete
    /// ```
    /// use quill_delta_rs::{
    ///     delta::Delta,
    ///     attributes::AttributesMap,
    ///     op::Op
    /// };
    ///
    /// use serde_json::json;
    ///
    /// let delta = Delta::from(vec![Op::retain(2, None), Op::delete(3)]);
    /// let base = Delta::from(vec![Op::insert("123456".into(), None)]);
    /// let expected = Delta::from(vec![Op::retain(2, None), Op::insert("345".into(), None)]);
    /// assert_eq!(expected, delta.invert(&base));
    /// let inverted = delta.invert(&base);
    /// assert_eq!(base, base.compose(&delta).compose(&inverted))
    /// ```
    ///
    /// ## Invert retain
    ///
    /// ```
    /// use quill_delta_rs::{
    ///     delta::Delta,
    ///     attributes::AttributesMap,
    ///     op::Op
    /// };
    ///
    /// use serde_json::Value;
    ///
    /// let delta = Delta::from(vec![
    ///     Op::retain(2, None),
    ///     Op::retain(3, Some(AttributesMap::from([("bold", true.into())]))),
    /// ]);
    /// let base = Delta::from(vec![Op::insert("123456".into(), None)]);
    /// let expected = Delta::from(vec![
    ///     Op::retain(2, None),
    ///     Op::retain(3, Some(AttributesMap::from([("bold", Value::Null)]))),
    /// ]);
    /// let inverted = delta.invert(&base);
    /// assert_eq!(expected, inverted);
    /// assert_eq!(base, base.compose(&delta).compose(&inverted))
    /// ```
    pub fn invert(&self, base: &Delta) -> Delta {
        let mut inverted = Delta::new();
        self.fold(0, |base_index, op| {
            if op.is_insert() {
                inverted.delete(op.len());
            } else if op.is_retain() && op.attributes().is_none() {
                inverted.retain(op.len(), None);
                return base_index + op.len();
            } else if op.is_delete() || (op.is_retain() && op.attributes().is_some()) {
                let length = op.len();
                let slice = base.slice(base_index, Some(base_index + length));
                for base_op in slice.ops {
                    if op.is_delete() {
                        inverted.push(base_op);
                    } else if op.is_retain() && op.attributes().is_some() {
                        inverted.retain(
                            base_op.len(),
                            Some(AttributesMap::invert(
                                op.attributes().unwrap(),
                                base_op.attributes().unwrap_or_default(),
                            )),
                        );
                    }
                }
                return base_index + length;
            }
            base_index
        });
        inverted.chop();
        inverted
    }
}

impl From<Vec<Op>> for Delta {
    fn from(value: Vec<Op>) -> Self {
        Delta { ops: value }
    }
}

impl Display for Delta {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for op in &self.ops {
            f.write_fmt(format_args!("{}\n", op))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod push_tests {
    use serde_json::Value;

    use crate::{collections, op::Op};

    use super::Delta;

    #[test]
    fn from_ops() {
        let delta = Delta::from(vec![
            Op::retain(2, None),
            Op::delete(3),
            Op::insert("a".into(), None),
        ]);
        assert_eq!(3, delta.ops().len());
    }

    #[test]
    fn push_on_empty() {
        let mut delta = Delta::new();
        delta.push(Op::insert(Value::from("test"), None));
        assert_eq!(1, delta.ops().len());
    }

    #[test]
    fn push_insert_on_delete() {
        let mut delta = Delta::new();
        delta.delete(3).push(Op::insert("b".into(), None));
        assert_eq!(2, delta.ops().len());
        assert_eq!(Op::insert("b".into(), None), delta.ops()[0],);
    }

    #[test]
    fn push_insert_on_insert_with_matching_attributes_plus_delete() {
        let mut delta = Delta::new();
        delta
            .insert("a".into(), Some(collections!("bold" => Value::Bool(true))))
            .delete(3)
            .push(Op::insert(
                "b".into(),
                Some(collections!("bold"=>Value::Bool(true))),
            ));
        assert_eq!(2, delta.ops().len());
        assert_eq!(
            Op::insert("ab".into(), Some(collections!("bold" => Value::Bool(true)))),
            delta.ops()[0],
        );
    }

    #[test]
    fn push_insert_on_insert_with_different_attributes_plus_delete() {
        let mut delta = Delta::new();
        delta
            .insert("a".into(), Some(collections!("bold" => Value::Bool(true))))
            .delete(3)
            .push(Op::insert(
                "b".into(),
                Some(collections!("italic"=>Value::Bool(true))),
            ));
        assert_eq!(3, delta.ops().len());
        assert_eq!(
            Op::insert("a".into(), Some(collections!("bold" => Value::Bool(true)))),
            delta.ops()[0],
        );
        assert_eq!(
            Op::insert(
                "b".into(),
                Some(collections!("italic" => Value::Bool(true)))
            ),
            delta.ops()[1],
        );
        assert_eq!(Op::delete(3), delta.ops()[2],);
    }

    #[test]
    fn push_consecutive_delete() {
        let mut delta = Delta::new();
        delta.delete(2).push(Op::delete(3));
        assert_eq!(1, delta.ops().len());
        assert_eq!(Op::delete(5), delta.ops()[0]);
    }

    #[test]
    fn push_consecutive_text() {
        let mut delta = Delta::new();
        delta
            .insert("a".into(), None)
            .push(Op::insert("b".into(), None));
        assert_eq!(1, delta.ops().len());
        assert_eq!(Op::insert("ab".into(), None), delta.ops()[0]);
    }

    #[test]
    fn push_consecutive_text_matching_attributes() {
        let mut delta = Delta::new();
        delta
            .insert("a".into(), Some(collections!("bold" => Value::Bool(true))))
            .push(Op::insert(
                "b".into(),
                Some(collections!("bold"=>Value::Bool(true))),
            ));
        assert_eq!(1, delta.ops().len());
        assert_eq!(
            Op::insert("ab".into(), Some(collections!("bold" => Value::Bool(true)))),
            delta.ops()[0],
        );
    }

    #[test]
    fn push_consecutive_retain_matching_attributes() {
        let mut delta = Delta::new();
        delta
            .retain(1, Some(collections!("bold" => Value::Bool(true))))
            .push(Op::retain(
                3,
                Some(collections!("bold" => Value::Bool(true))),
            ));
        assert_eq!(1, delta.ops().len());
        assert_eq!(
            Op::retain(4, Some(collections!("bold" =>  Value::Bool(true)))),
            delta.ops()[0],
        );
    }

    #[test]
    fn push_consecutive_test_different_attributes() {
        let mut delta = Delta::new();
        delta
            .insert("a".into(), Some(collections!("bold" => Value::Bool(true))))
            .push(Op::insert(
                "b".into(),
                Some(collections!("italic" => Value::Bool(true))),
            ));
        assert_eq!(2, delta.ops().len());
    }

    #[test]
    fn push_consecutive_retain_different_attributes() {
        let mut delta = Delta::new();
        delta
            .retain(2, Some(collections!("bold" => Value::Bool(true))))
            .push(Op::retain(
                3,
                Some(collections!("italic" => Value::Bool(true))),
            ));
        assert_eq!(2, delta.ops().len());
    }
}

#[cfg(test)]
mod helpers_tests {
    use serde_json::{json, Value};

    use crate::{collections, op::Op};

    use super::Delta;

    #[test]
    fn retain() {
        let mut delta = Delta::new();
        delta.insert("Test".into(), None).retain(4, None);
        let mut exp = Delta::new();
        exp.insert("Test".into(), None);
        assert_eq!(&exp, delta.chop());
    }

    #[test]
    fn insert() {
        let mut delta = Delta::new();
        delta.insert("Test".into(), None);
        assert_eq!(&delta.clone(), delta.chop());
    }

    #[test]
    fn insert_merge() {
        let mut delta = Delta::new();
        delta.insert("Test".into(), None).insert("!".into(), None);
        assert_eq!(Delta::from(vec!(Op::insert("Test!".into(), None))), delta);
    }

    #[test]
    fn retain_with_attribute() {
        let mut delta = Delta::new();
        delta
            .insert("Test".into(), None)
            .retain(4, Some(collections!("bold" => Value::Bool(true))));
        assert_eq!(&delta.clone(), delta.chop())
    }

    #[test]
    fn is_not_empty() {
        let mut delta = Delta::new();
        delta.insert("Text".into(), None).delete(3).retain(4, None);
        assert!(!delta.is_empty());
    }

    #[test]
    fn is_empty() {
        let delta = Delta::new();
        assert!(delta.is_empty());
    }

    #[test]
    fn len() {
        let mut delta = Delta::new();
        delta.insert("Text".into(), None).delete(3).retain(4, None);
        assert_eq!(11, delta.len());
    }

    #[test]
    fn change_len() {
        let mut delta = Delta::new();
        delta.insert("Text".into(), None).delete(3).retain(4, None);
        assert_eq!(1, delta.change_len());
    }

    #[test]
    fn plain_text() {
        let mut delta = Delta::new();
        delta
            .insert("Text".into(), None)
            .delete(3)
            .retain(4, None)
            .insert(json!({"key": "value"}), None);
        assert_eq!("Text\n\n\n", delta.plain_text());
    }

    #[test]
    fn slice() {
        let mut delta = Delta::new();
        delta
            .insert("Text".into(), None)
            .delete(3)
            .retain(4, None)
            .insert(json!({"key": "value"}), None);
        let mut expected = Delta::new();
        expected.insert("ext".into(), None).delete(2);
        assert_eq!(expected, delta.slice(1, Some(6)))
    }

    #[test]
    fn slice_until_end() {
        let mut delta = Delta::new();
        delta
            .insert("Text".into(), None)
            .delete(3)
            .retain(4, None)
            .insert(json!({"key": "value"}), None);
        let mut expected = Delta::new();
        expected
            .insert("ext".into(), None)
            .delete(3)
            .retain(4, None)
            .insert(json!({"key": "value"}), None);
        assert_eq!(expected, delta.slice(1, None))
    }

    #[test]
    fn concat_empty_delta() {
        let mut delta = Delta::new();
        delta.insert("Test".into(), None);
        let concat = Delta::new();
        assert_eq!(delta, delta.concat(concat))
    }

    #[test]
    fn concat_unmergeable() {
        let mut delta = Delta::new();
        delta.insert("Test".into(), None);
        let original = Delta::from(delta.ops.clone());
        let mut concat = Delta::new();
        concat.insert("!".into(), Some(collections!("bold" => true.into())));
        let mut expected = Delta::new();
        expected
            .insert("Test".into(), None)
            .insert("!".into(), Some(collections!("bold" => true.into())));
        assert_eq!(expected, delta.concat(concat));
        assert_eq!(original, delta);
    }

    #[test]
    fn concat_mergeable() {
        let mut delta = Delta::new();
        delta.insert("Test".into(), Some(collections!("bold" => true.into())));
        let original = delta.clone();
        let mut concat = Delta::new();
        concat.insert("!".into(), Some(collections!("bold" => true.into())));
        let mut expected = Delta::new();
        expected.insert("Test!".into(), Some(collections!("bold" => true.into())));
        assert_eq!(expected, delta.concat(concat));
        assert_eq!(original, delta)
    }
}

#[cfg(test)]
mod compose_tests {
    use std::vec;

    use serde_json::Value;

    use crate::{collections, op::Op};

    use super::Delta;

    // 0 length white space
    // placeholder for embedded in diff (no implementation so far)
    const EMBED_CODE: u32 = 0x200b;

    fn empty_embed() -> Value {
        Value::from(char::from_u32(EMBED_CODE).unwrap().to_string())
    }

    #[test]
    fn insert_insert() {
        let a = Delta::from(vec![Op::insert("A".into(), None)]);
        let b = Delta::from(vec![Op::insert("B".into(), None)]);
        let expected = Delta::from(vec![Op::insert("BA".into(), None)]);
        assert_eq!(expected, a.compose(&b));
    }

    #[test]
    fn insert_retain() {
        let a = Delta::from(vec![Op::insert("A".into(), None)]);
        let b = Delta::from(vec![Op::retain(
            1,
            Some(collections!(
                "bold" => true.into(),
                "color" => "red".into(),
                "font" => Value::Null
            )),
        )]);
        let expected = Delta::from(vec![Op::insert(
            "A".into(),
            Some(collections!(
                "bold" => true.into(),
                "color" => "red".into()
            )),
        )]);
        assert_eq!(expected, a.compose(&b))
    }

    #[test]
    fn insert_delete() {
        let a = Delta::from(vec![Op::insert("A".into(), None)]);
        let b = Delta::from(vec![Op::delete(1)]);
        assert_eq!(Delta::new(), a.compose(&b));
    }

    #[test]
    fn delete_insert() {
        let a = Delta::from(vec![Op::delete(1)]);
        let b = Delta::from(vec![Op::insert("B".into(), None)]);
        let expected = Delta::from(vec![Op::insert("B".into(), None), Op::delete(1)]);
        assert_eq!(expected, a.compose(&b));
    }

    #[test]
    fn delete_retain() {
        let a = Delta::from(vec![Op::delete(1)]);
        let b = Delta::from(vec![Op::retain(
            1,
            Some(collections!("bold" => true.into(), "color" => "red".into())),
        )]);
        let expected = Delta::from(vec![
            Op::delete(1),
            Op::retain(
                1,
                Some(collections!("bold" => true.into(), "color" => "red".into())),
            ),
        ]);
        assert_eq!(expected, a.compose(&b))
    }

    #[test]
    fn delete_delete() {
        let a = Delta::from(vec![Op::delete(1)]);
        let b = Delta::from(vec![Op::delete(1)]);
        assert_eq!(Delta::from(vec![Op::delete(2)]), a.compose(&b))
    }

    #[test]
    fn retain_insert() {
        let a = Delta::from(vec![Op::retain(
            1,
            Some(collections!("color" => "blue".into())),
        )]);
        let b = Delta::from(vec![Op::insert("B".into(), None)]);
        let expected = Delta::from(vec![
            Op::insert("B".into(), None),
            Op::retain(1, Some(collections!("color" => "blue".into()))),
        ]);
        assert_eq!(expected, a.compose(&b));
    }

    #[test]
    fn retain_rertain() {
        let a = Delta::from(vec![Op::retain(
            1,
            Some(collections!("color" => "blue".into())),
        )]);
        let b = Delta::from(vec![Op::retain(
            1,
            Some(collections!(
                "color" => "red".into(),
                "bold" => true.into(),
                "fonr" => Value::Null,
            )),
        )]);
        let expected = Delta::from(vec![Op::retain(
            1,
            Some(collections!(
                "color" => "red".into(),
                "bold" => true.into(),
                "fonr" => Value::Null,
            )),
        )]);
        assert_eq!(expected, a.compose(&b))
    }

    #[test]
    fn retain_delete() {
        let a = Delta::from(vec![Op::retain(
            1,
            Some(collections!("color" => "blue".into())),
        )]);
        let b = Delta::from(vec![Op::delete(1)]);
        assert_eq!(Delta::from(vec![Op::delete(1)]), a.compose(&b))
    }

    #[test]
    fn insert_in_middle_of_text() {
        let a = Delta::from(vec![Op::insert("Hello".into(), None)]);
        let b = Delta::from(vec![Op::retain(3, None), Op::insert("x".into(), None)]);
        assert_eq!(
            Delta::from(vec![Op::insert("Helxlo".into(), None)]),
            a.compose(&b)
        )
    }

    #[test]
    fn insert_delete_ordering() {
        let a = Delta::from(vec![Op::insert("Hello".into(), None)]);
        let insert_first = Delta::from(vec![
            Op::retain(3, None),
            Op::insert("X".into(), None),
            Op::delete(1),
        ]);
        let delete_first = Delta::from(vec![
            Op::retain(3, None),
            Op::delete(1),
            Op::insert("X".into(), None),
        ]);
        let expected = Delta::from(vec![Op::insert("HelXo".into(), None)]);
        assert_eq!(expected, a.compose(&insert_first));
        assert_eq!(expected, a.compose(&delete_first));
    }

    #[test]
    fn insert_embed() {
        let a = Delta::from(vec![Op::insert(
            empty_embed(),
            Some(collections!("src" => "https://www.mozilla.org".into())),
        )]);
        let b = Delta::from(vec![Op::retain(
            1,
            Some(collections!("alt" => "Mozilla".into())),
        )]);
        let expected = Delta::from(vec![Op::insert(
            empty_embed(),
            Some(
                collections!("src" => "https://www.mozilla.org".into(), "alt" => "Mozilla".into()),
            ),
        )]);
        assert_eq!(expected, a.compose(&b));
    }

    #[test]
    fn delete_entire_text() {
        let a = Delta::from(vec![Op::retain(4, None), Op::insert("Hello".into(), None)]);
        let b = Delta::from(vec![Op::delete(9)]);
        assert_eq!(Delta::from(vec![Op::delete(4)]), a.compose(&b));
    }

    #[test]
    fn retain_more_than_text_length() {
        let a = Delta::from(vec![Op::insert("Hello".into(), None)]);
        let b = Delta::from(vec![Op::retain(10, None)]);
        assert_eq!(a, a.compose(&b))
    }

    #[test]
    fn retain_empty_embed() {
        let a = Delta::from(vec![Op::insert(empty_embed(), None)]);
        let b = Delta::from(vec![Op::retain(1, None)]);
        assert_eq!(a, a.compose(&b))
    }

    #[test]
    fn remove_all_attributes() {
        let a = Delta::from(vec![Op::insert(
            "A".into(),
            Some(collections!("bold" => true.into())),
        )]);
        let b = Delta::from(vec![Op::retain(
            1,
            Some(collections!("bold" => Value::Null)),
        )]);
        assert_eq!(
            Delta::from(vec![Op::insert("A".into(), None)]),
            a.compose(&b)
        );
    }

    #[test]
    fn remove_all_embed_attributes() {
        let a = Delta::from(vec![Op::insert(
            empty_embed(),
            Some(collections!("src" => "https://mozilla.org".into())),
        )]);
        let b = Delta::from(vec![Op::retain(
            1,
            Some(collections!("src" => Value::Null)),
        )]);
        assert_eq!(
            Delta::from(vec![Op::insert(empty_embed(), None)]),
            a.compose(&b)
        );
    }

    #[test]
    fn immutability() {
        let a1 = Delta::from(vec![Op::insert(
            "Test".into(),
            Some(collections!("bold" => true.into())),
        )]);
        let a2 = Delta::from(vec![Op::insert(
            "Test".into(),
            Some(collections!("bold" => true.into())),
        )]);
        let b1 = Delta::from(vec![
            Op::retain(1, Some(collections!("color" => "red".into()))),
            Op::delete(2),
        ]);
        let b2 = Delta::from(vec![
            Op::retain(1, Some(collections!("color" => "red".into()))),
            Op::delete(2),
        ]);
        let expected = Delta::from(vec![
            Op::insert(
                "T".into(),
                Some(collections!("color" => "red".into(), "bold" => true.into())),
            ),
            Op::insert("t".into(), Some(collections!("bold" => true.into()))),
        ]);
        assert_eq!(expected, a1.compose(&b1));
        assert_eq!(a1, a2);
        assert_eq!(b1, b2);
    }

    #[test]
    fn retain_start_optimization() {
        let a = Delta::from(vec![
            Op::insert("A".into(), Some(collections!("bold" => true.into()))),
            Op::insert("B".into(), None),
            Op::insert("C".into(), Some(collections!("bold" => true.into()))),
            Op::delete(1),
        ]);
        let b = Delta::from(vec![Op::retain(3, None), Op::insert("D".into(), None)]);
        let expected = Delta::from(vec![
            Op::insert("A".into(), Some(collections!("bold" => true.into()))),
            Op::insert("B".into(), None),
            Op::insert("C".into(), Some(collections!("bold" => true.into()))),
            Op::insert("D".into(), None),
            Op::delete(1),
        ]);
        assert_eq!(expected, a.compose(&b));
    }

    #[test]
    fn retain_start_optimization_split() {
        let a = Delta::from(vec![
            Op::insert("A".into(), Some(collections!("bold" => true.into()))),
            Op::insert("B".into(), None),
            Op::insert("C".into(), Some(collections!("bold" => true.into()))),
            Op::retain(5, None),
            Op::delete(1),
        ]);
        let b = Delta::from(vec![Op::retain(4, None), Op::insert("D".into(), None)]);
        let expected = Delta::from(vec![
            Op::insert("A".into(), Some(collections!("bold" => true.into()))),
            Op::insert("B".into(), None),
            Op::insert("C".into(), Some(collections!("bold" => true.into()))),
            Op::retain(1, None),
            Op::insert("D".into(), None),
            Op::retain(4, None),
            Op::delete(1),
        ]);
        assert_eq!(expected, a.compose(&b))
    }

    #[test]
    fn retain_end_optimization() {
        let a = Delta::from(vec![
            Op::insert("A".into(), Some(collections!("bold" => true.into()))),
            Op::insert("B".into(), None),
            Op::insert("C".into(), Some(collections!("bold" => true.into()))),
        ]);
        let b = Delta::from(vec![Op::delete(1)]);
        let expected = Delta::from(vec![
            Op::insert("B".into(), None),
            Op::insert("C".into(), Some(collections!("bold" => true.into()))),
        ]);
        assert_eq!(expected, a.compose(&b));
    }

    #[test]
    fn retain_end_optimization_join() {
        let a = Delta::from(vec![
            Op::insert("A".into(), Some(collections!("bold" => true.into()))),
            Op::insert("B".into(), None),
            Op::insert("C".into(), Some(collections!("bold" => true.into()))),
            Op::insert("D".into(), None),
            Op::insert("E".into(), Some(collections!("bold" => true.into()))),
        ]);
        let b = Delta::from(vec![Op::retain(1, None), Op::delete(1)]);
        let expected = Delta::from(vec![
            Op::insert("AC".into(), Some(collections!("bold" => true.into()))),
            Op::insert("D".into(), None),
            Op::insert("E".into(), Some(collections!("bold" => true.into()))),
        ]);
        assert_eq!(expected, a.compose(&b))
    }
}

#[cfg(test)]
mod invert_tests {
    use serde_json::Value;

    use crate::{collections, op::Op};

    use super::Delta;

    #[test]
    fn insert() {
        let delta = Delta::from(vec![Op::retain(2, None), Op::insert("A".into(), None)]);
        let base = Delta::from(vec![Op::insert("123456".into(), None)]);
        let expected = Delta::from(vec![Op::retain(2, None), Op::delete(1)]);
        assert_eq!(expected, delta.invert(&base));
        let inverted = delta.invert(&base);
        assert_eq!(base, base.compose(&delta).compose(&inverted))
    }

    #[test]
    fn delete() {
        let delta = Delta::from(vec![Op::retain(2, None), Op::delete(3)]);
        let base = Delta::from(vec![Op::insert("123456".into(), None)]);
        let expected = Delta::from(vec![Op::retain(2, None), Op::insert("345".into(), None)]);
        assert_eq!(expected, delta.invert(&base));
        let inverted = delta.invert(&base);
        assert_eq!(base, base.compose(&delta).compose(&inverted))
    }

    #[test]
    fn retain() {
        let delta = Delta::from(vec![
            Op::retain(2, None),
            Op::retain(3, Some(collections!("bold" => true.into()))),
        ]);
        let base = Delta::from(vec![Op::insert("123456".into(), None)]);
        let expected = Delta::from(vec![
            Op::retain(2, None),
            Op::retain(3, Some(collections!("bold" => Value::Null))),
        ]);
        let inverted = delta.invert(&base);
        assert_eq!(expected, inverted);
        assert_eq!(base, base.compose(&delta).compose(&inverted))
    }

    #[test]
    fn retain_on_delta_with_attributes() {
        let delta = Delta::from(vec![Op::retain(
            4,
            Some(collections!("italic" => true.into())),
        )]);
        let base = Delta::from(vec![
            Op::insert("123".into(), None),
            Op::insert("4".into(), Some(collections!("bold" => true.into()))),
        ]);
        let expected = Delta::from(vec![Op::retain(
            4,
            Some(collections!("italic" => Value::Null)),
        )]);
        assert_eq!(expected, delta.invert(&base));
        let inverted = delta.invert(&base);
        assert_eq!(base, base.compose(&delta).compose(&inverted))
    }

    #[test]
    fn combined() {
        let delta = Delta::from(vec![
            Op::retain(2, None),
            Op::delete(2),
            Op::insert("AB".into(), Some(collections!("italic" => true.into()))),
            Op::retain(
                2,
                Some(collections!("italic" => Value::Null, "bold" => true.into())),
            ),
            Op::retain(2, Some(collections!("color" => "red".into()))),
            Op::delete(1),
        ]);
        let base = Delta::from(vec![
            Op::insert("123".into(), Some(collections!("bold" => true.into()))),
            Op::insert("456".into(), Some(collections!("italic" => true.into()))),
            Op::insert(
                "789".into(),
                Some(collections!("color" => "red".into(), "bold" => true.into())),
            ),
        ]);
        let expected = Delta::from(vec![
            Op::retain(2, None),
            Op::insert("3".into(), Some(collections!("bold" => true.into()))),
            Op::insert("4".into(), Some(collections!("italic" => true.into()))),
            Op::delete(2),
            Op::retain(
                2,
                Some(collections!("italic" => true.into(), "bold" => Value::Null)),
            ),
            Op::retain(2, None),
            Op::insert(
                "9".into(),
                Some(collections!("color" => "red".into(), "bold" => true.into())),
            ),
        ]);
        assert_eq!(expected, delta.invert(&base));
        let inverted = delta.invert(&base);
        assert_eq!(base, base.compose(&delta).compose(&inverted))
    }
}
