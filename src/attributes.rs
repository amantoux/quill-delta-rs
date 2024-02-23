use std::{
    collections::{hash_map::IntoIter, HashMap, HashSet},
    fmt::Display,
    ops::Index,
};

use serde_derive::{Deserialize, Serialize};
use serde_json::Value;

/// Attributes of an operation
///
/// These include any formating attribute or companion data associated with
/// an inserted item
#[derive(Default, Debug, Serialize, Deserialize, Clone, PartialEq)]
pub struct AttributesMap(HashMap<String, Value>);

impl AttributesMap {
    pub fn new() -> Self {
        AttributesMap(HashMap::new())
    }

    /// Union of attributes, where conflicts are overriden by second argument
    ///
    /// Always keeps [Value::Null] of [a]
    /// If [keep_null] is `true`, [Value::Null] of [b] are kept
    ///
    /// # Example
    ///
    /// ```
    /// use quill_delta_rs::attributes::AttributesMap;
    /// use serde_json::Value;
    ///
    /// let mut a = AttributesMap::new();
    /// a.insert("keyA".into(), "a".into());
    /// a.insert("keyANull".into(), Value::Null);
    /// let mut b = AttributesMap::new();
    /// b.insert("keyA".into(), "ab".into());
    /// b.insert("keyB".into(), "b".into());
    /// b.insert("keyBNull".into(), Value::Null);
    /// let composed = AttributesMap::compose(a, b, false);
    /// assert_eq!(composed, Some(AttributesMap::from([
    ///   ("keyA", "ab".into()), ("keyB", "b".into()),
    /// ])));
    /// ```
    pub fn compose(a: AttributesMap, b: AttributesMap, keep_null: bool) -> Option<Self> {
        let mut attributes = b.clone();

        if !keep_null {
            let mut keys_to_remove: HashSet<String> = HashSet::new();
            for entry in &attributes {
                let (key, value) = entry;
                if matches!(value, Value::Null) {
                    keys_to_remove.insert(key);
                }
            }
            for key in keys_to_remove {
                attributes.remove(&key);
            }
        }

        for key in a.0.keys() {
            if !matches!(a[key], Value::Null) && !b.0.contains_key(key) {
                attributes.0.insert(key.clone(), a[key].clone());
            }
        }

        if attributes.is_empty() {
            None
        } else {
            Some(attributes)
        }
    }

    /// Intersection of attribute of 2 maps, the second argument values take precedence
    ///
    /// If key is present in first argument but absent of second, the diff will be [Value::Null]
    /// for the key
    ///
    /// # Example
    ///
    /// ```
    /// use quill_delta_rs::attributes::AttributesMap;
    /// use serde_json::Value;
    ///
    /// let mut a = AttributesMap::from([
    ///     ("keyA", Value::from("a")),
    ///     ("keyANull", Value::Null)
    /// ]);
    /// let mut b = AttributesMap::from([
    ///     ("keyA", Value::from("ab")),
    ///     ("keyB", Value::from("b")),
    ///     ("keyBNull", Value::Null)
    /// ]);
    /// let composed = AttributesMap::diff(a, b);
    /// assert_eq!(
    ///     Some(AttributesMap::from([
    ///         ("keyA", Value::from("ab")),
    ///         ("keyB", Value::from("b")),
    ///         ("keyBNull", Value::Null),
    ///         ("keyANull", Value::Null),
    ///     ])),
    ///     composed
    /// );
    /// ```
    pub fn diff(a: AttributesMap, b: AttributesMap) -> Option<Self> {
        let mut attributes = AttributesMap::new();
        let mut keys: HashSet<String> = a.0.clone().into_keys().collect();
        keys.extend(b.0.clone().into_keys());
        for k in keys {
            if a.get(&k) != b.get(&k) {
                attributes.insert(
                    k.clone(),
                    if let Some(value) = b.get(&k) {
                        value.clone()
                    } else {
                        Value::Null
                    },
                );
            }
        }
        if attributes.is_empty() {
            None
        } else {
            Some(attributes)
        }
    }

    /// Compute the invert map of a map compared to a base
    ///
    /// Any base key that exist in the map will have the base value.
    /// Any map key the doesn't exist in base, it will have a null value
    ///
    /// # Example
    ///
    /// ```
    /// use quill_delta_rs::attributes::AttributesMap;
    /// use serde_json::Value;
    ///
    /// let attributes = AttributesMap::from([("bold", Value::Bool(true))]);
    /// let base = AttributesMap::from([("italic", Value::Bool(true))]);
    /// assert_eq!(
    ///     AttributesMap::from([("bold", Value::Null)]),
    ///     AttributesMap::invert(attributes, base)
    /// );
    /// ```
    pub fn invert(attr: AttributesMap, base: AttributesMap) -> AttributesMap {
        let mut base_inverted = AttributesMap::new();
        for k in base.0.keys() {
            if base.get(k) != attr.get(k) && attr.0.contains_key(k) {
                base_inverted.insert(k.clone(), base[k].clone());
            }
        }
        for k in attr.0.keys() {
            if attr.get(k) != base.get(k) && !base.0.contains_key(k) {
                base_inverted.insert(k.clone(), Value::Null);
            }
        }
        base_inverted
    }

    /// Compute the transform map that is composed of all the key-valu of the right operand that
    /// are not in the left operand.
    ///
    /// #Example
    ///
    /// ```
    /// use quill_delta_rs::attributes::AttributesMap;
    /// use serde_json::Value;
    ///
    /// let left = AttributesMap::from([
    ///     ("bold", Value::Bool(true)),
    ///     ("color", Value::from("red")),
    ///     ("font", Value::Null),
    /// ]);
    /// let right = AttributesMap::from([
    ///     ("color", Value::from("blue")),
    ///     ("font", Value::from("serif")),
    ///     ("italic", Value::Bool(true)),
    /// ]);
    /// assert_eq!(
    ///     Some(AttributesMap::from([("italic", Value::Bool(true))])),
    ///     AttributesMap::transform(left, right, true)
    /// )
    /// ```
    pub fn transform(a: AttributesMap, b: AttributesMap, priority: bool) -> Option<AttributesMap> {
        if a.is_empty() {
            return if b.is_empty() { None } else { Some(b) };
        }
        if b.is_empty() {
            return None;
        }

        if !priority {
            return Some(b); // b simply overwrites us without priority
        }
        let mut attributes = AttributesMap::new();
        for k in b.0.keys() {
            if !a.0.contains_key(k) {
                attributes.insert(k.clone(), b[k].clone());
            }
        }
        if attributes.is_empty() {
            None
        } else {
            Some(attributes)
        }
    }

    /// Returns `true` if the attributes contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use quill_delta_rs::attributes::AttributesMap;
    /// use serde_json::Value;
    ///
    /// let mut a = AttributesMap::new();
    /// assert!(a.is_empty());
    /// a.insert("key".to_string(), Value::from("a"));
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Inserts an attribure in the attributes map.
    ///
    /// If the attributes map did not have this key present, [`None`] is returned.
    ///
    /// If the attributes map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical. See the [module-level
    /// documentation] for more.
    ///
    /// # Examples
    ///
    /// ```
    /// use quill_delta_rs::attributes::AttributesMap;
    /// use serde_json::Value;
    ///
    /// let mut map = AttributesMap::new();
    /// assert_eq!(map.insert("key".to_string(), Value::from("a")), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// let key = "key".to_string();
    /// map.insert(key.clone(), Value::from("b"));
    /// assert_eq!(map.insert(key.clone(), Value::from("c")), Some(Value::from("b")));
    /// assert_eq!(map[&key], Value::from("c"));
    /// ```
    pub fn insert(&mut self, key: String, value: Value) -> Option<Value> {
        self.0.insert(key, value)
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use quill_delta_rs::attributes::AttributesMap;
    /// use serde_json::Value;
    ///
    /// let key = String::from("key");
    /// let mut map = AttributesMap::new();
    /// map.insert(key.clone(), Value::from(1));
    /// assert_eq!(map.get(&key), Some(&Value::from(1)));
    /// assert_eq!(map.get(&("other key".to_string())), None);
    /// ```
    pub fn get(&self, key: &String) -> Option<&Value> {
        self.0.get(key)
    }

    /// Removes a key from the attribute map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use quill_delta_rs::attributes::AttributesMap;
    /// use serde_json::Value;
    ///
    /// let key = String::from("key");
    /// let mut map = AttributesMap::new();
    /// map.insert(key.clone(), Value::from(1));
    /// assert_eq!(map.remove(&key), Some(Value::from(1)));
    /// assert_eq!(map.remove(&key), None);
    /// ```
    pub fn remove(&mut self, key: &String) -> Option<Value> {
        self.0.remove(key)
    }
}

impl Index<&String> for AttributesMap {
    type Output = Value;

    fn index(&self, index: &String) -> &Self::Output {
        self.0.get(index).unwrap()
    }
}

impl From<HashMap<String, Value>> for AttributesMap {
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use serde_json::Value;
    /// use quill_delta_rs::attributes::AttributesMap;
    ///
    /// let hash_map = HashMap::from([("key1".to_string(), Value::from(2)), ("key2".to_string(), Value::from(4))]);
    /// let map1 = AttributesMap::from(hash_map.clone());
    /// let map2: AttributesMap = hash_map.into();
    /// assert_eq!(map1, map2);
    /// ```
    fn from(value: HashMap<String, Value>) -> Self {
        AttributesMap(value)
    }
}

impl<const N: usize> From<[(String, Value); N]> for AttributesMap {
    /// # Examples
    ///
    /// ```
    /// use quill_delta_rs::attributes::AttributesMap;
    /// use serde_json::Value;
    ///
    /// let map1 = AttributesMap::from([("key1".to_string(), Value::from(2)), ("key2".to_string(), Value::from(4))]);
    /// let map2: AttributesMap = [("key1".to_string(), Value::from(2)), ("key2".to_string(), Value::from(4))].into();
    /// assert_eq!(map1, map2);
    /// ```
    fn from(arr: [(String, Value); N]) -> Self {
        Self::from_iter(arr)
    }
}

impl FromIterator<(String, Value)> for AttributesMap {
    fn from_iter<T: IntoIterator<Item = (String, Value)>>(iter: T) -> AttributesMap {
        let mut map = HashMap::with_hasher(Default::default());
        map.extend(iter);
        AttributesMap(map)
    }
}

impl<'a, const N: usize> From<[(&'a str, Value); N]> for AttributesMap {
    /// # Examples
    ///
    /// ```
    /// use quill_delta_rs::attributes::AttributesMap;
    /// use serde_json::Value;
    ///
    /// let map1 = AttributesMap::from([("key1", Value::from(2)), ("key2", Value::from(4))]);
    /// let map2: AttributesMap = [("key1", Value::from(2)), ("key2", Value::from(4))].into();
    /// assert_eq!(map1, map2);
    /// ```
    fn from(arr: [(&'a str, Value); N]) -> Self {
        Self::from_iter(arr)
    }
}

impl<'a> FromIterator<(&'a str, Value)> for AttributesMap {
    fn from_iter<T: IntoIterator<Item = (&'a str, Value)>>(iter: T) -> AttributesMap {
        let mut map = HashMap::with_hasher(Default::default());
        for entry in iter {
            map.insert(entry.0.to_string(), entry.1);
        }
        AttributesMap(map)
    }
}

impl IntoIterator for AttributesMap {
    type Item = (String, Value);
    type IntoIter = IntoIter<String, Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl IntoIterator for &AttributesMap {
    type Item = (String, Value);
    type IntoIter = IntoIter<String, Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.clone().into_iter()
    }
}

impl Display for AttributesMap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("{")?;
        for pair in self {
            f.write_fmt(format_args!(
                "{}: {}}}",
                pair.0,
                pair.1.as_str().unwrap_or(format!("{}", pair.1).as_str())
            ))?;
        }
        f.write_str("}")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::attributes::AttributesMap;
    use serde_json::Value;

    #[test]
    fn from_iter_string() {
        let map1 = AttributesMap::from([
            ("key1".to_string(), Value::from(2)),
            ("key2".to_string(), Value::from(4)),
        ]);
        let map2: AttributesMap = [
            ("key1".to_string(), Value::from(2)),
            ("key2".to_string(), Value::from(4)),
        ]
        .into();
        assert_eq!(map1, map2);
    }

    #[test]
    fn from_hash_map() {
        let hash_map = HashMap::from([
            ("key1".to_string(), Value::from(2)),
            ("key2".to_string(), Value::from(4)),
        ]);
        let map1 = AttributesMap::from(hash_map.clone());
        let map2: AttributesMap = hash_map.into();
        assert_eq!(map1, map2);
    }

    #[test]
    fn into_iter() {
        let map = AttributesMap::from([("a", Value::from("a")), ("b", Value::from("b"))]);
        let mut hash_map: HashMap<String, Value> = HashMap::new();
        for attribute in map {
            hash_map.insert(attribute.0.clone(), attribute.1.clone());
        }
        assert_eq!(
            hash_map,
            HashMap::from([
                ("a".to_string(), Value::from("a")),
                ("b".to_string(), Value::from("b"))
            ])
        )
    }

    #[test]
    fn compose() {
        let a = AttributesMap::from([
            ("keyA", Value::from("a")),
            ("anotherKeyA", Value::from("a")),
            ("keyANull", Value::Null),
        ]);
        let b = AttributesMap::from([
            ("keyA", Value::from("ab")),
            ("keyB", Value::from("b")),
            ("keyBNull", Value::Null),
        ]);

        let composed = AttributesMap::compose(a, b, false);
        assert_eq!(
            composed,
            Some(AttributesMap::from([
                ("keyA", Value::from("ab")),
                ("anotherKeyA", Value::from("a")),
                ("keyB", Value::from("b")),
            ]))
        );
    }

    #[test]
    fn compose_keep_null() {
        let a = AttributesMap::from([("keyA", Value::from("a")), ("keyANull", Value::Null)]);
        let b = AttributesMap::from([
            ("keyA", Value::from("ab")),
            ("keyB", Value::from("b")),
            ("keyBNull", Value::Null),
        ]);
        let composed = AttributesMap::compose(a, b, true);
        assert_eq!(
            composed,
            Some(AttributesMap::from([
                ("keyA", Value::from("ab")),
                ("keyB", Value::from("b")),
                ("keyBNull", Value::Null)
            ]))
        );
    }

    #[test]
    fn compose_null_output() {
        let a = AttributesMap::from([("keyANull", Value::Null)]);
        let b = AttributesMap::from([("keyBNull", Value::Null)]);
        let compose = AttributesMap::compose(a, b, false);
        assert!(compose.is_none())
    }

    #[test]
    fn diff() {
        let a = AttributesMap::from([
            ("1", Value::from("a")),
            ("2", Value::from("ab")),
            ("a-null", Value::Null),
        ]);
        let b = AttributesMap::from([
            ("1", Value::from("ab")),
            ("3", Value::from("b")),
            ("b-null", Value::Null),
        ]);
        let composed = AttributesMap::diff(a, b);
        assert_eq!(
            composed,
            Some(AttributesMap::from([
                ("1", Value::from("ab")),
                ("2", Value::Null),
                ("3", Value::from("b")),
                ("a-null", Value::Null),
                ("b-null", Value::Null),
            ]))
        );
    }

    #[test]
    fn diff_null() {
        let a = AttributesMap::from([
            ("1", Value::from("a")),
            ("2", Value::from("ab")),
            ("a-null", Value::Null),
        ]);
        let b = a.clone();
        let composed = AttributesMap::diff(a, b);
        assert_eq!(composed, None);
    }

    #[test]
    fn invert_replace() {
        let attributes = AttributesMap::from([("color", Value::from("red"))]);
        let base = AttributesMap::from([("color", Value::from("blue"))]);
        assert_eq!(base, AttributesMap::invert(attributes, base.clone()));
    }

    #[test]
    fn invert_revert_unset() {
        let attributes = AttributesMap::from([("bold", Value::Null)]);
        let base = AttributesMap::from([("bold", Value::Bool(true))]);
        assert_eq!(
            AttributesMap::from([("bold", Value::Bool(true))]),
            AttributesMap::invert(attributes, base)
        );
    }

    #[test]
    fn invert_merge() {
        let attributes = AttributesMap::from([("bold", Value::Bool(true))]);
        let base = AttributesMap::from([("italic", Value::Bool(true))]);
        assert_eq!(
            AttributesMap::from([("bold", Value::Null)]),
            AttributesMap::invert(attributes, base)
        );
    }

    #[test]
    fn invert_on_null() {
        let base = AttributesMap::from([("bold", Value::Bool(true))]);
        assert_eq!(
            AttributesMap::new(),
            AttributesMap::invert(AttributesMap::new(), base)
        );
    }

    #[test]
    fn invert_base_null() {
        let attributes = AttributesMap::from([("bold", Value::Bool(true))]);
        let expected = AttributesMap::from([("bold", Value::Null)]);
        assert_eq!(
            expected,
            AttributesMap::invert(attributes, AttributesMap::new())
        );
    }

    #[test]
    fn inver_both_null() {
        assert_eq!(
            AttributesMap::new(),
            AttributesMap::invert(AttributesMap::new(), AttributesMap::new())
        );
    }

    #[test]
    fn transform_left_empty() {
        let right = AttributesMap::from([
            ("color", Value::from("blue")),
            ("font", Value::from("serif")),
            ("italic", Value::Bool(true)),
        ]);
        assert_eq!(
            Some(right.clone()),
            AttributesMap::transform(AttributesMap::new(), right.clone(), false)
        )
    }

    #[test]
    fn transform_right_empty() {
        let left = AttributesMap::from([
            ("bold", Value::Bool(true)),
            ("color", Value::from("red")),
            ("font", Value::Null),
        ]);
        assert_eq!(
            None,
            AttributesMap::transform(left, AttributesMap::new(), false)
        );
    }

    #[test]
    fn transform_both_empty() {
        assert!(
            AttributesMap::transform(AttributesMap::new(), AttributesMap::new(), false).is_none()
        )
    }

    #[test]
    fn transform_with_priority() {
        let left = AttributesMap::from([
            ("bold", Value::Bool(true)),
            ("color", Value::from("red")),
            ("font", Value::Null),
        ]);
        let right = AttributesMap::from([
            ("color", Value::from("blue")),
            ("font", Value::from("serif")),
            ("italic", Value::Bool(true)),
        ]);
        assert_eq!(
            Some(AttributesMap::from([("italic", Value::Bool(true))])),
            AttributesMap::transform(left, right, true)
        )
    }

    #[test]
    fn transform_without_priority() {
        let left = AttributesMap::from([
            ("bold", Value::Bool(true)),
            ("color", Value::from("red")),
            ("font", Value::Null),
        ]);
        let right = AttributesMap::from([
            ("color", Value::from("blue")),
            ("font", Value::from("serif")),
            ("italic", Value::Bool(true)),
        ]);
        assert_eq!(
            Some(right.clone()),
            AttributesMap::transform(left, right, false)
        )
    }
}
