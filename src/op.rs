use std::fmt::{self, Display};

use serde_derive::{Deserialize, Serialize};
use serde_json::Value;

use crate::attributes::AttributesMap;

/// An error related to Deltas
#[derive(Debug)]
pub struct Error {
    message: String,
}

impl Error {
    fn new<T>(msg: T) -> Self
    where
        T: fmt::Display,
    {
        Error {
            message: msg.to_string(),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for Error {}

/// Kind operation that Deltas support
#[derive(Debug, Serialize, Deserialize, Clone, PartialEq)]
#[serde(rename_all = "lowercase")]
pub enum OpType {
    // Bind module to JSON serialization
    INSERT(Value),
    RETAIN(usize),
    DELETE(usize),
}

/// An operation in a Delta.
///
/// Operations materialize a change to be applied to a state and results in a new state
#[derive(Debug, Serialize, Deserialize, Clone, PartialEq)]
pub struct Op {
    #[serde(flatten)]
    kind: OpType,
    #[serde(default, skip_serializing_if = "AttributesMap::is_empty")]
    attributes: AttributesMap,
}

impl Op {
    fn attributes_or_empty(attributes: Option<AttributesMap>) -> AttributesMap {
        match attributes {
            Some(attributes) => attributes,
            _ => AttributesMap::new(),
        }
    }

    pub fn insert<V: Into<Value>>(object: V, attributes: Option<AttributesMap>) -> Self {
        let object = object.into();
        if !matches!(object, Value::String(_))
            && attributes.is_some()
            && !attributes.as_ref().unwrap().is_empty()
        {
            panic!(
                "Insert error: \
            Cannot combine attributes with an inserted value other than a string.",
            );
        }
        Op {
            kind: OpType::INSERT(object),
            attributes: Self::attributes_or_empty(attributes),
        }
    }

    pub fn try_insert(object: Value, attributes: Option<AttributesMap>) -> Result<Self, Error> {
        if !matches!(object, Value::String(_))
            && attributes.is_some()
            && !attributes.as_ref().unwrap().is_empty()
        {
            return Err(Error::new(
                "Insert error: \
            Cannot combine attributes with an inserted value other than a string.",
            ));
        }
        Ok(Op {
            kind: OpType::INSERT(object),
            attributes: Self::attributes_or_empty(attributes),
        })
    }

    pub fn retain(length: usize, attributes: Option<AttributesMap>) -> Self {
        assert_ne!(length, 0, "retain length must be greater than zero");
        Op {
            kind: OpType::RETAIN(length),
            attributes: Self::attributes_or_empty(attributes),
        }
    }

    pub fn delete(length: usize) -> Self {
        assert_ne!(length, 0, "delete length must be greater than zero");
        Op {
            kind: OpType::DELETE(length),
            attributes: AttributesMap::new(),
        }
    }

    pub fn retain_until_end() -> Self {
        Self::retain(usize::MAX, None)
    }

    pub fn is_insert(&self) -> bool {
        matches!(self.kind, OpType::INSERT(_))
    }

    pub fn is_text_insert(&self) -> bool {
        matches!(&self.kind, OpType::INSERT(value) if matches!(value, Value::String(_)))
    }

    pub fn is_retain(&self) -> bool {
        matches!(self.kind, OpType::RETAIN(_))
    }

    pub fn is_delete(&self) -> bool {
        matches!(self.kind, OpType::DELETE(_))
    }

    pub fn kind(&self) -> OpType {
        self.kind.clone()
    }

    pub fn len(&self) -> usize {
        match &self.kind {
            OpType::INSERT(value) => match value {
                Value::String(s) => s.len(),
                _ => 1,
            },
            OpType::RETAIN(len) => *len,
            OpType::DELETE(len) => *len,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn attributes(&self) -> Option<AttributesMap> {
        match self.kind {
            OpType::DELETE(_) => None,
            _ => {
                if self.attributes.is_empty() {
                    None
                } else {
                    Some(self.attributes.clone())
                }
            }
        }
    }

    pub fn value(&self) -> Value {
        match &self.kind {
            OpType::INSERT(value) => value.clone(),
            _ => panic!(
                "Retrieving the value of an operation is possible \
                only on INSERT operations; Try to get value of {:?}",
                &self
            ),
        }
    }

    pub fn value_as_string(&self) -> String {
        match &self.kind {
            OpType::INSERT(value) => {
                if let Some(str) = value.clone().as_str() {
                    String::from(str)
                } else {
                    panic!(
                        "Retrieving the text value of an operation is possible \
                        only on string INSERT operations; Try to get string value of {:?}",
                        &self
                    )
                }
            }
            _ => panic!(
                "Retrieving the text value of an operation is possible \
                only on string INSERT operations; Try to get string value of {:?}",
                &self
            ),
        }
    }
}

impl Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            OpType::INSERT(v) => {
                f.write_fmt(format_args!(
                    "ins({})",
                    v.as_str()
                        .unwrap_or(format!("{v}").as_str())
                        .replace('\n', "⏎")
                ))?;
            }
            OpType::RETAIN(l) => {
                f.write_fmt(format_args!("ret({l})"))?;
            }
            OpType::DELETE(l) => {
                f.write_fmt(format_args!("del({l})"))?;
            }
        }
        if self.attributes().is_some() {
            f.write_fmt(format_args!(" + {}", self.attributes().unwrap()))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use serde_json::{json, Value};

    use crate::attributes::{attributes, AttributesMap};

    use crate::op::{Op, OpType};

    #[test]
    fn deserialize_insert_no_attributes() {
        let json = json!({
            "insert": "something"
        });
        assert_eq!(
            serde_json::from_value::<Op>(json).unwrap(),
            Op::insert(Value::from("something"), None)
        );
    }

    #[test]
    fn deserialize_insert_with_attribute() {
        let json = json!({
            "insert": "something",
            "attributes": {
                "key": 1
            }
        });
        assert_eq!(
            serde_json::from_value::<Op>(json).unwrap(),
            Op::insert(Value::from("something"), Some(attributes!("key" => 1)))
        );
    }

    #[test]
    fn serialize_insert_no_attributes() {
        let op = Op::insert(Value::from("something"), None);
        let exp = json!({
            "insert": "something"
        });
        assert_eq!(serde_json::to_value(op).unwrap(), exp)
    }

    #[test]
    fn insert_string_no_attribute() {
        let result = Op::try_insert(Value::from("something"), None);
        assert!(
            result.is_ok(),
            "Op::insert return an err {}",
            result.unwrap_err()
        );
        let act = result.unwrap();
        assert_eq!(act.len(), "something".len());
        assert!(act.is_text_insert());
        assert!(act.is_insert());
        assert!(!act.is_delete());
        assert!(!act.is_retain());
        assert!(matches!(act.kind(), OpType::INSERT(_)));
        assert!(act.attributes().is_none())
    }

    #[test]
    fn insert_string_with_attributes() {
        let result = Op::try_insert(Value::from("something"), Some(attributes!("b" => true)));
        assert!(
            result.is_ok(),
            "Op::insert return an err {}",
            result.unwrap_err()
        );
        let act = result.unwrap();
        assert!(act.is_text_insert());
        assert!(act.is_insert());
        assert!(!act.is_delete());
        assert!(!act.is_retain());
        assert!(matches!(act.kind(), OpType::INSERT(_)));
        assert!(
            act.attributes().is_some(),
            "No attributes; attributes are expected"
        );
        assert_eq!(act.attributes().unwrap(), attributes!("b" => true))
    }

    #[test]
    fn insert_object_no_attribute() {
        let mut content: serde_json::Map<String, Value> = serde_json::Map::new();
        content.insert(
            String::from("link"),
            Value::from("http://www.wikipedia.com"),
        );
        let value = Value::Object(content);
        let result = Op::try_insert(value.clone(), None);
        assert!(
            result.is_ok(),
            "Op::insert returned an err {}",
            result.unwrap_err()
        );
        let act = result.unwrap();
        assert!(!act.is_text_insert());
        assert!(act.is_insert());
        assert!(!act.is_delete());
        assert!(!act.is_retain());
        assert!(matches!(act.kind(), OpType::INSERT(_)));
        assert_eq!(act.len(), 1);
        assert_eq!(act.value(), value);
        assert!(act.attributes().is_none(), "No attributes are expected");
    }

    #[test]
    fn insert_object_with_attributes() {
        let mut content: serde_json::Map<String, Value> = serde_json::Map::new();
        content.insert(
            String::from("link"),
            Value::from("http://www.wikipedia.com"),
        );
        let value = Value::Object(content);
        let result = Op::try_insert(value, Some(attributes!("b" => true)));
        assert!(result.is_err(), "Op::insert returned ok");
    }

    #[test]
    #[should_panic]
    fn insert_or_panic_panics() {
        let mut content: serde_json::Map<String, Value> = serde_json::Map::new();
        content.insert(
            String::from("link"),
            Value::from("http://www.wikipedia.com"),
        );
        let value = Value::Object(content);
        Op::insert(value, Some(attributes!("b" => true)));
    }

    #[test]
    fn insert_or_panic_no_panic() {
        let mut content: serde_json::Map<String, Value> = serde_json::Map::new();
        content.insert(
            String::from("link"),
            Value::from("http://www.wikipedia.com"),
        );
        let value = Value::Object(content);
        let act = Op::insert(value.clone(), None);
        assert!(act.attributes().is_none());
        assert_eq!(act.value(), value)
    }

    #[test]
    #[should_panic]
    fn value_as_string_on_insert_object_panic() {
        let mut content: serde_json::Map<String, Value> = serde_json::Map::new();
        content.insert(
            String::from("link"),
            Value::from("http://www.wikipedia.com"),
        );
        let value = Value::Object(content);
        let op = Op::insert(value, None);
        op.value_as_string();
    }

    #[test]
    #[should_panic]
    fn value_as_string_on_none_insert() {
        let op = Op::retain(10, None);
        op.value_as_string();
    }

    #[test]
    fn value_as_string() {
        let op = Op::insert(Value::from("something"), None);
        assert_eq!(op.value_as_string(), Value::from("something"))
    }

    #[test]
    #[should_panic]
    fn value_on_none_insert() {
        let op = Op::retain(10, None);
        op.value();
    }

    #[test]
    fn value() {
        let op = Op::insert(Value::from("something"), None);
        assert_eq!(op.value(), Value::from("something"))
    }

    #[test]
    fn delete() {
        let act = Op::delete(3);
        assert!(!act.is_text_insert());
        assert!(!act.is_insert());
        assert!(act.is_delete());
        assert!(!act.is_retain());
        assert!(matches!(act.kind(), OpType::DELETE(_)));
        assert_eq!(act.len(), 3);
        assert!(act.attributes().is_none());
    }

    #[test]
    fn retain_no_attribute() {
        let act = Op::retain(3, None);
        assert!(!act.is_text_insert());
        assert!(!act.is_insert());
        assert!(!act.is_delete());
        assert!(act.is_retain());
        assert!(matches!(act.kind(), OpType::RETAIN(_)));
        assert_eq!(act.len(), 3);
        assert!(act.attributes().is_none())
    }

    #[test]
    fn retain_with_attribute() {
        let act = Op::retain(3, Some(attributes!("b" => true)));
        assert!(!act.is_text_insert());
        assert!(!act.is_insert());
        assert!(!act.is_delete());
        assert!(act.is_retain());
        assert!(matches!(act.kind(), OpType::RETAIN(_)));
        assert_eq!(act.len(), 3);
        assert!(
            act.attributes().is_some(),
            "No attributes; attributes are expected"
        );
        assert_eq!(act.attributes().unwrap(), attributes!("b" => true))
    }

    #[test]
    fn retain_until_end() {
        let op = Op::retain_until_end();
        assert_eq!(op.len(), usize::MAX)
    }
}
