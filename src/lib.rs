pub mod attributes;
pub mod delta;
pub mod iter;
pub mod op;

pub(crate) mod utils {
    #[macro_export]
    macro_rules! collections {
        // map-like
        ($($k:expr => $v:expr),* $(,)?) => {{
            From::from([$(($k, $v),)*])
        }};
        // set-like
        ($($v:expr),* $(,)?) => {{
            From::from([$($v,)*])
        }};
    }
}
