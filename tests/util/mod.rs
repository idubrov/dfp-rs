use std::str::FromStr;

pub fn parse_wrapper<T: FromStr>(s: &str) -> Result<T, T::Err> {
    s.parse()
}
