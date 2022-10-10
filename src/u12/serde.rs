use super::U12;
extern crate serde;

impl serde::Serialize for U12 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_u16(self.0)
    }
}

struct U12Visitor;

impl<'de> serde::de::Visitor<'de> for U12Visitor {
    type Value = U12;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("an integer between 0 and 2^12-1")
    }

    fn visit_u8<E>(self, value: u8) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(U12(value as u16))
    }

    fn visit_u16<E>(self, value: u16) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        if value > U12::max_value().0 {
            Err(E::custom(format!("U12 out of range: {}", value)))
        } else {
            Ok(U12(value))
        }
    }

    fn visit_u32<E>(self, value: u32) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        if value > U12::max_value().0 as u32 {
            Err(E::custom(format!("U12 out of range: {}", value)))
        } else {
            Ok(U12(value as u16))
        }
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        if value > U12::max_value().0 as u64 {
            Err(E::custom(format!("U12 out of range: {}", value)))
        } else {
            Ok(U12(value as u16))
        }
    }

    fn visit_i8<E>(self, value: i8) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        if value < 0 || value > U12::max_value().0 as i8 {
            Err(E::custom(format!("U12 out of range: {}", value)))
        } else {
            Ok(U12(value as u16))
        }
    }

    fn visit_i16<E>(self, value: i16) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        if value < 0 || value > U12::max_value().0 as i16 {
            Err(E::custom(format!("U12 out of range: {}", value)))
        } else {
            Ok(U12(value as u16))
        }
    }

    fn visit_i32<E>(self, value: i32) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        if value < 0 || value > U12::max_value().0 as i32 {
            Err(E::custom(format!("U12 out of range: {}", value)))
        } else {
            Ok(U12(value as u16))
        }
    }

    fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        if value < 0 || value > U12::max_value().0 as i64 {
            Err(E::custom(format!("U12 out of range: {}", value)))
        } else {
            Ok(U12(value as u16))
        }
    }
}

impl<'de> serde::Deserialize<'de> for U12 {
    fn deserialize<D>(deserializer: D) -> Result<U12, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_u16(U12Visitor)
    }
}
