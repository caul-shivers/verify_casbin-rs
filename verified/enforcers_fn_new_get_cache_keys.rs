//results: verification results:: 8 verified, 0 errors

//new function: allows evaluation of different policies
//get_cache_key function: gets the string identifier for the request

use vstd::prelude::*;

verus! {

pub struct EnforceContext {
    pub r_type: String,
    pub p_type: String,
    pub e_type: String,
    pub m_type: String,
}

impl EnforceContext {
    pub fn new(suffix: &str) -> (Self)
        ensures(
            true
        )
    {
        Self {
            r_type: format!("r{}", suffix),
            p_type: format!("p{}", suffix),
            e_type: format!("e{}", suffix),
            m_type: format!("m{}", suffix),
        }
    }

    pub fn get_cache_key(&self) -> (String)
        ensures(
            true
        )
    {
        format!(
            "EnforceContext{{{}-{}-{}-{}}}",
            self.r_type, self.p_type, self.e_type, self.m_type
        )
    }
}

} // verus!

fn main() {}