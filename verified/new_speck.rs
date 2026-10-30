//
// What we are proving here: 
// When you create a new authorization "scoreboard" (the stream) with a valid rule mode 
// and at least 1 rule to check, it starts perfectly clean. `done` is false, `idx` is 0, 
// and the starting result perfectly matches the mathematical definition of that mode.

use vstd::prelude::*;

verus! {

// -----------------------------------------------------------------------------
// 1. TRANSLATING MESSY STRINGS INTO PURE MATH
// Verus (specifically its mathematical Z3 solver) hates dealing with raw computer 
// memory, which is what standard Rust `&str` strings use. 
// To fix this, we use the `@` symbol (the "view" operator). This strips away 
// the memory pointers and turns the text into a pure, abstract sequence of 
// characters (`Seq<char>`) that the math solver can easily read.
// -----------------------------------------------------------------------------

pub open spec fn expr_allow() -> Seq<char> { "some(where (p_eft == allow))"@ }
pub open spec fn expr_allow_not_deny() -> Seq<char> {
    "some(where (p_eft == allow)) && !some(where (p_eft == deny))"@
}
pub open spec fn expr_priority() -> Seq<char> { "priority(p_eft) || deny"@ }
pub open spec fn expr_not_deny() -> Seq<char> { "!some(where (p_eft == deny))"@ }

/// This defines the strict boundary of our system. It returns true ONLY if the 
/// provided text perfectly matches one of the 4 modes Casbin-RS understands.
pub open spec fn supported(s: Seq<char>) -> bool {
    s == expr_allow() || s == expr_allow_not_deny() || s == expr_priority() || s == expr_not_deny()
}

/// This acts as our mathematical answer key. It tells Verus exactly what the 
/// starting default answer should be for each specific mode. 
/// Only Deny-Override (expr_not_deny) starts as `true`.
pub open spec fn initial_res(s: Seq<char>) -> bool {
    if s == expr_allow() { false }
    else if s == expr_allow_not_deny() { false }
    else if s == expr_priority() { false }
    else { true }
}

// -----------------------------------------------------------------------------
// 2. THE TRUSTED BOUNDARY
// Because the math solver can't evaluate Rust's `a == b` for string pointers, 
// we have to build a bridge. `#[verifier::external_body]` tells Verus: 
// "Don't try to prove the inside of this function. Just trust me that if it 
// returns true, the mathematical character sequences of 'a' and 'b' are identical."
// -----------------------------------------------------------------------------
#[verifier::external_body]
fn eq_str(a: &str, b: &str) -> (r: bool)
    ensures r == (a@ == b@) // "Trust me, the abstract character sequences match."
{
    a == b
}

// -----------------------------------------------------------------------------
// 3. THE SCOREBOARD (Data Structure)
// -----------------------------------------------------------------------------
pub struct DefaultEffectStream {
    pub done: bool,
    pub res: bool,
    // We wrap the expression string in a `Ghost`. This tells Verus to use it 
    // ONLY for the mathematical proof. When the code is actually compiled into 
    // a real binary, this variable completely disappears and takes up 0 bytes of memory!
    pub expr: Ghost<Seq<char>>, 
    pub idx: usize,
    pub cap: usize,
}

// -----------------------------------------------------------------------------
// 4. THE MAIN FUNCTION AND MATHEMATICAL CONTRACT
// -----------------------------------------------------------------------------
pub fn new_stream(expr: &str, cap: usize) -> (s: DefaultEffectStream)
    // REQUIRES (Preconditions): The strict rules the caller must follow.
    requires
        cap > 0,          // You cannot evaluate a policy with 0 rules.
        supported(expr@), // The text string MUST be one of our 4 supported modes.
    
    // ENSURES (Postconditions): The promises Verus guarantees if you follow the rules.
    ensures
        !s.done,                     // We just started, so we are definitely not done.
        s.idx == 0,                  // We haven't looked at any rules yet.
        s.cap == cap,                // The capacity is recorded correctly.
        s.expr@ == expr@,            // The saved expression matches the input.
        s.res == initial_res(expr@), // The starting result matches our math answer key perfectly.
{
    // We use our trusted `eq_str` bridge here to figure out which mode we are in.
    let res = if eq_str(expr, "some(where (p_eft == allow))") {
        false
    } else if eq_str(expr, "some(where (p_eft == allow)) && !some(where (p_eft == deny))") {
        false
    } else if eq_str(expr, "priority(p_eft) || deny") {
        false
    } else if eq_str(expr, "!some(where (p_eft == deny))") {
        true
    } else {
        // THE UNREACHABLE PANIC:
        // In the original code, an unsupported string crashes the program. 
        // Because our `requires` clause strictly mandates that the input MUST be supported, 
        // Verus mathematically knows it is physically impossible to ever reach this `else` block.
        proof { assert(false); } 
        vstd::pervasive::unreached() // We tell Verus: "I proved we never hit this line."
    };
    
    // Package it all up into a fresh scoreboard and return it.
    DefaultEffectStream { done: false, res, expr: Ghost(expr@), idx: 0, cap }
}

} // verus!

fn main() {}