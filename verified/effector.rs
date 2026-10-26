// Verus model of casbin-rs `src/effector.rs`
// (DefaultEffector::new_stream / DefaultEffectStream::push_effect / next)
// together with the way `Enforcer::private_enforce` drives it.
//
// Run:   verus <this file>
//
// ─────────────────────────── Modelling choices ───────────────────────────
//   * The effect expression `expr: String` is modelled by the `Mode` enum
//     (one variant per expression accepted by `new_stream`). The string ->
//     Mode step is NOT verified (trusted boundary, see TRUSTED below).
//   * A ghost sequence `effs` records every effect pushed so far, so the
//     stream's result can be stated over the whole history.
//   * The `explain` feature (`expl`) is not modelled. It only reports
//     diagnostics and never influences the allow/deny result.
//
// ─────────────────────────── What is proved ───────────────────────────
//   1. push_effect preserves `inv()`:
//        res  == decision(mode, effs)   (result == policy-effect semantics)
//        done == a decisive effect was seen OR the last rule was pushed
//      => `next()`'s `assert!(self.done)` cannot fail under the caller contract.
//   2. Early exit is sound: if the stream stops at a decisive effect, the
//      remaining rules could not have changed the result
//      (lemma_early_exit).
//   3. run_effects (the loop in private_enforce, abstracted to a vector of
//      per-rule effects) returns exactly `decision(mode, all effects)`, and
//        - a grant (mode != DenyOverride) implies some rule had effect Allow,
//        - any Deny blocks the grant in AllowAndNoDeny / DenyOverride.
//   4. run_single: the "empty policy" path of private_enforce.
//
// ─────────────────────────── TRUSTED / not covered ───────────────────────────
//   * `expr` string -> `Mode` mapping in new_stream (and its `panic!` on
//     unsupported expressions).
//   * How private_enforce computes each rule's EffectKind from the Rhai
//     matcher and `p_eft` (modelled only as "a vector of EffectKind").
//   * The model is a hand-written copy of the Rust logic, not the original
//     source file.
//
// Caller contract of push_effect: inv() && !done. private_enforce satisfies
// it: it stops as soon as push_effect returns true, and cap = max(len, 1).

use vstd::prelude::*;

verus! {

broadcast use vstd::seq::group_seq_axioms;

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum EffectKind {
    Allow,
    Indeterminate,
    Deny,
}

/// One variant per effect expression accepted by DefaultEffector::new_stream.
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Mode {
    AllowOverride,  // "some(where (p_eft == allow))"
    AllowAndNoDeny, // "some(where (p_eft == allow)) && !some(where (p_eft == deny))"
    DenyOverride,   // "!some(where (p_eft == deny))"
    Priority,       // "priority(p_eft) || deny"
}

// ───────────────────────── specification ─────────────────────────

pub open spec fn has_effect(s: Seq<EffectKind>, k: EffectKind) -> bool {
    exists|i: int| #![trigger s[i]] 0 <= i < s.len() && s[i] == k
}

/// Priority semantics: the FIRST non-Indeterminate effect is Allow.
pub open spec fn allow_first(s: Seq<EffectKind>) -> bool {
    exists|i: int| #![trigger s[i]]
        0 <= i < s.len() && s[i] == EffectKind::Allow
            && (forall|j: int| #![trigger s[j]] 0 <= j < i ==> s[j] == EffectKind::Indeterminate)
}

/// The meaning of each effect expression over the full list of rule effects.
pub open spec fn decision(m: Mode, s: Seq<EffectKind>) -> bool {
    match m {
        Mode::AllowOverride => has_effect(s, EffectKind::Allow),
        Mode::AllowAndNoDeny => has_effect(s, EffectKind::Allow) && !has_effect(s, EffectKind::Deny),
        Mode::DenyOverride => !has_effect(s, EffectKind::Deny),
        Mode::Priority => allow_first(s),
    }
}

/// An effect after which the result can no longer change (stream may stop).
pub open spec fn decisive_for(m: Mode, e: EffectKind) -> bool {
    match m {
        Mode::AllowOverride => e == EffectKind::Allow,
        Mode::AllowAndNoDeny => e == EffectKind::Deny,
        Mode::DenyOverride => e == EffectKind::Deny,
        Mode::Priority => e != EffectKind::Indeterminate,
    }
}

pub open spec fn stop_seen(m: Mode, s: Seq<EffectKind>) -> bool {
    match m {
        Mode::AllowOverride => has_effect(s, EffectKind::Allow),
        Mode::AllowAndNoDeny => has_effect(s, EffectKind::Deny),
        Mode::DenyOverride => has_effect(s, EffectKind::Deny),
        Mode::Priority => has_effect(s, EffectKind::Allow) || has_effect(s, EffectKind::Deny),
    }
}

/// `p` is a prefix of `s`.
pub open spec fn is_prefix(p: Seq<EffectKind>, s: Seq<EffectKind>) -> bool {
    &&& p.len() <= s.len()
    &&& forall|i: int| #![trigger p[i]] 0 <= i < p.len() ==> p[i] == s[i]
}

// ───────────────────────── helper lemmas ─────────────────────────

proof fn lemma_has_effect_push(s: Seq<EffectKind>, k: EffectKind, e: EffectKind)
    ensures
        has_effect(s.push(e), k) == (has_effect(s, k) || e == k),
{
    let t = s.push(e);
    assert(t.len() == s.len() + 1);
    if has_effect(s, k) {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == k;
        assert(t[i] == s[i]);
    }
    if e == k {
        assert(t[s.len() as int] == e);
    }
    if has_effect(t, k) {
        let i = choose|i: int| 0 <= i < t.len() && t[i] == k;
        if i < s.len() {
            assert(t[i] == s[i]);
        } else {
            assert(i == s.len());
            assert(t[i] == e);
        }
    }
}

/// If nothing decisive has happened yet, Priority's result is "false", and
/// pushing `e` makes it exactly `e == Allow`.
proof fn lemma_allow_first_push(s: Seq<EffectKind>, e: EffectKind)
    requires
        !has_effect(s, EffectKind::Allow),
        !has_effect(s, EffectKind::Deny),
    ensures
        !allow_first(s),
        allow_first(s.push(e)) == (e == EffectKind::Allow),
{
    let t = s.push(e);
    assert(t.len() == s.len() + 1);

    // every element of s is Indeterminate
    assert forall|j: int| 0 <= j < s.len() implies s[j] == EffectKind::Indeterminate by {}

    if allow_first(s) {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == EffectKind::Allow
            && (forall|j: int| 0 <= j < i ==> s[j] == EffectKind::Indeterminate);
        assert(has_effect(s, EffectKind::Allow));
    }

    if e == EffectKind::Allow {
        let i = s.len() as int;
        assert(t[i] == EffectKind::Allow);
        assert forall|j: int| 0 <= j < i implies t[j] == EffectKind::Indeterminate by {
            assert(t[j] == s[j]);
        }
        assert(allow_first(t));
    }

    if allow_first(t) {
        let i = choose|i: int| 0 <= i < t.len() && t[i] == EffectKind::Allow
            && (forall|j: int| 0 <= j < i ==> t[j] == EffectKind::Indeterminate);
        if i < s.len() {
            assert(t[i] == s[i]);
            assert(s[i] == EffectKind::Indeterminate);
        } else {
            assert(i == s.len());
            assert(t[i] == e);
        }
    }
}

/// An effect present in a prefix is present in the whole sequence.
proof fn lemma_has_effect_prefix(p: Seq<EffectKind>, s: Seq<EffectKind>, k: EffectKind)
    requires
        is_prefix(p, s),
        has_effect(p, k),
    ensures
        has_effect(s, k),
{
    let i = choose|i: int| 0 <= i < p.len() && p[i] == k;
    assert(s[i] == p[i]);
}

/// Priority: once the prefix already contains a decisive effect, extending it
/// cannot change whether "the first decisive effect is Allow".
proof fn lemma_allow_first_prefix(p: Seq<EffectKind>, s: Seq<EffectKind>)
    requires
        is_prefix(p, s),
        has_effect(p, EffectKind::Allow) || has_effect(p, EffectKind::Deny),
    ensures
        allow_first(s) == allow_first(p),
{
    if allow_first(p) {
        let i = choose|i: int| 0 <= i < p.len() && p[i] == EffectKind::Allow
            && (forall|j: int| 0 <= j < i ==> p[j] == EffectKind::Indeterminate);
        assert(s[i] == p[i]);
        assert forall|j: int| 0 <= j < i implies s[j] == EffectKind::Indeterminate by {
            assert(s[j] == p[j]);
        }
        assert(allow_first(s));
    }
    if allow_first(s) {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == EffectKind::Allow
            && (forall|j: int| 0 <= j < i ==> s[j] == EffectKind::Indeterminate);
        if i < p.len() {
            assert(p[i] == s[i]);
            assert forall|j: int| 0 <= j < i implies p[j] == EffectKind::Indeterminate by {
                assert(s[j] == p[j]);
            }
            assert(allow_first(p));
        } else {
            // every element of p precedes i, hence is Indeterminate ...
            assert forall|j: int| 0 <= j < p.len() implies p[j] == EffectKind::Indeterminate by {
                assert(s[j] == p[j]);
            }
            // ... contradicting that p contains an Allow or a Deny
            if has_effect(p, EffectKind::Allow) {
                let d = choose|d: int| 0 <= d < p.len() && p[d] == EffectKind::Allow;
                assert(p[d] == EffectKind::Indeterminate);
            } else {
                let d = choose|d: int| 0 <= d < p.len() && p[d] == EffectKind::Deny;
                assert(p[d] == EffectKind::Indeterminate);
            }
        }
    }
}

/// EARLY EXIT IS SOUND: if the effects consumed so far (`p`) already contain
/// a decisive effect, then the decision over any extension `s` of `p` equals
/// the decision over `p`. The rules that the loop skips cannot matter.
proof fn lemma_early_exit(m: Mode, p: Seq<EffectKind>, s: Seq<EffectKind>)
    requires
        stop_seen(m, p),
        is_prefix(p, s),
    ensures
        decision(m, s) == decision(m, p),
{
    match m {
        Mode::AllowOverride => {
            lemma_has_effect_prefix(p, s, EffectKind::Allow);
        },
        Mode::AllowAndNoDeny => {
            lemma_has_effect_prefix(p, s, EffectKind::Deny);
        },
        Mode::DenyOverride => {
            lemma_has_effect_prefix(p, s, EffectKind::Deny);
        },
        Mode::Priority => {
            lemma_allow_first_prefix(p, s);
        },
    }
}

// ───────────────────────── safety lemmas ─────────────────────────

/// "Granted ⇒ some matched rule had effect Allow."
/// (False for DenyOverride by design: with no matching rule it grants.)
proof fn lemma_grant_has_allow_witness(m: Mode, s: Seq<EffectKind>)
    requires
        decision(m, s),
        m != Mode::DenyOverride,
    ensures
        has_effect(s, EffectKind::Allow),
{
    if m == Mode::Priority {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == EffectKind::Allow
            && (forall|j: int| 0 <= j < i ==> s[j] == EffectKind::Indeterminate);
        assert(has_effect(s, EffectKind::Allow));
    }
}

/// "Any matched Deny blocks the grant" for the two deny-sensitive modes.
proof fn lemma_deny_blocks(m: Mode, s: Seq<EffectKind>)
    requires
        has_effect(s, EffectKind::Deny),
        m == Mode::AllowAndNoDeny || m == Mode::DenyOverride,
    ensures
        !decision(m, s),
{
}

// ───────────────────────── the stream ─────────────────────────

pub struct Stream {
    pub done: bool,
    pub res: bool,
    pub mode: Mode,
    pub idx: usize,
    pub cap: usize,
    pub effs: Ghost<Seq<EffectKind>>, // every effect pushed so far
}

impl Stream {
    pub open spec fn inv(&self) -> bool {
        &&& self.cap > 0
        &&& self.idx == self.effs@.len()
        &&& self.idx <= self.cap
        // the result always equals the policy-effect semantics of the history
        &&& self.res == decision(self.mode, self.effs@)
        // the stream is done exactly when it saw a decisive effect or the last rule
        &&& self.done == (stop_seen(self.mode, self.effs@) || self.idx == self.cap)
    }

    /// DefaultEffector::new_stream (with the string already parsed to a Mode).
    pub fn new(mode: Mode, cap: usize) -> (s: Stream)
        requires
            cap > 0,
        ensures
            s.inv(),
            s.mode == mode,
            s.cap == cap,
            s.effs@ == Seq::<EffectKind>::empty(),
            !s.done,
    {
        let res = match mode {
            Mode::DenyOverride => true,
            _ => false,
        };
        Stream { done: false, res, mode, idx: 0, cap, effs: Ghost(Seq::empty()) }
    }

    /// DefaultEffectStream::push_effect
    pub fn push_effect(&mut self, eft: EffectKind) -> (r: bool)
        requires
            old(self).inv(),
            !old(self).done,
        ensures
            final(self).inv(),
            r == final(self).done,
            final(self).mode == old(self).mode,
            final(self).cap == old(self).cap,
            final(self).effs@ == old(self).effs@.push(eft),
    {
        let ghost s = self.effs@;
        proof {
            lemma_has_effect_push(s, EffectKind::Allow, eft);
            lemma_has_effect_push(s, EffectKind::Deny, eft);
            if self.mode == Mode::Priority {
                lemma_allow_first_push(s, eft);
            }
        }

        match self.mode {
            Mode::AllowOverride => match eft {
                EffectKind::Allow => {
                    self.done = true;
                    self.res = true;
                },
                _ => {},
            },
            Mode::AllowAndNoDeny => match eft {
                EffectKind::Allow => {
                    self.res = true;
                },
                EffectKind::Deny => {
                    self.done = true;
                    self.res = false;
                },
                EffectKind::Indeterminate => {},
            },
            Mode::DenyOverride => match eft {
                EffectKind::Deny => {
                    self.done = true;
                    self.res = false;
                },
                _ => {},
            },
            Mode::Priority => match eft {
                EffectKind::Indeterminate => {},
                EffectKind::Allow => {
                    self.done = true;
                    self.res = true;
                },
                EffectKind::Deny => {
                    self.done = true;
                    self.res = false;
                },
            },
        }

        if self.idx + 1 == self.cap {
            self.done = true;
            self.idx = self.cap;
        } else {
            self.idx = self.idx + 1;
        }

        self.effs = Ghost(s.push(eft));
        self.done
    }

    /// DefaultEffectStream::next — the runtime `assert!(self.done)` becomes
    /// the precondition `self.done`, so a verified caller can never panic here.
    pub fn next(&self) -> (r: bool)
        requires
            self.inv(),
            self.done,
        ensures
            r == self.res,
            r == decision(self.mode, self.effs@),
    {
        self.res
    }
}

// ───────────────────── the enforce loop (private_enforce) ─────────────────────

/// The loop in `private_enforce`: push one effect per policy rule and stop as
/// soon as `push_effect` returns true; then read `next()`.
/// `effs[k]` is the effect produced by rule k (Allow/Deny/Indeterminate).
/// `cap = max(policy_len, 1)`; here `effs.len() > 0` (the empty policy is
/// `run_single` below).
pub fn run_effects(mode: Mode, effs: &Vec<EffectKind>) -> (res: bool)
    requires
        effs.len() > 0,
    ensures
        // the loop computes exactly the policy-effect semantics ...
        res == decision(mode, effs@),
        // ... a grant (outside DenyOverride) needs an Allow rule ...
        (res && mode != Mode::DenyOverride) ==> has_effect(effs@, EffectKind::Allow),
        // ... and any Deny rule blocks the grant in the deny-sensitive modes.
        (has_effect(effs@, EffectKind::Deny)
            && (mode == Mode::AllowAndNoDeny || mode == Mode::DenyOverride)) ==> !res,
{
    let n = effs.len();
    let mut st = Stream::new(mode, n);
    let mut i: usize = 0;
    let mut done = false;

    proof {
        assert(effs@.take(0) =~= Seq::<EffectKind>::empty());
    }

    while i < n && !done
        invariant
            i <= n,
            n == effs.len(),
            st.inv(),
            st.mode == mode,
            st.cap == n,
            st.effs@ == effs@.take(i as int),
            done == st.done,
        decreases n - i,
    {
        let eft = effs[i];
        let ghost before = st.effs@;
        done = st.push_effect(eft);
        proof {
            // before == take(i) and st.effs@ == before.push(effs[i])
            assert(effs@.take((i + 1) as int) =~= effs@.take(i as int).push(effs@[i as int]));
        }
        i = i + 1;
    }

    let ghost p = effs@.take(i as int);
    proof {
        assert(p.len() == i);
        assert(is_prefix(p, effs@)) by {
            assert forall|j: int| #![trigger p[j]] 0 <= j < p.len() implies p[j] == effs@[j] by {}
        }
        // the loop ended: either `done`, or every rule was consumed (idx == cap)
        assert(i == n || done);
        if i == n {
            assert(st.idx == st.cap);
        }
        assert(st.done);
        if i < n {
            // stopped early: idx < cap, so a decisive effect must have occurred
            assert(stop_seen(mode, p));
            lemma_early_exit(mode, p, effs@);
        } else {
            assert(p =~= effs@);
        }
        assert(decision(mode, effs@) == decision(mode, p));
    }

    let res = st.next();

    proof {
        if res && mode != Mode::DenyOverride {
            lemma_grant_has_allow_witness(mode, effs@);
        }
        if has_effect(effs@, EffectKind::Deny)
            && (mode == Mode::AllowAndNoDeny || mode == Mode::DenyOverride)
        {
            lemma_deny_blocks(mode, effs@);
        }
    }
    res
}

/// The empty-policy path of `private_enforce`: `new_stream(.., max(0, 1))`,
/// exactly one push, then `next()`.
pub fn run_single(mode: Mode, eft: EffectKind) -> (res: bool)
    ensures
        res == decision(mode, seq![eft]),
{
    let mut st = Stream::new(mode, 1);
    let done = st.push_effect(eft);
    proof {
        // idx reached cap == 1, so the stream is done
        assert(done);
        assert(st.effs@ =~= seq![eft]);
    }
    let res = st.next();
    res
}


} // verus!

fn main() {}