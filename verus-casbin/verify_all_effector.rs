use vstd::prelude::*;

// ================
// File: effector.rs
// Functions: DefaultEffectStream::push_effect (lines 77-123)
//              - covers: index advance (lines 115-123)
//            DefaultEffectStream::next (lines 55-58)
//            DefaultEffectStream::explain (lines 60-69)
// ================

verus!{

    pub struct DefaultEffectStream {
        done: bool,
        res: bool,
        expr: String,
        idx: usize,
        cap: usize,
        // NOTE: in src/effector.rs this field is behind #[cfg(feature = "explain")].
        // The cfg is dropped here so that `explain` (which only exists when that
        // feature is on) can be verified.
        expl: Vec<usize>,
    }

    impl DefaultEffectStream {

        // ---------------- push_effect: index advance ----------------
        fn advance_index(self: &mut DefaultEffectStream)

            requires
                old(self).idx < old(self).cap, // ensures that the index is within bounds before advancing
            ensures
                // ensures that cap never changes
                final(self).cap == old(self).cap,

                // handles when self.idx + 1 != self.cap
                old(self).idx + 1 != old(self).cap ==>
                    final(self).idx == old(self).idx + 1
                    && old(self).done == final(self).done
                ,

                // handles when self.idx + 1 == self.cap
                old(self).idx + 1 == old(self).cap ==>
                    // old(self).idx + 1 == old(self).cap
                    final(self).idx == final(self).cap
                    && final(self).done == true
                ,

            // ---- VERBATIM from src/effector.rs lines 115-123 ----
            {
                if self.idx + 1 == self.cap {
                    self.done = true;
                    self.idx = self.cap;
                } else {
                    self.idx += 1;
                }
            }
            // ---- END VERBATIM ----

        // ---------------- next ----------------
        // `next` returns the final decision of the stream. It is only meaningful
        // once the stream is done (the original code asserts this).
        fn next(&self) -> (r: bool)
            requires
                self.done, // the assert!(self.done) must never fail
            ensures
                r == self.res, // returns exactly the stored decision

            // ---- VERBATIM from src/effector.rs lines 55-58 ----
            {
                assert!(self.done);
                self.res
            }
            // ---- END VERBATIM ----

        // ---------------- explain ----------------
        // `explain` returns None when no policy index was recorded,
        // otherwise Some(copy of the recorded indices).
        fn explain(&self) -> (r: Option<Vec<usize>>)
            requires
                self.done, // the assert!(self.done) must never fail
            ensures
                // empty explanation list ==> None
                self.expl@.len() == 0 ==> r.is_none(),

                // non-empty explanation list ==> Some of an identical list
                self.expl@.len() > 0 ==> (r.is_some() && r.unwrap()@ == self.expl@),

            // ---- VERBATIM from src/effector.rs lines 60-69 ----
            {
                assert!(self.done);
                if self.expl.is_empty() {
                    None
                } else {
                    Some(self.expl.clone())
                }
            }
            // ---- END VERBATIM ----
    }

    fn main(){}

} //verus!