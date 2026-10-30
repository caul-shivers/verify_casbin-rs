use vstd::prelude::*;

// ================
// File: effector.rs
// Functions: DefaultEffectStream::next (lines 55-58)
//            DefaultEffectStream::explain (lines 60-69)
// Both are methods of `impl EffectorStream for DefaultEffectStream`.
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