use vstd::prelude::*;

// ================
// File: effector.rs
// Function: DefaultEffectorStream::push_effect (lines 77-123)
// Covers: index advance (lines 115-123)
// ================

verus!{

    pub struct DefaultEffectStream {
        done: bool,
        res: bool,
        expr: String,
        idx: usize,
        cap: usize,
        #[cfg(feature = "explain")]
        expl: Vec<usize>,
    }

    impl DefaultEffectStream {
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
    }

    fn main(){}

} //verus!