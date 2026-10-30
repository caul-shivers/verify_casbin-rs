use vstd::prelude::*;

// ================
// File: effector.rs
// Function: DefaultEffectorStream::push_effect (lines 77-123)
// Covers: effect logic (lines 78-113) + index advance (lines 115-123)
// ================

verus!{

    // VERBATIM from src/effector.rs lines 3-8
    #[derive(PartialEq, Eq, Clone, Copy, Structural)] // DEVIATION: added Structural derive to allow for equality checks in specs
    pub enum EffectKind {
        Allow = 0,
        Indeterminate = 1,
        Deny = 2,
    }

    // DEVIATION: models the 4 strings accepted by new_stream (effector.rs lines 40-43) as a type-safe enum
    #[derive(PartialEq, Eq, Clone, Copy, Structural)]
    pub enum ExprKind {
        AllowOverride,                  // "some(where (p_eft == allow))"
        SomeAllowAndNotSomeDeny,        // "some(where (p_eft == allow)) && !some(where (p_eft == deny))"
        DenyOverride,                   // "!some(where (p_eft == deny))"
        PriorityOrDeny,                 // "priority(p_eft) || deny"
    }
    
    pub struct DefaultEffectStream {
        done: bool,
        res: bool,
        expr: ExprKind,     // DEVIATION: changed from String to ExprKind
        idx: usize,
        cap: usize,
        #[cfg(feature = "explain")]
        expl: Vec<usize>,
    }

    impl DefaultEffectStream {

        fn apply_effect(self: &mut DefaultEffectStream, eft: EffectKind)
            requires
                !self.done,
                self.idx < self.cap,
            ensures
                // ensures fields that are not modified by this function remain unchanged
                final(self).idx == old(self).idx,
                final(self).cap == old(self).cap,
                final(self).expr == old(self).expr,

                // A: ExprKind::AllowOverride
                // "some(where (p_eft == allow))"
                old(self).expr == ExprKind::AllowOverride ==> (
                    // if policy effect == Allow
                    if eft == EffectKind::Allow {
                        final(self).done == true
                        && final(self).res == true
                    }
                    // else policy effect != Allow
                    else {
                        final(self).done == old(self).done
                        && final(self).res == old(self).res
                    }
                ),

                // B: ExprKind::SomeAllowAndNotSomeDeny
                // "some(where (p_eft == allow)) && !some(where (p_eft == deny))"
                old(self).expr == ExprKind::SomeAllowAndNotSomeDeny ==> (
                    // if policy effect == Allow
                    if eft == EffectKind::Allow {
                        final(self).res == true
                        && final(self).done == old(self).done
                    }
                    // else if policy effect == Deny
                    else if eft == EffectKind::Deny {
                        final(self).done == true
                        && final(self).res == false
                    }
                    // else policy effect == Indeterminate
                    else {
                        final(self).done == old(self).done
                        && final(self).res == old(self).res
                    }
                ),

                // C: ExprKind::DenyOverride
                // "!some(where (p_eft == deny))"
                old(self).expr == ExprKind::DenyOverride ==> (
                    // if policy effect == Deny
                    if eft == EffectKind::Deny {
                        final(self).done == true
                        && final(self).res == false
                    }
                    // else policy effect != Deny
                    else {
                        final(self).done == old(self).done
                        && final(self).res == old(self).res
                    }
                ),

                // D: ExprKind::PriorityOrDeny
                // "priority(p_eft) || deny"
                old(self).expr == ExprKind::PriorityOrDeny ==> (
                    if eft != EffectKind::Indeterminate {
                        final(self).done == true
                        && final(self).res == (eft == EffectKind::Allow)
                    }
                    else {
                        final(self).done == old(self).done
                        && final(self).res == old(self).res
                    }
                ),

        // ---- VERBATIM from effector.rs lines 78-113, except for DEVIATION ----
        {
            if self.expr == ExprKind::AllowOverride {
                if eft == EffectKind::Allow {
                    self.done = true;
                    self.res = true;
                }
            } else if self.expr == ExprKind::SomeAllowAndNotSomeDeny{
                if eft == EffectKind::Allow {
                    self.res = true;
                } else if eft == EffectKind::Deny {
                    self.done = true;
                    self.res = false;
                }
            } else if self.expr == ExprKind::DenyOverride {
                if eft == EffectKind::Deny {
                    self.done = true;
                    self.res = false;
                }
            } else if self.expr == ExprKind::PriorityOrDeny
                && eft != EffectKind::Indeterminate
            {
                self.res = eft == EffectKind::Allow;

                self.done = true;
            }
        // ---- END VERBATIM ----
        }


        fn advance_index(self: &mut DefaultEffectStream)

            requires
                old(self).idx < old(self).cap, // ensures that the index is within bounds before advancing
            ensures
                // ensures untouched fields never change
                final(self).res == old(self).res,
                final(self).expr == old(self).expr,
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
    
        fn push_effect(self: &mut DefaultEffectStream, eft: EffectKind) -> (r: bool)
            requires
                !old(self).done,
                old(self).idx < old(self).cap,
            ensures
                // ensures untouched fields remain unchanged
                final(self).cap == old(self).cap,
                final(self).expr == old(self).expr,

                // ensures idx is advanced correctly
                final(self).idx <= final(self).cap,

                // push_effect returns the correct result
                r == final(self).done,

        {
            self.apply_effect(eft);
            self.advance_index();
            self.done
        }
    }

    fn main(){}

} //verus!