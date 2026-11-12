# Track B finite rank-gap regression (12 November 2026)

A genuine unary native structure on three vertices has one nonempty multivalued fibre F(0)={1,2}, no other function values, and identity part map (hence output transversality). The faithful Option(Set) conversion is by the library's original `toNonemptyPartial`, not an invented independent-domain source.

The original exact weak cut is S={0,1}. Clipping retains the output 1, so a single vertex 0 generates all of S; whole-fibre weak deletion loses the entire F(0) value because vertex 2 is outside S, so every subset is function-closed and at least two generators are needed. The formal statement is `exact_weak_rank_gap`; its two direct conjuncts, exact fibre evaluations, and genuine output transversality have root-level named `#print axioms` checks.

By the previously kernel-checked exact same-cut rank dictionaries, this difference also forbids identifying the two canonical ambient 2019 USize thresholds on arbitrary weak tests. It does not contradict qualified equality under `NoPartiallyRetainedValues` or genuine function-closedness (Track B PR #615), and it has no bearing on the independent intrinsic-to-ambient local completion obligation (Track C) or strict mixed-root target trees (Track D).

**Status:** draft until exact-head full Lean build and named axiom audit succeed; only additive sources/checks/docs, frozen survey not changed.
