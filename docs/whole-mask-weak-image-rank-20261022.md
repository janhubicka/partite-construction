# Exact weak-image USize monotonicity — 22 October 2026

The corrected functional iterated induction uses weak substructures on exact carriers: when an output is not wholly retained in a weak carrier it becomes undefined, while defined-empty outputs remain defined. The source-defined homomorphism restricted to a whole-weak carrier S maps surjectively onto the exact carrier f[S] and cannot increase its intrinsic finite generator rank (checked in merged #449).

Merged #465 and #466 identify that intrinsic weak generator rank with the 2019 USize of the induced ambient full-root complete-mask tagged graph on the **same exact carrier**. Compose the two theorems. If the source USize is ≤ n then the target induced ambient USize on f[S] is ≤ n. In particular USize(f[S]) ≤ USize(S).

This is the generator-rank monotonicity required when projecting exact weak tests during the iterated induction. It does not assert the stronger false claim that the cardinalities of the carriers decrease strictly or that arbitrarily glued mixed targets admit valid transversal functional completions.
