# Appendix A Track C: legal native Dom/Empty/graph roundtrip

14 November 2026. Stacked on the faithful F1/F3 encoding PR #665.

The new predicate \`Structure.IsLegalDomainEmpty\` expresses the
two local boolean laws connecting Dom_F and Empty_F to the
native function fibre. It forbids phantom native outputs with
Dom_F false, and forbids Dom_F=true/fibre empty without Empty_F.

The new decode takes a native fibre as an ENTIRE genuine
Option(Set) value whenever Dom_F holds and returns none
otherwise. All genuinely partial structures reencode after
decoding identically, including some(empty); conversely every
legal native structure is literally the encoding of its decode
on the same carrier. Full maps still use #665's F1 dictionary.

**Next F2:** prove the legal predicate is closed under native
free amalgamation over FULL roots (and hence induction over a
loose B-tree). This is necessary before using the class-free
native B-cover pass for arbitrary rich Option(Set) values.
The present roundtrip does NOT prove that class closure.

No admits or new axioms; five named axiom checks and active
root. Draft until its exact-head full Lean run, no-admission,
source/inventory and axiom checks pass.
