# Why an entire native little-Picture rest need not be U-closed

11 October 2026. This audit is deliberately separate from the
successful **selected closed-test** protection theorem in merged #185.

Let Old have P-root r, non-P output o, and its unique prescribed
binary closure tuple R(r,o). The exact attaching support S={r}
is NOT relatively U-closed in Old.

Let Core have a single P-root c with no R-tuple. The attaching map
from Old|S to Core takes r to c and is a FULL induced embedding.
Its range is relatively U-closed INSIDE the semi-closed Core:
Core has no closure tuples, so there is no conflicting output there.
This agrees with the canonical line-range condition of #185.

Attach TWO indexed copies of Old along S. The actual attachment has
vertices c,o0,o1 and tuples R(c,o0), R(c,o1). It is non-semi-closed.
Its entire core {c} fails relative U-closedness because the roots
of both tuples lie there but the outputs do not. The REST of copy 0,
{c,o1}, also fails: R(c,o0) leaves that rest.

The exact regression script
`scripts/check_nonclosed_attachment_rest.py` was **executed
successfully** on the explicit finite structure above. The
general Lean theorems in this PR establish the same phenomenon
for ANY rules, base/core, attaching family and tuple rooted in
S with at least one output outside S. Once their final full CI
and axiom audit pass they can be marked kernel-verified.

There is NO conflict with #185: its theorem protects ranges
of genuinely U-CLOSED tests embedded wholly in Core, not Core
itself. In this one-vertex Core, no nonempty such test exists,
since c is a P-root with no R-output. The positive hypotheses
of #185 therefore remain satisfied and its conclusion is not
falsified.

**Implication for the repaired Lemma 2.30:** it would be invalid
to take an arbitrary closed source T and invoke the general
positive-map inverse-image lemma of draft #236 with target sides
equal to the entire native copy/rest sets. Those sets are a
true free tuple cover but are generally NOT relative U-substructures.
One must use the particular closed selected-profile tests,
or derive a history-dependent decomposition whose sides are
actually relatively U-closed in the target.

The printed TeX and literal 2019 predicates remain unchanged.
This is a strategy audit, not a refutation of the multiamalgamation
theorem.
