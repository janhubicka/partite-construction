# A genuinely weaker predecessor invariant for native unary functional iteration

**18 October 2026 — English proof and independent adversarial audit before Lean.**

The currently validated \`SetAmbientRelativeWeakTreeWitness.AtMost\`
requires strict full-functional B-tree weak-history witnesses for
ALL exact weak tests I in a functional control D of |I|≤m.
This is stronger than the desired final Appendix A conclusion,
which tests function-closed substructures. The unary local mixed
step can often be based on a weaker CLOSED-control predecessor.

## Definition: AtMostClosed

For finite functional D, selected irreducible A and irreducible
Base B, define

    AtMostClosed(A,Base,D,m)

to assert the same actual strict full-functional B-tree witness,
ambient full A-copy intersection certificates and EVERY finite
projected history, but ONLY for finite I⊆D which are
function-closed in D and satisfy |I|≤m.

There is an immediate forgetful arrow

    AtMost(A,Base,D,id,m) => AtMostClosed(A,Base,D,m),

but not conversely. Indeed, unary F(a)=b and I={a}
is a legitimate WEAK test but is not function-closed.

## Closed occupied relative target mark

Fix a FULL α:A↪D, a finite D-closed projected side set I
of |I|≤m, and assume the occupied α-boundary

    H={a∈A | α(a)∈I}

is function-closed (automatically true because α is full
and I is function-closed).

Request the AtMostClosed predecessor witness on **the
original exact I**, with the caller's projected history
augmented by every singleton control-part test. The
existing \`SetAmbientRelativeWeakTreeWitness.
protected_of_closedOccupiedA\` attaches a single fresh
TARGET B-copy over the FULL A.induce H root of the
old target A-mark. Every output outside H is fresh in
the marked B-copy; singleton histories prevent wrong
target hits on occupied H.

Restrict the finite history list back to the caller's
original list. This produces a verified
\`SetAmbientProtectedWeakTreeWitness\` on the SAME exact
I with no weak-set closure and no added tested vertices.

This derivation uses only the weaker **closed** rank-m
predecessor and the actual closure of I and H.
The root gluing is full because H is closed; it is not
a universal protected mark on arbitrary nonclosed tests.

## Proof audit

* This is true for genuinely multivalued set-valued
  functions, retaining transversal outputs where supplied.
* It does not turn the arbitrary weak set I into its
  function closure: closedness is an INPUT hypothesis,
  and the rank budget counts exactly I.
* The independent \`Option(Set)\` defined-empty bit
  is outside the current nonempty-fibre 2019 convention.
* A relative mark on an arbitrary NONCLOSED projected
  I does not follow. The parity and C5 counterexamples
  prohibit replacing the present hypotheses by a blanket
  compatibility assumption.
* This alone does not establish the complete
  unary n-pass strict sparsening theorem: the actual HJ
  core/pure/mixed picture steps must be shown to preserve
  this weaker AtMostClosed history invariant. That is
  the next mathematical and Lean-level task.

## Lean deliverables

Define \`AtMostClosed\`, prove \`AtMost.toClosed\`, and
derive \`AtMostClosed.protected_of_closedOccupiedA\`.
Reuse the already validated protected-target construction
and history restriction; no new gluing construction.
Provide named axiom checks and full project CI. This is
library preparation for the closed-test unary iteration,
not an unsupported global theorem marker in the survey.
