# Full native multivalued weak-substructure induction is the canonical singleton U-induction

**20 October 2026 — English proof, adversarial audit before Lean**

Fix a finite genuine transversal set-valued-functional partite
system B over output part carrier P, with positive function arities.
Its canonical per-part singleton split B^P retains every original
output in one primitive partial function (F,q) while preserving
ALL original vertices and all parts.

For any literal arbitrary weak vertex set S⊆V(B), let
B|ᵂS be the native weak function structure whose outputs are
restricted to S. Let E denote the AMBIENT complete-root
tagged equality-pattern expansion of B^P, and let E|S be
its induced relational structure on precisely S.

For every T⊆S the full dictionary is

\[
  \mathrm{IsClosed}_{B|^w S}(T)
    \iff \mathrm{IsUSubstructure}_{\mathcal U,E|S}(T).
\]

Indeed the original weak F-output incidence y∈F_{B|ᵂS}(x)
is equivalent to its singleton part-indexed incidence
y∈(F,part(y))_{B^P|ᵂS}(x), and all singleton outputs
remain original outputs. Thus the native weak closed-set
predicates agree for every T. Apply the checked generic
positive-arity weak ambient-tag dictionary (PR #444)
to the singleton structure B^P.

The two relative closure operators inside S therefore
agree literally on the SAME weak carrier; so do
their generating seed sets, and for any finite n,

\[
 (B|^{w}S).\mathrm{GeneratedByAtMost}(n)
  \iff
 \mathrm{USize}(\mathcal U,E|S)\le n.
\]

This is **intrinsic generator size of the exact weak test**,
not the size of its potentially larger ambient generated hull.
The ambient root tags retain old function-domain activity
even after all output vertices disappear from S, so E|S is
semi-closed rather than falsely total. This is exactly the
intermediate invariant used in the corrected U-closed proof.

## Adversarial audit

* The new theorem holds for multi-output original F because
  every output part q is represented by its own singleton
  primitive function; no output ordering or ranking is chosen.
* S and T remain literal vertex subsets throughout;
  neither is closed to its ambient function-generated hull.
* Every surviving weak function value stays fully recorded,
  while an active ambient domain with zero surviving
  outputs remains an OLD tagged domain record, not a
  forged defined-empty output.
* The original (nonclosed) weak test need NOT satisfy the
  U-closed totality axiom; only the semi-closed assertion
  already checked is used in the global Picture proof.
* Primitive positive arity is required by the 2019 fresh
  full-root closure-description coding; nullaries are
  addressed separately.
* The equality concerns INTRINSIC weak generator rank, and
  does not assert that USize(ambient hull of S) equals
  USize(E|S), an independently refuted shortcut.
* Nothing upgrades the original-partial EHN projection
  to global full fibre reflection or independently
  chosen strict targets to compatible root completions.

## Lean acceptance

First prove closedness for every T⊆S is invariant under
the output-part split of the exact weak native function
structure. Then compose the verified generic PR #444
weak-tagged dictionary, derive literal equality of both
weak closure hulls on S, and deduce the finite generator
USize comparison. Require named axiom checks and full CI.

The remaining genuine functional n-pass sparsening
problem is TARGET profile compatibility across mixed
weak-root attachments, not a mismatch of weak rank,
weak source closure or Hales–Jewett source objects.
