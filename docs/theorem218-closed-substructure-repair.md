# Theorem 2.18: coordinated closed-substructure repair

9 October 2026. Positive continuation after #181; literal counterexample
work in #182 remains separate. This is an explicit proposed correction,
not an implication from the printed hypothesis. Frozen manuscript and
literal predicates are unchanged. Final build/audit evidence is recorded
in PR #183. The complete repaired main theorem is not claimed proved.

## Exact proposed text changes

**Definition 2.15, map clause:** keep the intrinsic U-irreducibility
predicate unchanged, but require a U-homomorphism-embedding to restrict
to an embedding on every **U-closed U-irreducible** substructure of its
source. Global positivity remains required. A completion still has an
ordinary irreducible target. Its source can be nonclosed; in that case
its own closed irreducible substructures are the protected tests.

**Definition 2.17(4a):** use that amended completion notion, without
adding U-closedness of the original C0.

**Definition 2.17(4b):** replace the condition by: "Every U-closed
U-irreducible substructure of C is in K."

**Definition 2.17(4c):** retain "not necessarily U-closed" and the
original bound on the number of vertices of the exact tested structure.
Use the amended completion notion consistently. Do NOT replace these
weak tests by only closed n-vertex tests.

The conclusion is unchanged: one K-completion respecting all B-copies.
The first three class assumptions are unchanged: finite closed members,
closed hereditariness, and strong amalgamation. R is a Ramsey class of
finite ordinary irreducibles. The integer n(B,C0) is fixed using the
ORIGINAL witness before any refinement and never reselected later.
The code also proves monotonicity in the cutoff, including cutoff zero.

Qualify the coverage conclusions in Lemmas 2.28--2.31 by closedness and
use the amended maps. This is NOT a claim that their full proofs have
already been repaired. Restricting (4b)'s tested family weakens that
antecedent and therefore strengthens the local-completion requirement
on K. No equivalence with the printed axiom is asserted.

## Precise formal contract and final implication

`ClosureClosedLocalFiniteness.lean` defines `ClosedUHereditary`,
`ClosedUIrreduciblesIn`, `ClosedULocalCompletionAt` and the proposed
`ClosedUMultiamalgamationClass`. No new axiom or unproved instance is added.

Six theorems establish membership from actual B-copy coverage using only
closed hereditariness; nonvacuity of the repaired membership condition
on genuine K-members; restriction to weak sources; cutoff monotonicity;
and the local-completion/Ramsey endpoint from explicit rank data.

For any original weak test S with |S| <= n, its induced closed ambient
hull has U-size <= |S|. Complete the hull using the supplied rank
invariant and restrict the map to the SAME original S and SAME target.
This proves amended (4c), not a substituted assertion about a larger
vertex set. Closed-copy coverage supplies (4b); the original-control
protected projection supplies (4a). The local axiom and B-copywise
colour transfer then produce a K-Ramsey witness.

The rank-controlled Ramsey picture remains an EXPLICIT input of the
endpoint theorem. Its name and hypotheses do not masquerade as a proof
of the construction or of the complete main theorem.

## A stronger cut lemma for the actual weak tests

`ClosureRelativeMapGlue.lean` has four new theorems. In a free source
amalgam, it is enough that the two side ranges are relative
U-substructures. Neither the whole source, either side nor their common
cut needs to be intrinsically U-closed.

Proof: pull both side ranges back into an embedded CLOSED U-irreducible
test T. They are relative U-substructures of T, hence intrinsically
closed, and freely cover T. Irreducibility localizes T to one side.
The relative range hypotheses survive any exact weak source restriction.
Compatible protected positive side maps therefore glue.

Independent projected K-completions can also be glued in this setting,
provided the SAME closed K-member Q embeds in both projected sources and
their original boundary maps factor through one map to Q. Each completion
embeds Q automatically, because Q is closed and ordinarily irreducible.
Strongly amalgamate their targets over Q. The source boundary itself may
be nonclosed or collapsed. Only the source amalgam is free; the target
may add relations. The target Q hypothesis is NOT dropped.

Concrete weak-cut check: ambient vertices r,o,a,b, unary root P(r),
sole closure tuple R(r,o). Closed sides {r,o,a} and {r,o,b} become
{r,a} and {r,b} on the exact weak test {r,a,b}. The test, both sides,
and their common cut {r} are nonclosed; the sides remain relatively
closed. This is genuinely outside the old closed-source-cut hypothesis.

## Constructed whole finite protected pass

`ClosureProtectedPass.lean` iterates the ACTUAL local Picture lemma
from #181 over an arbitrary finite list of A-embeddings into closed D.
Inputs are a finite closed old D-partite picture, its protected part
map, and an A-copy in it. The result is finite and closed, has a
protected part map, and every closed irreducible test embeds in the
ORIGINAL old picture, not merely an unspecified intermediate stage.

The colour conclusion is `CanonicalOn`: for any colouring one can find
a copy of the original picture on which each listed projection profile
is monochromatic. DIFFERENT profiles may still have different colours.
This is a whole finite canonical pass, not yet the global Ramsey arrow
extracted using an original Ramsey witness and initial B-copies.

Proof: finite backward induction. Use a constant colouring to preserve
an A-copy at each stage, apply the genuine local Picture witness, pull
back the subsequent colouring, and compose embeddings. Coverage composes
back to the original input as well. No assumed refinement oracle.

`protected_pass_with_rank_one` retains corrected (4b) and obtains all
closed rank-at-most-one completions, including rank zero. Such a test
is U-irreducible, so in fact it belongs to K and has an identity
completion. This is the BASE invariant, not higher-rank preservation.

## Validation and remaining work

All twelve theorem declarations are individually included in
CheckClosureAxioms. Every earlier audit line is retained. No custom
axioms, sorry, full-hereditary K assumption, or hidden hereditary
irreducibility of A is introduced. The final combined PR head must pass
the full build and permitted-axiom audit; the PR records exact hashes
and workflow evidence. No separate independent referee process is claimed.

The companion standard-library finite regression (conversation artifact)
checks 630 relative free covers and 2,804 protected-test instances across
three models. 82 of those covers have a NONCLOSED common cut. It includes
the five-vertex seed obstruction, verifies that dropping relative side
closedness can break localization, and checks that a two-element closed
matching is not excluded by singleton nonclosed tests. These are finite
regressions, not additional Lean model certificates.

Still outstanding: the higher-rank increment on actual Picture histories,
especially the no-common-variable-coordinate branch; the initial closed
repair over possibly nonclosed original C0; and full theorem assembly.
Relative cut gluing does not give the two target-rank bounds. The known
four-vertex boundary-budget obstruction remains: adding the closed
boundary can consume the rank supposedly saved by losing a generator.
Do not infer that proper closed sides have smaller U-size, that raw
images are closed, or that hull cardinality is bounded by generator count.
