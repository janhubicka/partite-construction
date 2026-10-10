# Theorem 2.18: part-predicate language transport needs root-sensitive symbols

10 October 2026; continuation of the verified weak-cut gluing patch #186.
The original manuscript is frozen. This is a formalization checkpoint, not
a claim that the unrestricted initial recursive repair is finished.

## What the new Lean module proves

`ClosurePartPredicates.lean` defines the relational unary-part extension
`RelLanguage.withPartPredicates P`, its exact structure expansion and
reduct, and the conversions between the full induced embeddings and
partite-system embeddings.

A map between expanded structures is a relational induced embedding
if and only if its underlying map is an induced embedding and it
preserves part labels. The conversions are inverse, including nullary
relations and repeated relation entries. Ordinary Gaifman irreducibility
is unchanged, because unary predicates cannot witness adjacency between
distinct vertices.

These are necessary parts of the proposed initial recursive argument.
They are **not sufficient** for transporting the closure description.

## Exact obstruction to a naive closure-rule lift

A closure rule in `ClosureDescription2019.lean` consists of one symbol
R and ONE particular finite *induced* root structure. Its validity clause
requires that **every** R-tuple match that root; its totality clause
requires one R-tuple over every embedded root.

Suppose the old description has a unary-root rule using the binary
closure symbol R and we add unary predicates `Part_a` and `Part_b`.
To support both parts, a tempting but false lift is to introduce two
rules on the SAME old relation symbol R, one whose root has `Part_a`
and another whose root has `Part_b`.

If the expanded structure has a tuple R(x,y) with `Part_a(x)`, the
first rule's validity condition is satisfied, but the second rule's
validity condition fails: x does not realize the `Part_b` root.
Requiring both lifted rules to be closed would forbid ALL R-tuples,
contradicting totality at every root.

Therefore **simply enumerating part assignments to closure roots while
keeping their closure-relation symbols unchanged is not a valid
translation** of the 2019 axioms. The problem is not resolved by
full induced embeddings, and one must not claim that U-closedness
or U-irreducibility is invariant under this naive lift.

## Safe construction alternatives

(1) Split each designated closure symbol by the part assignment of
its root, interpreting the tagged relation as the old relation
restricted to closure tuples with those root labels. Lift the root
structure with its corresponding unary part predicates. Keep enough
relation data to recover the old reduct and reflect nonclosure tuples.
The transformed rules then have genuinely DISTINCT relation symbols.

(2) Enrich the interface of a closure description so that a symbol is
allowed a finite family of admissible root types, with tuple validity
tested existentially among that family's roots and uniqueness tested
per matched root. That is a more substantial change to Definition
2.12 and the existing Lean API.

The tagged-relation approach (1) is the least disruptive to existing
proofs because each lifted rule still has one fixed root and one
designated relation symbol. It needs a careful equivalence of
U-closedness, relative U-substructures, protected closed tests and
completions under reduct; the latter must preserve the exact weak test
size. It also needs correct flattening after the inner construction.

## Remaining theorem validation

The merged #185 already proves that closed selected-profile copies
in the actual temporarily conflicting native line attachment are
relatively U-closed. The new part-predicate module only addresses the
language interface needed to name those parts in a recursive inner
application. No proof currently transports the entire closure
description by the proposed tagged-symbol construction.

The main higher-rank increment remains open. In #186 the weak
source-cut gluing step was completed without assuming its root is
closed; the two projected side-generator budgets still must come
from actual Picture histories or a stronger justified invariant.

This checkpoint is separate from the draft #182 literal-definition
audit. The paired-equivalence class from #182 is not locally finite
under the repaired convention.
