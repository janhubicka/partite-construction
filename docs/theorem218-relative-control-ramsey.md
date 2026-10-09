# Closed-test Ramsey construction over relative-copy controls

Continuation of merged PR #183. The original manuscript and literal
published predicates remain unchanged. All maps and irreducible-test
coverage below use the EXPLICIT closed-test convention.

## What is constructed

Let A and B be finite U-closed relational structures, let A embed into B,
and let D be finite with D -> (B)^A_k. Assume that the image of EVERY
embedding A -> D is a relative U-substructure of D. There is a finite
U-closed C with

* C -> (B)^A_k;
* a positive map C -> D embedding every closed U-irreducible test;
* an embedding into the original B for every closed U-irreducible test in C.

The control D is NOT assumed U-closed. The result is the nontrivial
A-embeds-in-B case of the CLOSED-TEST repair of Lemma 2.29, with its
relative-copy hypothesis retained. The omitted degenerate case is
mathematically immediate: when A does not embed in B, take C=B and any
B-copy in D; every B-copy is vacuously monochromatic. This degenerate
wrapper has not been added as a separate Lean theorem in this patch.

This does not prove Lemma 2.28, which must also handle A-copy ranges that
are not relatively closed in the original D. It does not change the
repaired local-finiteness axiom by assuming its original control is closed.

## 1. Native initial picture, not an assumed input

Use the existing initial picture P0 indexed by all embeddings beta:B->D.
Its carrier is Emb(B,D) x B, with each relation tuple wholly inside one
indexed B-copy. The index type is nonempty, obtained by applying the
original Ramsey arrow to a constant colouring. This also handles empty
B without losing nullary relation values.

Every union of index fibres is a relative U-substructure: a closure tuple
has a nonempty root and lies wholly in one fibre, so one root coordinate
already determines its fibre. This uses the existing positive-root-size
assumption in the published ClosureRule, not a newly imposed restriction.

The prescribed closure roots are ordinarily irreducible and therefore
lie in one fibre. Existence and uniqueness of their closure tuples follow
from the closed base B and the relative closedness of that fibre. The
root-cover theorem proves P0 closed without assuming D closed.

A CLOSED U-irreducible test T in P0 lies in one fibre. To see this, choose
one index met by T and split T into the vertices with that index and all
remaining vertices. The sides are relatively closed in T; since T is
closed they are intrinsically closed. Every tuple of T lies wholly on
one side, so U-irreducibility makes one side all T. The chosen vertex
rules out the complement. An empty test is assigned any index.

Thus the test factors through an actual B-copy. Composing that factor
with beta:B->D proves protectedness of the initial part projection.
No claim is made about nonclosed intrinsically irreducible tests.

## 2. Closed attaching supports suffice

In the local Picture step, let p:P->D be protected, P closed, and
alpha:A->D an embedding. The actual attaching support is p^{-1}(alpha[A]).
To prove the local theorem it suffices that THIS support be relatively
closed in P. Closedness of all of D is unnecessary.

Restrict P to the support. The restriction is closed, and its part map
to A remains protected. Apply the finite Hales--Jewett partite lemma and
the positive-power protection theorem from #181. Its native coordinate
power is a closed protected core. Attach copies of P along ALL existing
partite embeddings, just as in the native Picture.build.

The closed-attachment theorem proves the whole picture closed. Protected
core and copy maps glue to a protected map to D. Every closed irreducible
test lies in the core or an old copy. Core tests embed in A and therefore
in P; thus all such tests embed into the old P.

For a whole finite pass, the relative-copy assumption on alpha[A] implies
the required support condition at every stage by positive preimage.
Backward induction gives CanonicalOn for all processed profiles, and
closed-test embeddability composes back to the ORIGINAL P0.

## 3. Global colour extraction

The pass enumerates the existing RelevantEmbedding A B D type: exactly
the embeddings A->D that factor through a B-copy. For any colouring of
A-copies in the final C, it gives a P0-copy on which the colour of an
A-copy depends only on its projection to D.

Choose one initial representative for each relevant A-embedding in D;
assign the corresponding colour. Give irrelevant A-embeddings any default
colour. Apply D -> (B)^A_k. Every A-subcopy of the resulting B-copy is
relevant, and its initial representative has the same colour as the
corresponding A-copy in the indexed B-component of P0. Composing that
component embedding with the selected P0-copy gives a monochromatic B
in C. This is the global Arrow, not merely CanonicalOn.

Finally, factor a closed irreducible test of C through P0 and then through
one of its original B-copies. The final coverage target is B, not P0.

## 4. A fully constructed rank-one local-completion case

Assume additionally that B belongs to a closed-hereditary class K, B and
D are ordinarily irreducible, and the corrected local-completion axiom
holds for the original B,D at a cutoff n<=1. The constructed C above is
an actual Ramsey witness, not an assumed rank-controlled structure.

Every closed induced test of U-size at most n is U-irreducible, hence
embeds in B and has a K-completion. The closed-hull restriction theorem
supplies completions of ALL exact weak tests of at most n vertices, with
no hull-cardinality claim. Coverage and closed hereditariness provide the
corrected membership premise. Apply the corrected local axiom at the
same B,D,n and the B-copywise colour transfer to obtain a Ramsey witness
inside K. Strong amalgamation is not needed for this rank-one special case.

## Formal scope

Twelve declarations in three modules are explicitly imported and
individually printed by CheckClosureAxioms:

* ClosureProtectedInitial: five initial-picture/closed-test theorems.
* ClosureRelativeControlPicture: actual closed-support Picture gluing,
  its local Ramsey witness, and the finite relative-profile pass.
* ClosureRelativeControlRamsey: global extraction, constructed relative-
  control Ramsey witness, its closed-control corollary, and cutoff-one
  local-completion implication.

Consult PR #184 for the FINAL full-project build and permitted-axiom
audit result. Source existence or a partial imported-module build alone
is not certification. All previous checks are retained. Direct proof-
scope review is performed; no separate independent referee process is claimed.

## Remaining work and proposed proof placement

The new initial-picture and extraction arguments close the remaining
assembly around the repaired relative-copy Lemma 2.29. Its proof can use
the same initial picture and finite profile enumeration as the original,
with the coverage assertion restricted to CLOSED irreducible tests.

The two central obligations are still:

1. The initial repair over arbitrary nonclosed D when A-copy ranges may
   not be relatively closed. The new local theorem identifies the exact
   input needed: relative closedness of the actual attaching support.
   An intrinsic closed A-copy in nonclosed D does NOT supply that input.
2. The higher-rank increment for actual Picture histories. In particular,
   a free cut need not lower the absolute generating rank of either side.
   The no-common-variable-coordinate branch still requires a genuine
   boundary-aware completion construction, not a relative-completion oracle.

Consequently the full repaired Theorem 2.18 remains unvalidated here.
