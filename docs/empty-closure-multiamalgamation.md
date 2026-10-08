# Empty-closure multiamalgamation: Theorem 2.18 with U = ∅

**Lean-verified 8 October 2026.** This is a self-contained special case of
Hubička--Nešetřil, *All those Ramsey classes*, Advances in Mathematics 356
(2019), Theorem 2.18. It does **not** assume that the target class is closed
under free amalgamation.

## Statement

Let R be a Ramsey class of finite irreducible relational structures, and
let K ⊆ R satisfy:

1. heredity for substructures;
2. finite strong amalgamation;
3. the locally finite completion property of Definition 2.17(4) with
   closure description U = ∅.

Then K is Ramsey.

For fixed B ∈ K and C0 ∈ R, the locally finite completion property
provides n such that any finite C satisfying:

- a homomorphism-embedding C → C0;
- every irreducible substructure belongs to K;
- every induced substructure on **at most n vertices**, without closure
  enlargement, has a K-homomorphism-embedding completion;

has a finite K-completion **with respect to copies of B**. The last
completion is one vertex map preserving every B-copy by an induced
embedding; it need not be a global homomorphism.

Lean declarations:

- `FiniteStrongAmalgamationClass`
- `EmptyClosureLocalFiniteness`
- `FiniteRamseyClass`
- `emptyClosure_multiamalgamation_isRamsey`

The colour type in `FiniteRamseyClass` is an ordinary finite small
type, which suffices for every finite number of colours required by
the published Ramsey class definition.

## Proof, matching the partite construction

Fix A,B ∈ K and a colour set κ. Obtain
C0 ∈ R with C0 → (B)^A_κ by the Ramsey property of R.
Choose n from local finiteness.

The previously checked strict relational sparsening theorem
`sparseningRamsey_strict_baseIrreducible_all` constructs a finite
Ramsey witness C with:

- C → (B)^A_κ;
- a global relational homomorphism-embedding C → C0;
- every induced test of at most n vertices homomorphism-embeds into
  a **strict** tree amalgam of copies of B;
- every irreducible substructure of C is contained in a B-copy.

The latter property and heredity of K imply every irreducible
substructure of C belongs to K.

To use local finiteness, it remains to complete every small test in K.
The key is a finite strong-amalgamation induction over a strict B-tree T.

At a tree gluing T = T1 ∪_D T2, each root map
D → Ti has its image contained in an irreducible substructure.
By the irreducible containment lemma for strict B-trees, that
irreducible is contained in one constituent B-copy. Therefore a
B-copywise completion of Ti into Ki ∈ K restricts to an **embedding**
D → Ki. Strongly amalgamate K1,K2 over those embeddings, obtaining
Q ∈ K. The two old vertex maps now fold to a single map T → Q
preserving every B-copy. The target may have extra mixed relations,
and the folded map need not be a global embedding or even a
homomorphism. This is exactly
`TreeAmalgam.copywiseCompletion_inStrongClass`; its independent
fold lemma is `CopywiseCompletion.fold_free`.

Next, any map T → Q preserving all constituent B-copies is nevertheless
a *homomorphism-embedding*: every irreducible substructure of T is in a
B-copy, while every relation tuple spans an irreducible range. Thus
`CopywiseCompletion.toHomomorphismEmbedding_of_strictTree`
and `HasTreeCompletion.toKCompletion` compose a homomorphism-embedding
S → T from a tested induced substructure with T → Q to obtain
a genuine K-completion of S. Again no generated closure of S is used.

The locally finite condition yields a B-copywise map C → C' ∈ K.
Because A is irreducible and every irreducible in C lies inside a
B-copy, this map preserves all A-copies as well. The already checked
`arrow_of_copywiseCompletion_inClass` transfers the colouring to
give C' → (B)^A_κ.

The exact fixed-arrow endpoint is
`ramsey_of_emptyClosure_multiamalgamation`; the class-level theorem
is `emptyClosure_multiamalgamation_isRamsey`.

## What remains for arbitrary nonempty U

The above is the U=empty specialization only. For general closure
descriptions the paper's locally finite axiom is stated on U-closed C
but quantifies over **not necessarily U-closed** substructures on at
most n vertices, and the local invariant involves U-size.
The new abstract partial-function semantics (PR #126) supplies the
appropriate *direction of domain preservation*, but does not by
itself encode all closure descriptions (R^U,R) with non-unary,
relationally prescribed roots.

The next task is a general U-closure interface and a U-relative
replacement for the two lemmas above:

1. A strict U-tree whose gluing roots lie in U-irreducible containers
   has copywise K-completions by strong amalgamation.
2. Every weak induced test on exactly n tested vertices admitting a
   U-homomorphism-embedding into such a tree has a (K,U)-completion.

Then the U-size iterated partite construction can feed the
locally finite completion axiom without strengthening source
homomorphisms to reflect undefined domains.

The counterexample to the 2026 survey's stronger *total-fibre*
homomorphism convention is unrelated to this 2019 transfer.
