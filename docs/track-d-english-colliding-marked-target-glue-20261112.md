# Track D — English proof first: strict target gluing over a *noninjective* source-root map

**12 November 2026. Scope:** a theorem for genuine full-functional source
free amalgams and original-2019 (source-defined) partial
homomorphism-embeddings. This is a *valid conditional gluing step*, not yet
an existence proof for the arbitrary ordered Hales–Jewett history. The
numbered Nešetřil programme survey and all collaborator TODOs remain frozen.

## 1. Exact mathematical statement

Fix a finite set-valued function/relation language `L`, a finite
**irreducible** full `L`-structure `B`, and a finite full-functional source
free amalgam

```
                    R
                  /   \
             sL  /     \  sR
                L       M
                 \     /
                iL\   /iR
                    C  =  L *_R M .
```

The source separator `R` is **genuinely function-closed** in both sides,
but may be reducible, multi-generated and have distinct vertices with the
same prescribed part label.

Let `A` be an arbitrary full `L`-structure (it need **not** be
irreducible), and let `T_L,T_R` be two **strict** full-functional trees
of full `B`-copies. Assume:

* `m_L:A↪T_L`, `m_R:A↪T_R` are **full** embeddings, and each image
  is contained in an irreducible constituent copy of `B` in its target
  tree (in particular, this holds for `m_i=b_i∘e_{AB}`, with a full
  `e_{AB}:A↪B` and a constituent-copy embedding `b_i:B↪T_i`);
* `p_L:L→T_L`, `p_R:M→T_R` are original-2019 **partial
  homomorphism-embeddings**; globally they need not be injective nor
  reflect source-undefined function domains;
* **one map** `q:R→A` (not necessarily injective, not asserted to be
  full) satisfies on every *actual source-root vertex* `r`:
  `p_L(s_L(r))=m_L(q(r))` and `p_R(s_R(r))=m_R(q(r))`.

**Claim.** There exists a strict full-functional `B`-tree `T` and an
original-2019 partial homomorphism-embedding `p:C→T`. The map `q`
may identify arbitrarily many source-root vertices; no full
`R↪A`, `R↪B`, or one-generated-root hypothesis is used.

This is strictly different from the verified Track D #619 theorem, whose
root map `R↪B` was itself a **full embedding**.

## 2. Complete English proof

Form the *genuine full-functional* target pushout
`T=T_L *_{A} T_R` using the **two full target maps**
`m_L,m_R`; write `j_L:T_L↪T`, `j_R:T_R↪T`.
These embeddings are full and function-closed because they are the
canonical maps of a full functional free amalgam.

Since each `m_i(A)` lies inside an irreducible constituent of the strict
`B`-tree `T_i`, the strict tree gluing constructor makes `T`
another strict `B`-tree. The gluing root for the **target** is the
fully embedded `A`, **not** the generally nonclosed image `q[R]`
nor the source root itself.

For each actual source root vertex `r∈R`, the displayed target
pushout equation gives

```
j_L(p_L(s_L(r))) = j_L(m_L(q(r)))
                  = j_R(m_R(q(r)))
                  = j_R(p_R(s_R(r))).
```

Therefore the two original-partial side maps `j_L∘p_L` and
`j_R∘p_R` agree on the genuine full source-root embeddings
`s_L,s_R`. The verified `IsFreeAmalgam.exists_EHN_projection`
combines them into one EHN map `p:C→T`, restricting to the two
side maps. Convert the EHN map to the *original-2019 partial*
homomorphism-embedding using the checked semantic equivalence.
This proves the claim.

For functions on a **source-defined** input, complete fibre equality
is retained because the EHN/source-defined partial maps and the full
target embeddings preserve it; a source-undefined mixed input is NOT
required to remain target-undefined. All source function incidences
remain on one free-amalgam side. Thus no false *total-fibre*
homomorphism condition was introduced.

## 3. Stronger historical consequence: an incoming-copy relative extension

Suppose `T_L` is the **already chosen strict target completion of the
previous Picture**, not merely an arbitrary tree, and let
`q_0=m_L∘q:R→T_L`. Under the right-hand marked witness
`(T_R,m_R,p_R)` and its root equation
`p_R∘s_R=m_R∘q`, the very same target pushout
`T_L*_{A}T_R` is a **strict tree extension of Start=T_L**.
Its right-hand map `j_R∘p_R` is an original-partial
homomorphism-embedding of `M` whose restriction to `R` is exactly
the canonical start embedding after `q_0`.

This is the *one-sided relative* witness needed by
`originalPartialTreeExtension_append` and does **not** require an
independent full `R↪B` embedding. It retains the already chosen
left target tree as the actual start of the extension.
The right-hand mark still has to be supplied.

## 4. Adversarial audit: what this does NOT prove

**(a) The marks are a genuine hypothesis.** Absolute strict
completability of `L` and `M` separately does **not** imply that
there are marks `m_L,m_R` and a common map `q` satisfying the
two displayed root equations. The K2/path-parity example in
`docs/fixed-core-root-invariant-counterexample.md` shows that even
a *prescribed* injective pair of opposite K2 endpoints is incompatible
with a two-edge old-copy path. One must allow a *test-dependent*
`q` and prove that the available side completions can use it.

**(b) The local EHN A-atlas is not a marked target witness.**
The checked one-generated source charts and active-input hulls
are each FULL but their images may have false intersections.
Pasting them into one marked target A-copy would wrongly assert
global injectivity or relation/domain reflection. No such pasting
is made here.

**(c) Cross-boundary wrong hits remain important for histories.**
The absolute original-partial theorem permits additional
identifications across the two source sides. To preserve the
`SetRespectsProjectedHistory` or ambient-A-copy **diary** across
further HJ attachments, strengthen the side marks by the already
formalized `ProtectedAMark` condition (both directions, especially
no wrong hits). The verified `protectedAMarkWeakTree_glue`
handles that *separate* history/weak-test endpoint.
The theorem above alone proves neither a protected history nor
a uniform source-rank successor.

**(d) Exact weak set and generator budget.** No original test
`S` is replaced by `cl(S)`; only target objects are enlarged.
A decomposition of a diagnostic input hull does NOT reduce the
generator rank of an entire mixed HJ test. Nullary original partial
domains/defined-empty `Option(Set)` values are not conflated.

**(e) A full rank-increment is not yet proved.** The necessary
remaining **existence lemma** is:

> For every genuinely maximal mixed exact closed test in every
> *ordered* selected Hales–Jewett line-attachment history satisfying
> the genuine rank-`n` predecessors, construct side completions with
> compatible, test-dependent full target A-marks (and protected traces
> when carrying the projected-history invariant).

The proof above establishes the *target gluing and incoming
relative append* once these marks exist, not this existence
claim. Earlier common-parameter-coordinate retractions only cover
restricted line families and cannot deliver full Hales–Jewett Ramsey.

## 5. Alternative resolution of the SURVEY theorem, not this optional lemma

The verified 2019 two-pass **closure-profile** route
(`AllThoseRamseyClasses.Published.coordinated2019_profile_sparse_witness_with_B_coverage`)
does **not** require this native strict-tree rank increment.
It creates relational closure profiles, applies relational strict
sparsening, and runs a second U-closed Picture pass before decoding
genuine partial functions. This is a legitimate alternate route to
the corrected 2019 multiamalgamation conclusion, **not** a proof
of the stronger optional native strict B-tree theorem. Conflate
neither implication with the other.

## 6. Validation plan

After English review, formalize two *additive* named Lean endpoints:
`IsFreeAmalgam.originalPartialTreeCompletion_of_marked_partialSides_noninjective`
and
`HasOriginalPartialTreeExtensionCompletion.of_marked_partial_right_noninjective`,
with `#print axioms` checks on each. The results may be merged only
after exact-head complete Lean and permitted-axiom CI passes.
Retain the open historical marked-witness existence gate in
the research note rather than inserting new manuscript TODOs.
