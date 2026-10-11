# Closed-substructure repair — coordinated weak-rank invariants checkpoint (11 October 2026)

This note accompanies the clean cumulative Lean patch integrating independently
checked PRs #229, #231, #232 and #233. The published TeX and literal 2019
predicates are frozen. The working predicates protect **embedded closed
U-irreducible** tests; the actual weak-substructure local condition always
tests the **exact induced vertex carrier**.

## Four positive results, with distinct proof scopes

1. **Minimum generating support.** If S is a minimum U-generating
   support of a finite (even nonclosed) T, then USize(T|S)=|S|;
   hence T|S is closure-independent. This does NOT extend a
   K-completion of the weak S to the actual prescribed closed
   generated hull T. A two-vertex Bad-predicate obstruction
   demonstrates this limitation.

2. **Common-coordinate native Hales–Jewett branch.** For a chosen
   native line subfamily with one shared variable coordinate k,
   coordinate evaluation on the core and identity on attached
   old copies give an **ordinary relational homomorphism-embedding**
   of the actual attachment to Old, with no closed-support,
   closed-target or globally semi-closed-attachment hypothesis.
   Every maximal-U-rank exact weak test of at most n vertices
   embedded in that subattachment has a corrected K-completion,
   provided the old U-closed picture has K-completions of ALL
   its closed rank-at-most-n induced tests. The intermediate
   exact weak-image completion assumption is discharged via
   the ambient closed hull, using the proper inequality
   USize(hull(weak S)) <= |S|.

3. **Maximal weak rank and two different ordinary side maps.**
   Every weak substructure fully embedded in a maximal-rank
   finite weak source itself has maximal rank; an ordinary
   homomorphism-embedding from either source side therefore
   protects all embedded closed irreducible tests. Thus
   two different ordinary side maps to one U-closed Old
   suffice to use the independently verified two-side
   completion/gluing lemma, IF their source root factors
   through one generated closed K-boundary with two
   embeddings into Old.

4. **Generate the common K-boundary instead of assuming it.**
   Suppose the source root part map q:Root->A and two
   possibly different full embeddings aL,aR:A->Old are given,
   where A is U-closed and A∈K. Set Q to the induced
   U-closure of q[Root] inside A. The preexisting closed-U
   hereditariness gives Q∈K, and the root's image generates Q.
   The two A-embeddings restrict to Q-embeddings, so the
   generated-boundary hypothesis of item (3) is automatic.
   Importantly, Root itself is allowed to be reducible,
   nonclosed and noninjectively mapped to Q.

5. **Combined ordinary sides with a canonical A-boundary.**
   The theorem `HasClosedUKCompletion.of_maximal_weak_two_ordinary_side_maps_via_A`
   packages items (3) and (4). Under maximal weak U-rank,
   small proper free sides, two ordinary side homomorphism-embeddings
   into the SAME closed Old picture, and compatibility of their
   root images through two embeddings of one closed A∈K, it
   produces a corrected K-completion. Both protection of the
   side maps and the common closed K boundary are DERIVED,
   not independent assumptions. Existence of the two side maps
   and their root factorization remains a genuine
   native-history obligation.

## Remaining proof boundary

These results do not assert a single coordinate variable on ALL
native HJ lines; the full Ramsey family generally has none.
Nor do the pairwise transverse-line lemmas (#207, #223) imply
one single A-word contains an arbitrary multi-line separator
(counterexample in merged #210).

The unresolved **real-history lemma** must take any closed test
of U-size j+1 in the final U-closed repaired Picture,
trace its finite generating set through the selected native
line histories, and either find a rank-j completion via a
coordinate/collision or decompose the *prescribed closed
test* into safely completed source pieces with compatible
A-root projections. Merely completing the exact weak
j+1-vertex generating set is insufficient: it may disregard
closure tuples prescribed on vertices outside the support.

This clean combined branch adds seven new Lean modules and eleven
individually audited declarations without changing any earlier
axiom checks. The source was successfully elaborated on earlier
branches separately. **Do not certify the combined branch
until its own complete CI and permitted-axiom audit pass.**

The full repaired Theorem 2.18 remains open.
