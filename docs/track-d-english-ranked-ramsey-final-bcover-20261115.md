# Track D — English first: transfer strict BARE rank through final genuine B-cover completion

15 November 2026. This is a separate finalization lemma on fresh main, independent of the pending one-pass control-budget stack (#685, #687, #710). The frozen Nešetřil-programme survey manuscript and collaborator-removed TODOs remain unchanged.

## Theorem

Fix an arbitrary relation/set-valued-function language L (nullary operations allowed), a hereditary free-amalgamation class K of genuine full L-structures, finite A and B in K, a finite control D, and a finite nonempty colour set κ. Let T be a **real EHN Stage over D** (so T belongs to K and has the genuine EHN part map p0:T→D).

Assume the **same T** has BOTH:

 (R) its actual full-language Ramsey arrow T→(B)^A_κ;

 (Q) `AtMostBare(B,T.toStructure,n)` on all EXACT weak n-vertex tests, with strict full-functional B-tree targets.

Then a finite genuine full-functional C exists with ALL of the following simultaneously:

 1. K(C);
 2. the actual full-functional Ramsey arrow C→(B)^A_κ;
 3. an EHN global projection C→D, hence a genuine **original-2019 source-defined partial** homomorphism-embedding C→D, without requiring domain reflection;
 4. `AtMostBare(B,C,n)` on every exact weak n-vertex test;
 5. `LooseTreeAmalgam(B,C)` and **internal** `IrreduciblesExtendTo(B,C)` (not merely external projected B-cover);
 6. for every literal finite FULL function-closed S⊆C with |S|≤n, a strict full-functional B-tree completion of C|S through a genuine original-2019 partial homomorphism-embedding on that same S.

B need not be assumed irreducible for this transfer theorem. There is no PositiveFuncArity hypothesis and no closure of the weak test or its projected image. It is a **conditional finishing transfer**, not an unconditional n-pass native sparsening result.

## Complete argument (all results already separately Lean-verified)

Apply the existing `Structure.sparseningRamsey_functional_looseFullTrees_inClass` to **T as Ramsey control**, not D. This yields C∈K with full Ramsey arrow, an EHN map q:C→T, a genuine loose full-functional B-tree witness, and internal extension of every irreducible substructure to a genuine full B-copy **inside the same C**.

Apply the merged rank-pullback `SetAmbientRelativeWeakTreeWitness.AtMostBare.pullback_ehn` (#695) to the actual EHN q and the input Q(T). This gives Q(C) at the **same n**: for each exact weak test S⊆C, the rank bound is applied to q[S]⊆T, of size no more than |S|. The strict full-functional target B-tree obtained for q[S] is unchanged, and the actual ambient-relative weak map pulls back. Thus the loose B-tree used to produce C does not replace or weaken its *local strict* targets.

Compose q:C→T and T.part:T→D, both EHN, to obtain an EHN map C→D; convert it to the original-2019 partial-function semantics using the already certified `toOriginalPartial`. Undefined source operations need NOT reflect target undefinedness; source-defined complete multivalued fibres are transported exactly.

Finally apply merged `AtMostBare.closedTest_originalPartialCompletion` (#703) to each literal function-closed S of ≤n vertices to obtain the advertised strict functional completion. All hypotheses use the actual same C. No spurious separate-witness conjunction is made.

## Exact mathematical boundary

This closes **final B-copy coverage**, the **final conditional Ramsey arrow**, the global original-partial projection, and the strict closed-test endpoint, provided a suitable ranked Ramsey Stage T has first been constructed. The currently proposed one-pass theorem #710 is intended to supply such a T only under the **independent** input control bound `AtMostBare(B,D,F_A(m))`; this final lemma does not manufacture that input and does NOT make the outer forward induction noncircular.

The theorem also intentionally distinguishes strict local completion (on an auxiliary genuine strict B-tree) from the fact that C ITSELF is only a loose full-functional B-tree. No false claim of a strict decomposition of all of C is needed.

## Acceptance

Add `Structure.sparseningRamsey_bareRank_withBCover_of_stage` and one direct named `#print axioms` check. Full exact-head Lean compilation, standard logical axioms only, no admissions. Do not edit manuscript black text, existing TODOs, or validation markers.
