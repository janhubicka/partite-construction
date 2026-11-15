# Track D — English first: one conditional strict full-functional endgame with internal B-coverage

15 November 2026. This proof packages two **independently stated** Track D obligations (#710 and #711) into an explicit final conditional theorem. It is STACKED on #710, with the final-transfer source from independent #711 supplied identically on this integration branch. Neither parent is yet claimed kernel-verified. The frozen Nešetřil programme survey prose, existing TODOs, and markers are untouched.

## Theorem (precise, conditional)

Let K be a hereditary full free-amalgamation class in an arbitrary relation/set-valued-function language L, INCLUDING nullary functions. Let A, B∈K be finite **irreducible** genuine full structures with a full embedding e:A↪B. Fix finite genuine control D, nonempty finite colour type κ, and a full-functional Ramsey arrow D→(B)^A_κ. Let m≥0 and

    F_A(m) = m + |A|(m+1)^|A|.

**Independent extra input**: D has strict bare full-functional weak locality at rank F_A(m), i.e. `AtMostBare(B,D,F_A(m))`.

Then one finite genuine full-functional C exists with ALL clauses simultaneously:

1. K(C);
2. the real full-functional Ramsey arrow C→(B)^A_κ;
3. a genuine **original-2019 source-defined partial** homomorphism-embedding p:C→D, not a false total-fibre global projection;
4. `AtMostBare(B,C,m+1)` for **literal** weak vertex tests of cardinality ≤m+1, with genuine strict full-functional B-tree targets;
5. internal `IrreduciblesExtendTo(B,C)`, not merely external/projected coverage;
6. genuine full-functional `LooseTreeAmalgam(B,C)`;
7. for every literally full function-closed S⊆C of size ≤m+1, a **strict** full-functional original-2019 partial B-tree completion of the full induced C|S on exactly those vertices.

The final C need not itself have a strict B-tree decomposition; it is loose. The strictness requirement concerns each finite local target, and is preserved.

## Proof

By the proposed conditional all-arity complete native EHN Ramsey-pass theorem `EHN.inducedConstruction_allArity_bareRank_of_controlBudget` in stacked PR #710, apply the **joint** arrow-and-high-rank hypothesis on the SAME original control D. It produces a REAL EHN Stage T over D with its own full-functional Ramsey arrow `Arrow A B T` and bare rank m+1, simultaneously.

Now invoke the independent finalization theorem `Structure.sparseningRamsey_bareRank_withBCover_of_stage` in PR #711 with exactly THIS T. It performs the verified loose-tree/internal-B-cover completion, obtaining a single final C with the full Ramsey arrow and EHN q:C→T. Its exact EHN pullback preserves strict bare rank m+1; the composite EHN map C→T→D is a genuine original-2019 partial map; its internal B-copies are present in C. On every literal closed S≤m+1, the merged strict bare→original-partial closed-test theorem supplies the strict full-functional B-tree target.

No new HJ construction, mixed-root gluing, finite trace restoration, or Ramsey argument is repeated. Every output is a **single existential witness** C, not a conjunction assembled from unrelated witnesses.

## Three critical nonclaims

* The control D already has a high strict rank **independently** of its Ramsey arrow. The result does NOT construct that D, and does NOT solve the full n-pass induction. A forward predecessor of rank m cannot be substituted for rank F_A(m). A finite reverse numeric budget without an independently provided ranked Ramsey starting control is circular.
* A is **irreducible** as required by the current mixed-source rank successor; do not infer arbitrary-A scope from this conditional result. When no embedding A↪B exists, a separate unconditional one-copy branch is in draft PR #717.
* The global map is in the **original 2019 source-defined partial-function** sense; undefined inputs can become defined in the control. It is not a total-fibre-surjective homomorphism-embedding, known false in general. No test or projected image is closed to hide a rank increase.

## Validation gate

Lean theorem `Structure.sparseningRamsey_bareStrict_withBCover_of_controlBudget`, direct named root `#print axioms`. Both parent candidate proofs #710 and #711, the actual stacked branch head, complete Lean build, no-admissions audit and standard logical axiom gate must all pass before this conclusion can be marked green.
