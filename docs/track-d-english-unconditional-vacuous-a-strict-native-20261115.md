# Track D — English first: unconditional strict native no-A-copy case (15 November 2026)

This resolves the logically vacuous branch of the genuine full-functional strict sparsening problem, rather than adding a new conditional rank-budget hypothesis. The frozen Nešetřil programme survey and author-removed TODOs are untouched.

## Exact statement

Work in any relation/set-valued-function language, with **all arities including nullary operations**. Let K be a hereditary free-amalgamation class (the proof actually only uses B ∈ K). Let A,B,D be finite genuine full structures, with B∈K, κ a finite nonempty colour type, and an ordinary full-function Ramsey arrow D -> (B)^A_κ.

Assume there is **no full embedding A -> B**. For every n≥0, take C=B. Then the SAME C has:

1. class membership K(C);
2. the ordinary full-function Ramsey arrow C -> (B)^A_κ (vacuous);
3. a global genuine original-2019 source-defined partial homomorphism-embedding C -> D (indeed a full embedding);
4. `AtMostBare(B,C,n)` for **all** n, using the single-copy strict full-functional B-tree C itself and the identity restricted to each literal weak test;
5. a genuine loose B-tree (even strict) and internal `IrreduciblesExtendTo(B,C)`;
6. on every literally full function-closed S⊆C with |S|≤n, strict full-functional original-2019 partial B-tree completion.

No irreducibility hypothesis on A or B, positive arity hypothesis, or extra control rank is needed.

## Proof

Apply D -> (B)^A_κ to the constant colouring. It produces a **full functional embedding** β:B↪D; since A does not embed into B, the monochromaticity condition of a B-copy in any target is empty. Therefore the identity B→B witnesses the Ramsey arrow on C=B.

The full β is a fortiori EHN and therefore a genuine original-2019 source-defined partial homomorphism-embedding B→D. This map may be used directly as the original projection; no undefined-input reflection is required (though the full embedding has it).

The genuine strict full-functional tree `TreeAmalgam B V B` is the one-copy constructor on identity. Thus by the exact merged `AtMostBare.of_strictTree` (Track D #695), every literal weak test of C has a strict target B with an ambient-relative weak HE. The usual verified `LooseTreeAmalgam.ofTree` and `LooseTreeAmalgam.irreduciblesExtendTo` give internal B-coverage of all irreducibles of C, regardless of whether B itself is irreducible. Finally merged `AtMostBare.closedTest_originalPartialCompletion` (#703) gives the genuine original-2019 strict completion of every closed S on **exactly** those vertices.

This is not a false deduction of a full projection from an EHN projection: β is already a genuine full embedding by the Ramsey arrow.

## Why this matters

The optional hard strict-native iteration can now be restricted to the nonvacuous case A↪B. This is a mathematically honest branch elimination. In the nonvacuous branch, Track D's mixed-rank successor additionally assumes A irreducible and a high-rank control `AtMostBare(B,D,F_A(m))`, whose independent existence remains the central open issue. This lemma does not solve that issue.

## Validation gate

Lean theorem `Structure.sparseningRamsey_bareStrict_noACopy`, one root `#print axioms`, exact-head full build and only standard logical axioms. Do not promote to validated or merge until checked.
