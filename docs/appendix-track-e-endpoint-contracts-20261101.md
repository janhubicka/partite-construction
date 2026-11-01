# Appendix A — Track E exact endpoint audit (1 November 2026)

**Scope:** independent endpoint source, not a replacement for the frozen manuscript or an unconditional functional sparsening proof. The only Lean implementation edits in this branch are new `Functional/TrackEStatementAudit.lean` and its new root-level axiom audit. The frozen survey prose and author-maintained TODO markers are untouched.

**Baseline:** main `0959f4d5b857059937a236c77d8cef67cfcdf4e1`; survey adversarial split [#140](https://github.com/janhubicka/Ne-et-il-s-classification-programme-of-Ramsey-classes/pull/140). Every `CheckAxioms*.lean` is included by `.github/workflows/lean.yml`. A proof requires CI on the precise HEAD, not just presence of a file.

## Statement comparison: no weakening by swapping the witness or tested set

| Comparison | Lean endpoint on the SAME objects | Direction and exact qualification |
|---|---|---|
| Survey full total-fibre projection `C.IsHomomorphismEmbedding D p` vs. genuine 2019 source-defined `IsOriginalPartialHomomorphismEmbedding C D p` | `totalHE_implies_originalPartialHE`; `totalHE_iff_originalPartialHE_and_domainReflection` | Full implies source-defined. Reverse needs nonempty-domain reflection on EVERY tuple of the identical C and p; no implicit domain equivalence. |
| Strict relational B-graph tree vs. strict full-function B-tree | `closedWhole_graphTree_not_fullFunctionTree` reuses `FunctionalClosedTestGraphObstruction.closedSource_graphCompletion_not_fullCompletion` | Graph tree is insufficient even for a function-closed entire source. Do not promote the verified graph local theorem. Positive graph-to-functional decoding uses actual function-closed graph root maps (`RelStructure.FunctionClosedTreeAmalgam.toFunctional`), not arbitrary graph targets. |
| Internal `IrreduciblesExtendTo B C` vs. external `ProjectsIrreduciblesInto B C D p` | `internalCover_implies_projectedCover_of_baseIrreducible`; `projectedCover_doesNot_imply_internalCover` | Internal + B irreducible + EHN p gives external for the **same C and p**. External alone does not put any B-copy inside C; simple finite C=one point, B=D=two points witnesses failure. |
| `K C` / `H C` vs. each exact weak S having a target in H | `HasExactWeakHCompletions`; `exactWeakHCompletions_of_weakHereditary` | If H is actually hereditary for the precise **weakInduce** semantics, H C implies this local property, with target the exact weak structure. Ordinary closed heredity is NOT weak heredity. The reverse is not asserted. Crucially, the upstream 2019 H certificates are **ambient relative OLD tagged completions**, *not* this intrinsic full weak HE. |

## Nonvacuous regression examples

- `oneCopy_internal_and_external`: actual one-copy B structure with full identity projection, internal and external coverage.
- `projectedCover_doesNot_imply_internalCover`: actual finite two-vertex vs. one-vertex binary first-projection structures; a B-copy in D need not exist in C.
- `closedWhole_graphTree_not_fullFunctionTree`: actual function-closed unary path of length two, a strict tree in its graph reduct, impossible in strict full-function B-trees.
- `literal_publishedTriple_false_atEveryRank`: the positive-arity, irreducible A/B, nonvacuous arrow `Fin 3 → (Fin 2)^(Fin 1)_2` of `PublishedTotalBinaryObstruction`; `PublishedSparseningConclusion` fails **for every n**, from clauses (1)+(3), not just rank-three locality.

## Actual endgame: quantified clause ledger

1. The printed predicate `PublishedSparseningConclusion A B D κ n` first **exists** one finite C with `Arrow A B C κ`, then **exists** a single `p:C→D`, with FULL `IsHomomorphismEmbedding`, and requires BOTH strict full-function local completions on **every closed S of size <=n** and internal `IrreduciblesExtendTo B C`. This literal target is refuted, not merely unproved.
2. The verified native `sparseningRamsey_nativeFunctional_graphStrict_withBCover` exists one finite C with arrow, genuine original-partial global p, strict `LocallyTreeLike A.graph B.graph C.graph n`, and internal B extension in that SAME C. It also has a loose full-functional B-tree structure. It assumes positive arity, the free-amalgamation class K, graph-hereditary irreducibility of A and n>0. It does **not** assert strict full-functional local completions.
3. The all-arity `sparseningRamsey_functional_looseFullTrees_inClass` has a full function-language Ramsey arrow, EHN p, internal coverage and a full FUNCTION loose B-tree C, with local closed tests embedding into that same loose C. **Loose** (arbitrary closed root) is not the printed strict tree.
4. Upstream `AllThoseRamseyClasses.Published.genuinePartite2019_actual_sparse_witness_with_H_completions` returns an actual part-preserving original partial-function Ramsey arrow, a source-defined projection, and for every exact small weak S, `HasGenuinePartiteTagged2019RelativeCompletion H (C.induce S)`. Targets of those *ambient-relational* tests are genuine H-structures, but the final C need not belong to H. This is not a same-target full intrinsic `weakInduce` embedding.
5. Upstream `genuinePartite2019_ramsey_of_original_class_data` produces class Ramseyness **conditionally**, assuming `hLocal`: for each K-member B and ambient R control C0 there is a uniform n with OLD-relative local completion for the required tests. Neither graph-tree completion nor external B coverage discharges this quantifier.

## Open/unasserted arrows

- Original intrinsic weak/local-finiteness `→` OLD ambient-relative H-class local axiom remains Track C (not assumed by this audit).
- Strict full-functional mixed reducible-root local B-trees on actual native Picture remain Track D.
- `C ∈ H` from only bounded exact weak H-completion certificates requires an additional class-level local-completion/strong-amalgamation transfer; it does not follow definitionally. Likewise `H C` plus only **closed** heredity cannot justify all intrinsic weak S.
- Converting full functional strict trees to an arbitrary *relational strict tree encoding* needs a proper target root-closure / irreducibility comparison; no unsupported blanket equivalence is claimed.

## Integration gate

Run full repository build and `CheckAxiomsTrackEStatementAudit.lean` on exact PR HEAD; inspect `#print axioms` results and zero `sorryAx`. The audit is not a replacement for Track F's manuscript marker reconciliation. **No survey prose or author-removed TODOs have been altered.**
