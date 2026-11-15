# Track D independent adversarial audit — the control-budget dependency

15 November 2026. This note audits the *actual theorem signature* of `inducedConstruction_allArity_bareRank_of_controlBudget` in PR #710, not merely its PR description. The survey's frozen text and validation markers are unchanged.

## Certified scope versus open theorem

The proposed theorem assumes both `Structure.Arrow A Base D κ` and `AtMostBare Base D (F_A(m))`, where
`F_A(m) = m + |A|(m+1)^|A|`. Its conclusion is `∃ Stage K D, AtMostBare Base T (m+1) ∧ Arrow A Base T κ`. This is a **conditional one-pass transfer** of the *joint* arrow/locality invariant. It does not establish the existence of its input control D or any unconditional rank increment.

The exact Lean source uses `inducedConstruction_preserving`, `initial_allArity_tree`, and `pictureLemma_lines_preservingBareRank_of_controlBudget`. The last is stacked on draft #687/#685; its axiom and exact-head CI status must not be inherited from merged helper results. At inspection #710 and #687 exact-head Lean runs were queued; #685 was in progress, none passed.

## Formal dependency obstruction

Write R_k(D) for `AtMostBare Base D k` and P(D) for the actual full Ramsey arrow. The new operation has type

  P(D) & R_{F_A(m)}(D)  ==>  exists T, P(T) & R_{m+1}(T).

Monotonicity of R (large rank implies small rank) goes **downward** in k, never upward. Thus an available predecessor P(D)&R_m(D) cannot be used to invoke this operation when A is nonempty, since F_A(m)>m. In particular, no finite repetition of this operation alone bootstraps from an arbitrary Ramsey control or from rank zero. Reversing a finite rank schedule merely moves the unprovided joint premise to the first (highest-rank) control.

Even relative to the *desired output* rank, F_A(m) >= m+1 when |A|>=1, with equality only for |A|=1,m=0. All genuinely nontrivial steps require strictly more rank on the input than on the output. This is a theorem-dependency obstruction, **not** a counterexample to existence of arbitrary finite rank Ramsey witnesses.

## Concrete conceptual test

In the ordinary simple-graph language with Base=K2 and A=K1, an arrow D -> (K2)^(K1)_κ means every κ-vertex-colouring of D has a monochromatic edge (chromatic number >|κ|). A bare local tree completion at larger rank imposes additional local structure; the arrow alone does not imply such a bound. For example a sufficiently large complete graph is a valid arrow control but its whole triangle cannot admit a source-induced homomorphism-embedding into a tree amalgam of edges. This illustrates why the arrow condition cannot silently discharge the high-rank control premise; it does **not** exclude the existence of other, high-girth/high-chromatic controls.

## Two logically distinct continuation routes

(1) Prove an independent joint-control existence theorem `∃ D, P(D) ∧ R_N(D)` for every prescribed N. This is essentially a sparse Ramsey control theorem and must be proved **without invoking the same conditional step in a circle**. The corrected two-pass closure-profile construction may be used as an independent source only if a further theorem genuinely upgrades its completion witnesses to *strict Base-trees* on exact weak tests; ordinary H-valued completions alone do not do so.

(2) Strengthen the attachment/picture invariant so the mixed case is handled by rank m rather than F_A(m), e.g. preserve externally marked A-copy traces *as part of the inductive invariant* instead of rebuilding them through the finite-trace budget. The previous marked-history obstruction (colliding roots and wrong hits at unoccupied marks) must then be solved with an actual coherent extension theorem; a bare rank-m predecessor is insufficient.

The graph-tree and two-pass relational/functional results must not be relabelled as (1) or (2) without a literal theorem-type and construction audit.

## Exact remaining gates

- Compile and axiom-audit the exact stacked heads #685 -> #687 -> #710.
- Confirm that `Stage K D` gives precisely the global original-2019 *source-defined* partial EHN semantics required by the printed corrected statement (not total-fibre surjectivity or domain reflection).
- If final irreducible Base-copy coverage is part of the target, prove it for the same final stage, rather than inferring it from the arrow.
- Do not upgrade survey Track D to green until either the independent joint-control input or an unconditional noncircular rank successor is proved.

No mathematical manuscript prose or author-removed TODOs were modified.
