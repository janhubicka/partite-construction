# Track D — English proof first: restore all ambient A-traces by a uniform weak-test rank blow-up

**14 November 2026.** This is a native full relation/set-valued-function
analogue of the already Lean-validated relational trace selector in
`Iterated/ProjectedPartialRestoration.lean`. The numbered
Nešetřil-programme survey and previously removed TODOs remain frozen.

## 1. Precise quantitative theorem

Let A be a finite FULL irreducible native functional structure,
Base any finite genuine full-functional target, and C a finite
native source. Say `AtMostBare(Base,C,k)` if EVERY exact weak
subset J⊆C with |J|≤k has a STRICT full-functional Base-tree
target T and an `IsAmbientRelativeWeakHE C J T g`: positive
relations and ALL retained multivalued function outputs survive;
complete ambient nonempty fibres are preserved when wholly
contained in J; every FULL irreducible ambient source copy
inside J is represented by a FULL target embedding.

This deliberately omits protection of arbitrary full ambient
A-copies which meet J only in a proper subset, as well as any
projected history.

Put

    F_A(n) = n + (n+1)^|A| |A|.

**Claim.** If C has `AtMostBare(Base,C,F_A(n))`, then for
ANY part-label map p:C→P it has the existing
`SetAmbientRelativeWeakTreeWitness.AtMostNoHistory(A,Base,C,p,n)`,
including FULL target A-copy marks for EVERY actual full
ambient A↪C intersecting EACH exact weak S of at most n
vertices. No function-closure or weak test rank cheating occurs.

## 2. Complete English proof

Fix literal finite S⊆C with |S|≤n. For each genuine FULL
embedding beta:A↪C, record the EXACT labeled trace

    t_beta : A→Option(S),
    t_beta(a) = some(beta(a)) if beta(a)∈S,
                none         otherwise.

There are at most `(|S|+1)^|A|` such traces (including
the empty trace). Use the existing verified
`FiniteTrace.selectIndices` lemma to choose one FULL
embedding beta_t for every trace realized by some beta.
Enlarge S ONLY for requesting the auxiliary witness:

    J = S ∪ ⋃_t beta_t[A].

Then

    |J| ≤ |S| + |A| (|S|+1)^|A| ≤ F_A(n).

Choose the AtMostBare witness `g:J→T` for this J.
The target is a strict FULL-functional Base-tree. Restrict
`g` to the literal S using the already verified native
`IsAmbientRelativeWeakHE.restrict_subset` lemma. It remains
a complete ambient-relative weak HE on S: no new source
vertices were introduced into the conclusion.

Now fix any actual FULL beta:A↪C. Its trace matches the
chosen representative beta_t. Since the ENTIRE image
beta_t[A] lies in J, the `IsAmbientRelativeWeakHE`
irreducible-test clause (A irreducible) supplies a FULL
embedding `e_t:A↪T` with

    e_t(a)=g(beta_t(a))   for EVERY a∈A.

For every a with beta(a)∈S, equality of the labeled
traces implies beta_t(a)=beta(a), as actual source
vertices, not just equal part labels or isomorphism
types. Consequently

    e_t(a)=g(beta_t(a))=g(beta(a)),

which is precisely the full ambient A-copy certificate
for the restricted target map S→T. Because A itself is
irreducible, `e_t.ContainedInIrreducible` can be
witnessed by the FULL target embedding e_t of A into T.
No target re-gluing or closure of the weak partial trace
is necessary. Finally projected history is the empty
list, so its requirement is vacuous.

The construction works for arbitrary genuine set-valued
function arities, repeated inputs and nullary symbols,
including source-undefined/nonempty-fibre asymmetry:
we use only the verified exact ambient-relative weak
map and its restriction lemma. The original-2019
nonempty-source-defined semantics is not replaced by
`Option(Set)` defined-empty semantics.

## 3. Adversarial caveat: NOT yet a valid native n-pass induction

The theorem proves a rigorous **quantitative conversion**
from a strong BARE completion bound to a weaker marked
completion bound. It does NOT say that the rank-m
control predecessor automatically provides rank-F_A(m)
bare completions. In fact F_A(m)>m for nonempty A.

The checked Track D mixed successor #642 consumes a
marked rank-m control predecessor to create rank-(m+1)
mixed completions; applying the present restoration
to the resulting rank-(m+1) *bare* property would
require a much larger rank, and is therefore NOT
licensed. Any attempt to iterate this quantitative
restoration must specify a NONCIRCULAR way to pay
the enlarged control budget (possibly the verified
two-pass closure-profile route), or replace the
induction invariant again. Do not claim the native
unrestricted HJ multi-line iteration is proved.

The result does, however, demonstrate that **partial
A-trace protection is a finite-type condition with
an explicit, structure-size-independent quantitative
cost**. This can help any future alternate induction,
and may permit finite rank scheduling over a separate
already-available family of large local tree bounds.

## 4. Lean validation

Re-use the exact verified `FiniteTrace.selectIndices`
API and the already checked
`RelStructure.projectedPartialRestorationBudget`.
Add:
* `SetAmbientRelativeWeakTreeWitness.AtMostBare`;
* `AtMostBare.restore_full_ambient_A_traces`:
  finite rank blow-up yields AtMostNoHistory.

The proof must use FULL native
`Structure.Embedding` (not merely weak embeddings),
`IsAmbientRelativeWeakHE.restrict_subset`,
and the actual ambient irreducible-copy clause.
One named root `#print axioms` check for the theorem.
Only merge after exact-head complete Lean/standard axiom
CI and source/no-admissions audit.
