# Native partite mixed rank: actual escaping control outputs on one source side

**18 October 2026 — English proof and adversarial audit before Lean.**

The previous fully verified functional rank-reduction theorem isolates
maximal projected tests with a nonclosed occupied selected A-boundary.
The independently verified occupied-A criterion converts this
nonclosedness into an EXPLICIT functional control-output witness.
The present lemma carries out that reduction on one ACTUAL native
functional partite stage (not an artificial U-closed relational stage).

## Setup and exact side tests

Let T be an actual genuine transversal \`System L P C\` with its
original-2019/EHN part projection p=T.part to a functional control D.
Assume its underlying function structure T.toStructure is a FULL free
amalgam of functional sides L and R over their FULL closed common
root; alpha:A↪D contains the actual projected common root.
Assume A irreducible, A↪B full, B irreducible, and D has the strict
rank-m ambient-A weak-history predecessor property.

For any exact finite mixed S⊆C, |S|≤m+1, let

    SideL = S ∩ range(iL),  SideR = S ∩ range(iR).

These are EXPLICIT subsets of the SAME actual native structure,
not closures of S. The exact projected side images satisfy

    p[SideL] = (p∘iL)[iL^{-1}S],
    p[SideR] = (p∘iR)[iR^{-1}S].

This uses only injectivity of the full side embeddings and the
ordinary definition of preimage, not p injectivity or any
set-valued operation assumption.

## The theorem

One of the following holds:

1. The exact S has a STRICT full-functional B-tree weak completion,
   protecting actual full ambient A-copy intersections and every
   requested finite projected history; or
2. |p[S]|=m+1 and, for one concrete side X=SideL or SideR,
   there exist F, an actual input tuple x of vertices of X, and
   an output part q such that
   * p(x_i)∈alpha(A) for every input i;
   * q∈F_D(p(x));
   * q∉p[X].

The proof applies the already checked sharp mixed rank theorem
(PR #417). If it returns a strict witness, we are done. Otherwise
it returns maximal projected rank and nonclosedness of one
occupied A-boundary. Use the displayed equality of exact side
projections to apply the checked
\`System.exposed_of_not_occupiedAlphaClosed\` criterion (PR #416)
to that same side subset inside the ACTUAL system T.

The second case supplies a FINITE, CONCRETE control function-root
obligation that any attempted completion of the remaining hard case
must resolve. No artificially generated vertex is inserted in S,
the projected image, or a predecessor rank test.

## Adversarial checks

1. **An exposed q need not escape p[S] globally.** It lies
   outside the selected SIDE projected set p[SideX] and may
   already be represented by a tested vertex of the OTHER side.
   We deliberately assert only the correct side-relative fact.
2. **The source operation may be undefined or its output may have
   been omitted by the weak restriction.** These two cases are
   distinguished by the separately verified EHN phantom/omitted
   dichotomy; no total-fibre reflection is smuggled in.
3. **Full side maps are essential for the actual attachment
   geometry and protected irreducible histories.** The projection
   p itself may identify vertices outside S.
4. **Multivalued output functions remain transversal.** The
   theorem uses genuine native \`System\` sources and strict full
   functional B-tree targets; equality of a single nonempty-domain
   bit is never mistaken for equality of all output-part masks.
5. **No weak set is treated as a full gluing root.** The target
   common-root compatibility and strict tree existence for exposed
   slots remain open. In particular the K2 parity and
   arbitrary-stage C5 counterexamples prohibit generic fixed
   A-marks or an unrestricted maximal-stage completion oracle.
6. **Nullaries and repeated inputs** are treated literally
   by the underlying set-valued function interpretation.
   No unwarranted empty common-root assumption.

## Validation boundary

This is a genuine positive case reduction in the native language,
not the final full functional iteration. Its second alternative is
precisely the history-dependent missing-output profile existence
problem to attack next. Only the explicitly stated disjunctive
theorem may receive a green marker after full CI/axiom verification.
