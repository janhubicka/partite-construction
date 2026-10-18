# Nonclosed occupied A-boundaries are exactly escaping control-output obligations

**18 October 2026 — English proof and adversarial audit before Lean.**

We continue the published-order native functional iterated partite
construction, retaining the already-verified recursive control D,
genuine transversal set-valued functions, exact weak vertex subsets
and the original-2019 source-defined EHN projection convention.

The verified mixed rank-(m+1) theorem applies when the two projected
occupied pieces of the selected A-copy are FUNCTION-CLOSED. We now
give an exact positive/negative criterion for that hypothesis.

## The exact equivalence

Let alpha:A→D be a FULL functional embedding of an arbitrary A
into the functional control D. Let B be a genuine functional
partite System over the carrier of D, with part map p:B→D
(not necessarily total-fibre or even EHN for the first equivalence).
For an exact weak subset S⊆B, put

    I = p[S],
    H = {a∈A : alpha(a)∈I}.

An **exposed control-output obligation** is a symbol F, an input
tuple x in the EXACT weak S, and an output label q such that

1. every projected input p(x_i) belongs to alpha(A);
2. q is a value of F_D(p(x));
3. q does NOT belong to I.

No source-definedness assumption is made. Because q∉I, the weak
restriction B|ᵂS necessarily has no function output of part q,
so the data is also precisely a witnessed
\`B.ControlMissingAtPart D S F x q\` with q escaping the projected
weak set. Fullness of alpha ensures q∈alpha(A) automatically.

**Theorem:**

    H is function-closed in A
        iff
    no exposed control-output obligation exists over S.

### Proof

Suppose H is not closed. There are a symbol F, arguments
a_i∈H, and an A-value b∈F_A(a) with b∉H. Since a_i∈H,
choose actual weak source vertices x_i∈S with
p(x_i)=alpha(a_i). Set q=alpha(b). By FULL function
preservation along alpha, q∈F_D(p(x)). Since b∉H,
q∉p[S]. Thus (F,x,q) is an exposed obligation.
No closure hull or new source vertex was used: the
input tuple consists of independently chosen actual
vertices from the exact weak set.

Conversely, let (F,x,q) be exposed. For each i choose
a_i∈A with alpha(a_i)=p(x_i). Fullness of alpha gives

    F_D(alpha(a)) = alpha[F_A(a)].

Hence q=alpha(b) for some b∈F_A(a). All a_i are in H,
but q∉p[S] means b∉H. Thus H is not closed.

This establishes an exact bridge between weak projected
subsets and the closure roots of the corrected U-closed
description, without replaying the relational construction.

## Consequence for a genuinely CLOSED finite source test

Now additionally assume B is EHN-partite over D and the
finite weak S is itself function-closed in B. By the
control phantom-versus-omitted dichotomy, an exposed q
cannot be a lost output of a source-defined tuple:
every actual source output on S inputs would remain in S.
Thus the source tuple is entirely UNDEFINED while the
functional control has a q-output. The verified
\`System.controlMissing_closedFiniteTest_decompose\` gives
a proper FULL functional free decomposition of the entire
closed induced test B|S. Both pieces and the common root
have STRICTLY fewer vertices than S.

In particular, if this closed induced test is irreducible
then H MUST be function-closed. The equivalent contrapositive
makes explicit the source of difficulty in an induction on
weak tests: intermediate weak S need not be closed, and
the maximal mixed rank case can have both source-omitted
and source-undefined control outputs.

## Adversarial checks

* **Full alpha embedding is necessary.** A weak map
  A→D need not reflect D-output values into A, and the
  reverse implication would fail.
* **No EHN assumption needed for the equivalence.**
  It is a statement about the control D, alpha, and exact
  projected weak set, not source-domain reflection.
  EHN is only required for the *reducibility corollary*.
* **Repeated inputs and nullaries:** choosing source lifts
  independently is allowed; a repeated A argument may be
  represented by any member of its part. An empty input
  tuple has its unique lift and exposes a missing nullary
  output exactly when H fails to contain it.
* **Distinct outputs:** multivalued set-valued functions
  are handled directly by full alpha.map_func. Native
  transversal per-output-part uniqueness is preserved,
  but unnecessary for this equivalence.
* **Weak subsets and budgets:** absolutely no closure
  of S or p[S] is taken. The output q is an existing
  control vertex outside p[S], NOT a new tested vertex
  paid for by the predecessor rank.
* **False upgrade to a rank step:** the rank-split
  corollary applies ONLY when S is closed. Intermediate
  weak mixed side cuts usually are NOT closed. Exposed
  obligations in those cuts therefore do NOT by
  themselves yield compatible target B-tree completions.
* **Known obstructions remain:** the K2 parity example
  rules out a globally fixed alpha-mark even in the
  purely relational language; the arbitrary-stage C5
  example rules out unqualified target-root existence.
  This theorem asserts neither.

## Intended Lean interfaces

\`System.ExposedControlOutputAtAlpha\` on an EXACT Set S;
\`System.occupiedAlphaClosed_iff_noExposed\`; an immediate
nonclosed→exposed witness; and a CLOSED finite-test
proper-free-decomposition corollary via the independently
verified PR #414. Audit all named axioms.

This is an exact reduction of the nonclosed occupied A-boundary
case, not a completed genuine-Hales–Jewett compatible TARGET
root-profile existence proof. The full functional n-pass
sparsening theorem remains unverified.
