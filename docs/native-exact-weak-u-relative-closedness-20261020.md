# Exact weak FUNCTION closedness equals relative U-substructure closedness of induced AMBIENT tags

**20 October 2026 — English proof and adversarial audit before Lean**

The faithful functional/U-closed dictionary must extend to **every**
weak induced test, not only closed subsets of the original full structure.

Let A be a finite genuine set-valued function structure with positive
primitive function arities. Fix an ARBITRARY exact weak vertex subset
S⊆V(A), and form the native weak structure A|ᵂS: its function outputs
are restricted to those original outputs that survive inside S.
Let E be the canonical full OLD equality-pattern graph of A with its
complete-root fresh 2019 U-tags, and consider the induced **AMBIENT**
tagged relational weak test E|S.

For every subset T⊆S (a subset of the subtype carrier), the claim is

\[
 \operatorname{IsClosed}_{A|^wS}(T)
 \quad\Longleftrightarrow\quad
 \operatorname{IsUSubstructure}_{\mathcal U,E|S}(T).
\]

It says that weak function-closure within S is precisely relative
U-closure in the induced ambient tagged structure. It is stronger
than agreement of closed sets in the full original A because S
may omit outputs and roots themselves need not be closed.

### Forward

A fresh tagged closure tuple surviving in E|S has a true old
function-output graph incidence in the full A, and every vertex
of the tuple lies in S. All its root inputs lie in T, and the
output is therefore a value in the weak restricted native
function A|ᵂS. If T is closed in the weak native structure,
the surviving output belongs to T. All other tuple coordinates
were already root vertices, so the U-substructure condition holds.

### Reverse

Take a surviving native function value y∈F_{A|ᵂS}(x) with all
inputs x_i∈T. In full A, factor the actual input tuple into
an injective enumeration e of its distinct vertices and a
surjection r from argument positions to those vertices.
Since the primitive arity is positive, the distinct-root size
is positive.

The full A-domain root is active (the output y witnesses it);
extract the complete full induced OLD input-root pattern and
its canonical fresh U-tag. The actual output graph tuple (e,y)
satisfies the corresponding tag in full E. All coordinates
lie in S, so the same tuple survives in E|S. Every root
vertex appears among x_i and therefore lies in T.
Relative U-substructure closure forces the last coordinate y
into T, proving weak native closedness.

This proof works for genuinely multivalued output fibres
and repeated input arguments; it does not assume the source
weak test is closed and never generates extra vertices.

### Why the AMBIENT tag is essential

A domain tuple can remain TRUE after all of its outputs
have been removed by weak restriction. For unary F(a)={b}
and S={a}, the ambient tag structure E|S retains the OLD
domain relation of a, although its fresh output closure
relation is empty. This is the correct semi-closed
intermediate state in the 2019 Picture.

If one recomputed the entire old-domain/root pattern from
A|ᵂS, the active domain bit would disappear and could
change the names of the complete-root tags. Nonetheless
the relative U-closure condition of E|S is still EXACTLY
weak native output closure as stated.

### Adversarial limits

* Positive arity required for the published full-root U-rule.
  Nullaries need the separately developed nullary interface.
* The equivalence is about closures of subsets **inside the
  exact weak test S**. It does not assert that these subsets
  are closed in full ambient A.
* U-semi-closedness of E|S is also independently verified;
  it does not entail U-closedness or existence of an output
  above an active but output-omitted root.
* The theorem says nothing about source-defined EHN
  homomorphism reflection or compatible strict B-tree
  target-root completions.
* It does not imply that an n-vertex weak test can be
  replaced by its ambient generated closure at the
  same vertex budget.

### Lean acceptance

Prove \`Structure.weakIsClosed_iff_ambientTagged_isUSubstructure\`
by adapting the already verified exact full-ambient
dictionary, with every construction on the literal
subtype carrier S. Then derive equality of native
weak functionClosure and relative UClosureHull on S
and equivalence of weak-test generating sets.

Audit named axioms and complete umbrella CI.

## Exact intrinsic weak-generator rank

The same relative-closure identity holds for every seed T⊆S, so
T generates the WHOLE weak functional structure A|ᵂS if and only if
it generates the induced AMBIENT tagged structure E|S in the
published relative U-sense. In particular, for every finite n,

\[
 (A|^{w}S).\mathrm{GeneratedByAtMost}(n)
 \quad\Longleftrightarrow\quad
 \mathrm{USize}(\mathcal U,E|S)\le n.
\]

The qualifier **intrinsic to the exact weak S** is important:
\(\mathrm{USize}(E|S)\) need not equal the U-size of the
generated *ambient* hull of S. The corrected 2019 proof
contains independent counterexamples to that false equality.

The additional Lean declarations are
\`weakGeneratedBy_iff_ambientTaggedUGenerating\` and
\`weakGeneratedByAtMost_iff_ambientTaggedUSize_le\`.
This closes the numerical weak-substructure presentation
dictionary once the current CI/axiom audit succeeds; it
still does not construct the missing strict functional
history-compatible target root.
