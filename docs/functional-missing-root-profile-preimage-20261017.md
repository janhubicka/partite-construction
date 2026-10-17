# The exact missing closure-slot profile is coherent across a genuine functional attachment

**English proof + adversarial audit, 17 October 2026.**

Let \(e:R\hookrightarrow B\) be a genuine FULL
part-preserving embedding of transversal set-valued-function
partite systems. Fix an arbitrary EXACT weak vertex set
\(S\subseteq V(B)\), and set \(S_R=e^{-1}[S]\).

For any \(F\), input tuple \(\bar r\in S_R^k\), and output
part \(q\), we have both:

1. The AMBIENT active output mask in \(R\) is exactly the
   ambient mask on \(e\bar r\) in \(B\) (existing
   \`Embedding.activeOutputAtPart_iff\`).
2. The SURVIVING active mask in the exact weak \(R|^w_{S_R}\)
   is exactly the surviving mask of the EXACT weak
   \(B|^w_S\) at the corresponding tuple.

**Proof of (2).** The forward direction maps a retained
source output \(y\in S_R\) to \(e(y)\in S\) by the FULL
function embedding. Conversely any target output
\(z\in F_B(e\bar r)\cap S\) is \(e(y)\) for an output
\(y\in F_R(\bar r)\), by the full FIBRE equality.
Since \(e(y)=z\in S\), we have \(y\in S_R\).
The output part is preserved by \(e\).
The same argument works with arbitrary multivalued fibres.

Therefore the "missing U-closure slot" predicate
\[
 \mathrm{Missing}_{F,q}(\bar r;S_R)
 := \mathrm{Active}_{F,q}^{R}(\bar r)
       \wedge \neg\mathrm{Active}_{F,q}^{R|^w_{S_R}}(\bar r)
\]
is preserved-and-reflected by every FULL functional
embedding on its exact inverse-image weak test.

Now let a genuine functional free attachment have two
FULL root embeddings \(i_L:R\hookrightarrow L\) and
\(i_H:R\hookrightarrow H\). For a common weak test in
the whole free amalgam, the exact intersections of the
root with the two side weak subsets coincide: both are
the preimage of the WHOLE weak test under the same
identified root. Hence the two sides carry the SAME
set of missing output-part slots on the common root.

This is the direct functional counterpart of agreement
of ambient active closure-root profiles in the corrected
U-closed induction. Importantly it includes **missing**
roots, not merely roots whose outputs already survived
the weak restriction.

## Adversarial audit

* FULL embeddings are essential. An EHN source-undefined
  input may acquire a target output, so even the ambient
  mask biconditional is false for arbitrary EHN projections.
* Exact PREIMAGE of the weak set is essential. If the left
  restriction omits one output while the right includes
  it, their surviving-mask predicates need not agree.
* The theorem uses no generated weak closure; all source
  carriers are literal preimages.
* No singleton-valued function assumption. A multivalued
  fibre can have missing outputs in some parts and present
  outputs in others; the result holds one output part at a time.
* The ambient/weak mask coherence concerns the TRUE
  functional source geometry. It does **NOT** itself imply
  compatible relative strict B-tree target completions:
  the relational C5 counterexample has no functions and
  vacuous active masks. That is still the separate
  history/rank geometric lemma.

**Formalization plan:** prove the surviving-mask iff
for a full partite embedding on an exact inverse-image
weak subset, derive the missing-mask iff, and then
specialize to two actual root embeddings with the
same selected weak-root preimage. Use the existing
\`System.funcTransversal\` throughout but do not insert
a relational intermediate construction.
