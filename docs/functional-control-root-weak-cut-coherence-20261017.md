# Root-level control missing-output masks agree across full weak side cuts

**17 October 2026 — English proof and adversarial audit BEFORE Lean.**

The previous exact weak-root theorems transport ambient and missing
SOURCE output-part masks along FULL partite embeddings. The related
control-projection dichotomy distinguishes a missing source output
from an input whose source fibre is entirely undefined while the
CONTROL fibre is defined. Here is the exact unconditional
common-root compatibility statement encompassing BOTH mechanisms.

## Theorem

Let R,L,H be transversal functional partite Systems over a common
part carrier P, let iL:R↪L and iH:R↪H be FULL embeddings, and let
S_L⊆L and S_H⊆H be exact weak vertex sets. Suppose they cut out
the same actual root vertices:

    iL^{-1}[S_L] = iH^{-1}[S_H].

For every symbol F, every input tuple x in this common weak root,
and every output part q:

1. \`Active\` for the SURVIVING source function output at part q in
   L|ᵂS_L iff \`Active\` in H|ᵂS_H.
2. For ANY functional control D on P, the statement
   \[
       q\in F_D(p_L(i_L\bar x))
       \quad\text{but no q-output survives in }L|^w_{S_L}
   \]
   is equivalent to the corresponding H-side statement.

The proof of (1) pulls back both side weak masks along their FULL
embeddings. On the root the two weak input carriers have equal
underlying vertices, so every retained root output survives on
one side iff it survives on the other. Every source fibre is
preserved-and-reflected by a FULL embedding, and its parts are
preserved. For (2), FULL partite embeddings preserve the part
labels of the input tuple. Hence the two projected D tuples are
literally equal. Combine with (1).

If the two sides are embedded FULLY in one common Whole, their
actual root images agree, and S_L,S_H are inverse images of ONE
weak S⊆Whole, the common-root cut hypothesis is automatic.

This is exactly the *source-root* part of the corrected
weak/U-closed correspondence even for the PHANTOM case when the
ambient source fibre is undefined but the D-control defines
the projected tuple. No source-defined EHN domain-reflection
condition is used in the root-coherence theorem itself.

## Adversarial audit

* FULL embeddings are indispensable. Replacing either root
  embedding by a merely weak EHN map can create missing control
  slots absent in the original source root.
* The equality of weak root preimages is indispensable. An output
  retained by one side and omitted by the other gives a counterexample.
* The control D is arbitrary; no control total-fibre homomorphism is
  asserted. The comparison uses only equality of **control input
  labels** and exact surviving source-output masks.
* Every function output is transversal in the actual native partite
  construction. This argument relies on full fibre reflection,
  not singleton outputs or a globally injective part map.
* Nullary function inputs have no distinguished root vertices but
  are still covered by the same exact weak-root-preimage argument.
* **Critical scope:** these theorems compare tuples belonging to
  the ACTUAL common attaching root. Extra A-labelled vertices
  in the two projected side histories need NOT belong to that
  common root. The statement does not construct a common TARGET
  strict B-tree completion or protected full A-mark. The C5 and
  K2-parity root-compatibility counterexamples remain valid.
* All source weak sets stay EXACT; there is no counted closure hull.

## Formalization acceptance

Use the previously kernel-checked
\`Embedding.weakActiveOutputAtPart_preimage_iff\`.
Prove an ambient-independent surviving-root common-cut equivalence,
then combine it with label equality to prove the control-missing
equivalence, and specialize to exact cuts from one ambient Whole.
Audit named Lean axioms and CI.

The genuinely missing global theorem remains the existence of
compatible **target** B-tree root-completion profiles for nonclosed
occupied A-boundaries under actual Hales--Jewett/history geometry
and predecessor rank n−1. Equal source/control Boolean profiles
cannot replace that geometric existence step.
