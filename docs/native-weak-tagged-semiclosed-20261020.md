# Every exact weak test of a genuine multivalued functional partite system is 2019 U-semi-closed

**20 October 2026 — English proof and adversarial audit BEFORE Lean**

The user's guiding equivalence with the U-closed 2019 partite
construction applies at the **semi-closed intermediate stage**,
not merely to fully function-closed tests.

Let B be any genuine transversal partite System with arbitrary
set-valued/multivalued primitive functions and fixed part carrier P.
Pass to the canonical singleton partial symbols (F,q), retaining
every original value in its actual part q. Take the complete-root
canonical 2019 tagged equality-pattern expansion E of this
singleton system on the very SAME vertex carrier.

The already verified canonical tag theorem proves
\[
                    \mathrm{IsUClosed}(\mathcal U,E).
\]
No positive-arity restriction is needed here: the tag rules
themselves quantify only over complete **positive** roots;
nullary function symbols are present in the old graph data
but not incorrectly treated as positive closure roots.

For **any exact literal weak set** S⊆V(B), form the ambient
induced tagged structure E|S. The checked 2019
\`IsUClosed.induce_isUSemiClosed\` theorem immediately gives
\[
               \mathrm{IsUSemiClosed}(\mathcal U,E|S).
\]

The output relation is now PARTIAL over roots: a full ambient
output tuple with last vertex outside S disappears, while its
old domain-root relation can remain active inside S. Nonetheless
every surviving tagged tuple has a valid full root and there is
at most ONE tagged output tuple over each root (for each
output part), exactly the Definition 2.24 semi-closed invariant.
This is the correct intermediate little-Picture condition;
it does NOT require all roots to have outputs.

For finite B in a positive-function-arity language the checked
dictionary also proves the sharper classification
\[
  \mathrm{IsUClosed}(\mathcal U,E|S)
  \ \Longleftrightarrow\
  S\text{ is function-closed in original }B.
\]
Thus weak Test is always semi-closed and is fully U-closed
PRECISELY when all native source outputs remain inside Test.
No closure hull or increased counted vertex set enters the
induction.

## Adversarial checks

* **False strengthening:** E|S is not generally U-closed.
  For unary F(a)={b}, S={a}, the active input-root tag is
  still present but its output tuple is missing.
* **Do not recompute old domain relations** from the truncated
  native weak fibres; that would erase the rooted obligation.
* **Transversality** is used only to make each (F,q) singleton,
  NOT to assert the original whole fibre has one value.
* **Partial/EHN projection:** the new theorem is a source
  property of a genuine System, and does not make an EHN
  stage part projection globally full or domain-reflecting.
* **Free amalgamation over weak roots:** 2019 free-amalgam
  semiclosed preservation assumes its COMMON root U-closed.
  This statement does not infer that an arbitrary weak
  common root is U-closed. Instead, the entire weak source
  stage is already induced from an ambient canonical
  U-closed structure, so semi-closedness is direct.
* **Target issue:** having a semi-closed source little
  Picture is the correct invariant for the recursive
  argument, but a subsequent closed target pass must
  still synchronize actual HJ histories/root profiles.
  This lemma is not a general strict B-tree completion
  over arbitrary nonclosed mixed roots.

## Lean acceptance

Prove for EVERY native transversal multivalued B and S:
1. \`System.taggedOutputPart_isUClosed\`
2. \`System.taggedOutputPart_weak_isUSemiClosed\`

Both reuse the already checked singleton output split and
2019 canonical tag / semi-closed inheritance theorems.
Three exact weak-root operations stay on the same vertices.
Audit named axioms and run full CI before merge.

