# Full singleton-language maps through the ACTUAL finite native attachment list

**19 October 2026 — English proof and adversarial audit before Lean.**

The original Appendix A iterated functional Picture is an ACTUAL
sequence of full native function-language attachments, not a
hypothetical relational surrogate. The verified construction
\`FunctionalPartite.EHN.Stage.attachList\` starts with a genuine
finite partite stage E and a list of prescribed FULL attaching
maps from one closed support of an old native partite B. It
constructs a genuine finite final stage T, one FULL core
embedding E↪T and a FULL embedding B↪T for EVERY copy index
in that list. These embeddings agree exactly on the prescribed
support vertices.

The preceding PRs check the canonical singleton output-part
translation of the genuine source objects:

* each old multivalued primitive F is exactly the family
  (F,q) of singleton-valued fibres by output part q;
* every FULL part-preserving native embedding translates
  to a FULL singleton-language embedding on the same map;
* every ACTUAL native full free amalgam remains a full
  singleton-language free amalgam, including its exact
  arbitrary weak induced source subdiagrams (merged #434);
* actual positive HJ coordinate powers are full-isomorphic
  after the translation (merged #433).

## The finite attachment result

Under the unchanged hypotheses of the native
\`Stage.attachList\`, retain its constructed final native
stage T, but translate ONLY its explicit full source maps
to the canonical split language:

    E^P ↪ T^P,
    B^P ↪ T^P   (one map per chosen line index).

For every listed index i, the attached B^P map and the
core E^P map agree on every point x of the EXACT original
closed attaching support S, after applying the
original prescribed split attaching map.

This is immediate by choosing the actual T/core/copy
provided by \`Stage.attachList\`, splitting each FULL
embedding using the checked \`Embedding.splitOutputParts\`,
and evaluating the existing source equality. The split
maps have the very same underlying functions, so
no additional gluing choices or vertices are needed.

An \`attachAll\` corollary covers an arbitrary finite
index type without selecting or ordering its indices.

## Independent audit

1. **This is a map-transport theorem, not a new
   relationally constructed stage.** T is exactly the
   actual native stage produced by the original
   functional HJ Picture, with native set-valued
   operations and EHN projection.
2. **The overlap S is genuinely closed**, exactly
   as required by the actual full functional
   attachment; it is NOT an arbitrary weak set
   treated as a full functional gluing root.
3. **Arbitrary weak tests** can be applied to the
   resulting ACTUAL free source diagram through
   the separately verified #434 weak-preimage
   lemma, without replacing the tested vertex set
   by its generated function closure.
4. **The finite list may have unrelated HJ
   parameter coordinates.** Unlike a global
   coordinate-retraction argument, this theorem
   does NOT require all lines to share any
   parameter coordinate. It only transports the
   genuine old/source embeddings.
5. **Projected control semantics:** the actual EHN
   map remains source-defined partial. Splitting
   the full attaching maps does not upgrade
   the global projection to a full homomorphism.
6. **Strict B-tree target roots:** nothing here
   proves that independently completed targets
   across unrelated lines have one compatible
   prescribed root. That is the genuinely
   remaining target-profile existence step.
7. **Function outputs:** all multivalued original
   fibres are preserved and reflected by the
   split FULL embeddings, by the verified
   output-part singletonization theorem.
8. **No new rank assumptions:** the exact stage
   carrier, original part map, and all tested
   vertex cardinalities remain unchanged.

Lean acceptance: add
\`EHN.attachList_splitCopies\` and
\`EHN.attachAll_splitCopies\`, using
only the actual existing native Stage constructors
and kernel-verified full embedding split functor.
Audit both named axioms plus full umbrella build.
