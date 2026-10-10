# Tagged closure symbols for the repaired recursive Picture proof

10 October 2026; continuation after #187. The original paper remains frozen.

## Why tagging is necessary

The old relational closure description ties one finite irreducible root
to one designated relation symbol, and its validity clause quantifies over
every tuple of that symbol. Attaching different unary part profiles to
the roots while retaining one old symbol invalidates that clause.

The tagged-language construction retains **all original relation
symbols** (so negative and nullary information is still reflected) and
adds two families:

* one NEW relation symbol for each original closure rule and every
  assignment of part labels to its root positions;
* the unary predicates naming individual parts.

The new tagged closure tuple predicate is the old closure predicate
AND equality of its root-part labels to the tag. Every tagged root is
the original induced root with its matching unary part predicates and
the tagged relations induced from that same data.

This ensures distinct root profiles have genuinely different closure
relation symbols. The old irreducibility witness remains a witness in
the expanded language, because every old relation symbol is retained.

## Checked interface targeted by this patch

`ClosureTaggedParts.lean` introduces
`ClosurePartTag`, `RelLanguage.withTaggedClosureParts`,
`RelStructure.expandTaggedClosureParts`, `ClosurePartTag.liftRule`,
and `ClosureDescription.withTaggedClosureParts`.

The first transport theorem asserts that for every exact subset S:

    IsUSubstructure U A S
      iff
    IsUSubstructure U_tag (expandTaggedClosureParts U A part) S.

The proof is direct. For a tagged tuple, forget its tag and apply
the original relative-closure condition. Conversely, for an old
closure tuple choose precisely the tag determined by its actual
root-part labels, so it is a tagged closure tuple and the tagged
relative-closure condition applies. No vertices are added; the
carrier S is the exact same set throughout.

A second module, `ClosureTaggedPartsClosedness.lean`, also establishes
exact equivalence of **U-closedness** of the entire expanded structure:
`isUClosed_iff_taggedParts`. This uses an explicit full-embedding
translation between original and tagged languages. For each tagged
tuple, the original closure rule provides a root embedding, and its
root labels automatically agree with the tag. Conversely, choose
the tag from the root labels of the original tuple. For every root
embedding, the old and new unique closure tuples coincide after
forgetting the tag, so the EXISTENCE and UNIQUENESS clauses transport
in both directions.

Both equivalences hold for arbitrary finite or infinite carrier types,
including structures with nullary relations. No vertices are added.
The proof does NOT require full U-closedness of the target before
translating: that is precisely what it establishes.

Later steps must still establish the equivalence of relative
free-decomposition and closed-U-irreducibility predicates, the
repaired positive completion-map transport, and local Ramsey-control
conditions in the expanded language.
The inner class must also meet the necessary Ramsey-control conditions;
these are NOT silently inferred from the ordinary Ramsey hypothesis
on the outer class.

## Remaining proof obligations

The actual no-common-variable-coordinate rank increment remains open:
both projected side generator budgets must be derived from the
Hales--Jewett history or from a justified relative-boundary invariant,
not simply assumed. The initial nonclosed-control repair still
requires the complete inner recursion and extraction after the
tagged-language transport.

This patch does not assert Theorem 2.18, Lemma 2.28 or a full
closed-test multiamalgamation theorem. Together, the two modules
introduce eight checked declarations (seven definitions/auxiliary
lemmas and two main iff statements are counted explicitly in the
audit). Consult PR #188 for the FINAL full-project build and
permitted-axiom audit; earlier successful partial builds do not
certify the last source revision. No independent referee process
is claimed.
