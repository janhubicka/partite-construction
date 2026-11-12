# Track D — reroot a partial side completion when only the separator map is full

**12 November 2026.** Candidate native-functional theorem, separate from the
frozen numbered Appendix A manuscript.

## New positive intermediate case

The source has a FULL embedding `s:Root↪Side` and an ABSOLUTE strict
original-2019 partial B-tree witness `p:Side→T`. The map `p` need **not**
be injective globally, nor reflect source-undefined function domains away
from `Root`.

Assume that the RESTRICTION `p∘s` is represented by a FULL embedding
`j:Root↪T` whose image lies in a single irreducible Base-copy inside `T`.
Then for any prescribed FULL `q:Root↪Base`, we may freely attach the
existing strict target tree `T` to a fresh Base copy over the two full
embeddings `q` and `j`. The resulting strict extension carries a
genuine original-partial map from the ENTIRE side and agrees with `q`
on the root. Root irreducibility is unnecessary.

This strictly relaxes the earlier routes:

* `of_full_tree_rooted` required a FULL embedding of the ENTIRE Side;
* `of_irreducible_root_absolute` obtained fullness of the root restriction
  automatically by assuming Root itself irreducible.

## New defect-based criterion

For a *chosen* original-partial map `p:Side→T`, the restricted root map
is FULL provided all three exact conditions hold:

1. `p∘s` is injective;
2. every target positive relation on a projected original root tuple is
   positive in Root (relation reflection);
3. a target-defined original function input tuple on `p∘s` is
   source-defined in Root (domain reflection).

The EHN fibre-exactness theorem supplies all target output values on
source-defined inputs, so no fourth extra-value condition is necessary.
One further hypothesis ensures that `p(s(Root))` lies in one specified
irreducible `Base` constituent of the chosen strict target tree.

Two named Lean theorems: `of_partial_side_full_root` and
`of_partial_side_root_defects_absent`.

## Adversarial boundary

This theorem neither provides the chosen absolute side map with the three
properties nor handles a genuinely colliding **canonical** EHN root map.
The maximal-rank mixed-root step may require a larger shared starting
strict tree and a NONINJECTIVE root completion. Independent absolute
side completions may still disagree there.

The theorem only weakens unnecessary assumptions in a positive
root-faithful subcase; it is not a solution of all ordered Hales–Jewett
attachment histories, and it adds no new manuscript validation marker.

**Gate:** keep as DRAFT until the exact-head full Lean build and named
`#print axioms` tests succeed, with no proof holes or new axioms.
