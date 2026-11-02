# Track B: exact native HJ power OLD input patterns (2026-11-02)

## Scope

This is a continuation of verified and merged native/2019 source-correspondence PR #535, not a proof of the full printed functional sparsening theorem. The manuscript is frozen and not modified.

The 2019 OLD equality-pattern relational expansion distinguishes **global injectivity of the distinct-input root** from a stronger *per-coordinate* injectivity requirement. The actual native Hales–Jewett power checks the former. It is not generally the coordinatewise relational product of OLD-encoded sources.

## Exact diagram and theorem contracts

For a genuine partite system B, an input pattern p with surjective argument map r:Fin(arity F) -> Fin(rootSize), a full root tuple x:Fin(rootSize) -> Induced.Vertex B N, and genuine native power Power = Induced.power B N:

- `nativePower_oldDomainPattern_iff`: the OLD `(.inr (.inl p))` domain predicate holds on x exactly when (a) the entire root x is injective as **power vertices**, and (b) there exists ONE common output part q such that every coordinate function fibre on the repeated-pattern input x∘r contains an output of part q. No hypothesis silently forces coordinatewise input injectivity.
- `nativePower_oldOutputPattern_iff`: the OLD `(.inr (.inr p))` value predicate holds on the exact root/output tuple exactly when the whole root is injective and the chosen output word is coordinatewise in each genuine source fibre.
- `nativePower_oldDomainPattern_control_iff`: with genuine `ProjectionHom A` and N>0, the complete OLD active-domain pattern is simply global power-root injectivity plus nonemptiness of the ORIGINAL control function on the tuple of part labels. This records repeated inputs via p.argMap and uses the previous verified common-output-part theorem.
- `nativePower_oldDomainPattern_coordinateCollapse`: a globally injective power root whose coordinate projection is noninjective can carry an actual OLD domain relation while the same root pattern fails in that source coordinate, provided a real common output part exists.
- `nativePower_globalInjective_coordinateCollision`: given two distinct original same-part vertices a and b, the explicit two-coordinate power words (a,a) and (a,b) are globally distinct but equal in coordinate zero. This proves the equality-pattern obstruction independently of any function-domain hypothesis.

All the above theorems refer to the **exact true native power vertices** and **do not use a surrogate relational power**. In particular the global equality pattern must be constructed *after* forming the native function-language power.

## When the coordinatewise OLD test is actually correct

`TrackBPowerOldRootTransversal2019.lean` repairs the naïve assertion under
an explicit and mathematically natural extra condition:

- `nativePower_coordinateRoot_injective_of_partInjective`:
  if distinct input-root vertices have distinct *part labels*, their
  vertex coordinates are injective for **every** coordinate. This is a
  genuine full-partite effect, not a generic fact about tuples of words.
- `nativePower_oldDomainPattern_transversal_iff`: for such roots,
  the actual OLD domain relation is equivalent to the collection of
  coordinatewise OLD domain relations *together with one common output
  part* present in every coordinate. No arbitrary output-part choices
  are identified.
- `nativePower_oldDomainPattern_transversal_control_iff`: if the
  source system has the verified full native `ProjectionHom A` and
  the power length is positive, the common-control projection makes
  all coordinate output-part sets equal. Under part-injective roots,
  the actual OLD domain predicate is therefore equivalent to
  `∀ i, coordinate i satisfies the SAME OLD domain pattern`.

This is the precise successful restricted comparison. The counterexample
to unrestricted coordinatewise OLD equality patterns still applies to
globally distinct power words *in the same input part*. Neither result
claims that **fresh canonical full-root tags** automatically commute
with relational coordinate powers: those tags inspect the entire induced
OLD pattern of all distinct input-root vertices.


## Complete fresh U-closure tag on the actual functional power

The new `TrackBPowerFreshFullRoot2019.lean` makes the missing
full-root data explicit, rather than conflating it with the OLD
domain/output relations.

- `RelStructure.patternTagExpansion_fresh_iff_fullOldRoot`:
  on any OLD relational source E, a *fresh* tag at `t` means the
  corresponding OLD output tuple is realized, the distinct-root
  prefix is globally injective, and **every OLD relation symbol
  on every input-root tuple** agrees with the prescribed complete
  relational structure `p.root`. The last clause has both directions
  (full embedding), not merely preservation of positive tuples.
- `Induced.nativePower_freshTag_iff_completeOldRootProfile`:
  on the ACTUAL Hales--Jewett native power, substitute the genuine
  coordinatewise output-word criterion while keeping exact global
  injectivity and the entire OLD root profile. This includes original
  relations, all equal-input-pattern active domains, and all OLD
  output relations, including negatives on the root.
- `Induced.nativePower_oldOutput_admits_canonicalFreshRoot`:
  every real OLD output witness with a positive distinct-input root
  determines an actual fresh closure tag using the exact induced
  OLD root, with no enlarged test carrier and no guessed pattern.
- `TrackBPowerFreshRootCollision2019.lean` upgrades the
  coordinate-collapse obstruction from a bare OLD active-domain
  predicate to a **real fresh 2019 U-closure tag**: if a globally
  injective native root has one common output part across all
  source coordinates, it has a genuine output word and hence its
  canonical complete-root tag, even when a particular coordinate's
  *same* OLD domain input-pattern symbol is false because its root
  collapses.

Therefore the unrestricted coordinatewise OLD-tagged product
interpretation is not an equivalence. The correct safe presentation
forms the native function-language Hales--Jewett power first, and
then adds complete OLD/root tags on its actual vertex set.

This conclusion is distinct from the **part-injective root** repair
above. Even when OLD relations admit a coordinatewise comparison,
the fresh U-tag `p` is indexed by the WHOLE OLD root pattern, whose
relations must all be preserved and reflected. It is not determined
by the symbol's own domain mask alone.

**Validation gate:** the four new fresh-root declarations have
`#print axioms` checks; do not mark them green before a complete
Lean CI success for the exact branch head. No TeX manuscript changes.

## Conclusions and unresolved directions

1. The positive source correspondence via canonical OLD tagging of each actual native stage is sound. The unqualified assertion `tag(nativePower) = relationalCoordinatePower(tag(native))` requires special compatibility conditions and must **not** be treated as a theorem; even OLD distinct-root equality patterns can fail to commute with coordinate powers.
2. The actual Hales–Jewett **line maps** remain FULL function maps and transport all induced ambient tagged weak-test data, as proved in merged `TrackBNativePowerTaggedLineTransport2019.lean` and `TrackBHeterogeneousTaggedPreimage2019.lean`. This suffices for the source-side geometry needed by the corrected 2019 weak-test induction.
3. This does not decide the separately required intrinsic-original-local-finiteness to ambient-relative 2019 K-completion implication (Track C), nor strict full-functional mixed-root B-tree targets (Track D).
4. Original class H/K membership requires canonical genuine Option(Set) encoding and explicit class closure, transversality, finiteness and isomorphism conditions; it cannot be inferred for arbitrary nonclosed induced ambient OLD tests.

Validation: draft until exact-head full Lean CI and named `#print axioms` pass. No TeX content or removed author TODO is altered.
