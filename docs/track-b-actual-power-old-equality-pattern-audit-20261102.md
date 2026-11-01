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

## Conclusions and unresolved directions

1. The positive source correspondence via canonical OLD tagging of each actual native stage is sound. The unqualified assertion `tag(nativePower) = relationalCoordinatePower(tag(native))` requires special compatibility conditions and must **not** be treated as a theorem; even OLD distinct-root equality patterns can fail to commute with coordinate powers.
2. The actual Hales–Jewett **line maps** remain FULL function maps and transport all induced ambient tagged weak-test data, as proved in merged `TrackBNativePowerTaggedLineTransport2019.lean` and `TrackBHeterogeneousTaggedPreimage2019.lean`. This suffices for the source-side geometry needed by the corrected 2019 weak-test induction.
3. This does not decide the separately required intrinsic-original-local-finiteness to ambient-relative 2019 K-completion implication (Track C), nor strict full-functional mixed-root B-tree targets (Track D).
4. Original class H/K membership requires canonical genuine Option(Set) encoding and explicit class closure, transversality, finiteness and isomorphism conditions; it cannot be inferred for arbitrary nonclosed induced ambient OLD tests.

Validation: draft until exact-head full Lean CI and named `#print axioms` pass. No TeX content or removed author TODO is altered.
