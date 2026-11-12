# Track D — English FIRST: pure-power and existing-tree no-history strict functional certificates

**12 November 2026.** Companion to English-first rank-mixed PR #642.
This is a separate positive base/pure-case reduction for the proposed
weaker no-projected-history native strict functional invariant.
The frozen numbered survey Appendix A and collaborator TODOs are unchanged.

## 1. Any genuine strict Base-tree already has every-rank certificates

Let C be an ACTUAL FULL strict functional tree amalgam of copies of an
irreducible Base. Let A be an irreducible full native structure, and
let p:C→P be **ANY** map (the identity case and actual part projections
are both included).

For every LITERAL weak vertex set S⊆C, take target T=C itself and
the restricted identity `f:S→C`. The FULL identity embedding
`id_C` induces an `IsAmbientRelativeWeakHE C S C f` for
arbitrary weak S, because positive incidences are preserved and
the entire function fibre maps exactly whenever all source outputs
survive in S.

For each genuine FULL ambient embedding e:A↪C, irreducibility of A
and the verified tree-copy localization theorem for FULL native
functional trees give a FULL B-copy embedding j:Base↪C whose image
contains every vertex e(a). Since Base is irreducible, this j
certifies `e.ContainedInIrreducible`. Choose target A mark eT=e
itself; on all occupied S-vertices, trivially
`eT(a)=f(e(a))`.

Therefore `SetAmbientRelativeWeakTreeWitness A Base C p S []`
holds for **every** S, independently of |S|. In particular
`AtMostNoHistory A Base C p n` holds for every n. No total-fibre
homomorphism is required outside the preserved source weak inputs.

This settles the **initial Picture** base whenever the already
verified native initial stage is a strict full-functional tree
of Base copies (for the genuinely positive-arity initial/consistent
nullary-root setting used there).

## 2. Any EHN one-copy A→Base target also carries all-rank certificates

Let C be an actual full functional source with an EHN map
q:C→A. Let eAB:A↪Base be a FULL embedding, where Base itself is
irreducible and A is irreducible.

For arbitrary literal weak S⊆C take target T=Base with one-copy
strict tree, and `f(x)=eAB(q(x))` on S. The verified theorem
`IsEHNHomomorphismEmbedding.ambientRelativeWeak_to_embedding`
supplies the exact ambient-relative weak HE without assuming
that q is globally injective or reflects source-undefined domains.

Every actual FULL A-copy e:A↪C restricts under q to a FULL
embedding `q_e:A↪A` by EHN irreducible protection. The target
embedding `eT=eAB ∘ q_e : A↪Base` agrees with f on every occupied
vertex of that A-copy. Since Base itself is irreducible, this
entire target image lies in one irreducible constituent (namely
Base). Thus ambient A-copy protection holds.

Therefore `SetAmbientRelativeWeakTreeWitness A Base C p S []`
and `AtMostNoHistory A Base C p n` hold for all weak S and n
and **any** externally specified part map p.

Apply this to the ACTUAL native Hales–Jewett power core
`C=(Induced.power R N).toStructure`: the verified
`power_weaklyPartiteOver hR hN` supplies the EHN map into
the selected A, so the whole power has strict no-history
ambient-A tree certificates on EVERY weak test.
This discharges the **pure-core** branch independently of rank.

## 3. The remaining finite-picture step

For each one-copy native full attachment, a tested weak S either lies
entirely in the copied old side (inherit its `AtMostNoHistory n`),
lies entirely in the HJ power core (apply §2), or is mixed (apply the
English-first rank-mixed theorem of #642). Under the verified
ordinary HJ output/arrow/bookkeeping, finite induction over the
ACTUAL ordered list of parameter-line attachments then appears to
produce an entire functional Picture with
`AtMostNoHistory (m+1)`.

**BUT this whole-pass statement remains to be constructed and
machine checked**, including the exact weak restriction transport
along each full side and the final external EHN projection. The
stronger `AtMost` predicate with arbitrary histories is not
inferred from this weaker route.

## 4. Formalization acceptance

Add exact Lean named theorems:
- `SetAmbientRelativeWeakTreeWitness.of_strictTree_noHistory`,
- `SetAmbientRelativeWeakTreeWitness.of_ehn_oneCopy_noHistory`,
- `SetAmbientRelativeWeakTreeWitness.AtMostNoHistory.of_strictTree`,
- `SetAmbientRelativeWeakTreeWitness.AtMostNoHistory.of_ehn_oneCopy`.

Use the checked native `LooseTreeAmalgam.ofTree` and
`LooseTreeAmalgam.irreducible_contained_in_copy` to produce target
irreducible containment; no invented Gaifman-completeness argument.
Use the existing `Embedding.ambientRelativeWeakRestriction` and
`IsEHNHomomorphismEmbedding.ambientRelativeWeak_to_embedding`.
Named #print axioms and complete exact-head CI. No proof holes,
frozen manuscript edits or unverified n-pass claims.
