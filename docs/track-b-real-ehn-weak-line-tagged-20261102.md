# Track B: genuine EHN weak-projection Hales–Jewett lines retain full 2019 tags

2 November 2026. Independent source-stage correction following merged Track B PR #535. The frozen survey manuscript is unchanged.

## Missing interface in previous source bridge

The earlier green `Induced.lineEmbedding_taggedWeakPreimage` was restricted to a **full native ProjectionHom**. The actual EHN stage has only `Stage.isPartite : WeaklyPartiteOver`, whose first component is the original `IsWeakHomomorphism` projection. The former hypothesis MUST NOT be silently inferred from the latter. The two notions differ on function-source undefinedness and complete projected fibres.

However, `Induced.weak_lineEmbedding` (verified in `WeakInduced.lean`) is itself an actual **FULL part-preserving function embedding**: one Hales–Jewett parameter coordinate gives a preimage of every native-power output and transversality gives uniqueness; this does not require the *projection* to preserve full function fibres.

## New statements on literal stage and weak tests

- `Induced.weak_lineEmbedding_taggedWeakPreimage` takes precisely `B.toStructure.IsWeakHomomorphism A B.part`, any genuine HJ line W, and arbitrary literal Test subset of the actual power's vertex type. It gives a FULL canonical 2019 tagged relational embedding from the exact preimage of Test through the unchanged native weak-line vertex function. Complete OLD input-root equality patterns, OLD active-domain masks, actual output relations and fresh U-root patterns are preserved and reflected.
- `Induced.weaklyPartite_lineEmbedding_taggedWeakPreimage` uses exactly `B.WeaklyPartiteOver A`, no stronger hypothesis.
- `EHN.Stage.taggedWeakLinePreimage` applies the same source map to the ACTUAL finite EHN stage T and its stored `isPartite`, preserving exact weak preimage subsets and original output-part splitting on the real native HJ power.

The proof composes the existing full `Induced.weak_lineEmbedding`, genuine output-part singleton split, and merged heterogeneous full tagged weak-preimage functor. No new Ramsey witness, local strict B-tree completion, or abstract surrogate power is fabricated.

## Independent scope

These are statements about full LINE embeddings into the actual power. They do NOT identify the weak projection `B.part` with a full original-2019 function homomorphism, do not assert that nonclosed *intrinsic* weak inclusion is full, and do not identify arbitrary old tagged coordinate powers with native power tagging. The latter issue is treated in independent draft PR #543 (complete root equality patterns).

Validation requires exact-head Lean build, active root inventory, and named axiom audit. No manuscript validation marker is added before success.
