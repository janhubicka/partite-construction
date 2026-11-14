# Track B — exact 2019 OLD U-closure naturality on actual HJ lines (14 November 2026)

The verified Track B full weak-preimage theorem (merged PR #658) gives equality of *whole-fibre* closure images along any genuinely full native copy or weak EHN Hales–Jewett line. The new theorem uses the separately checked 2019 ambient complete-mask closure dictionaries at the actual original source B and its **actual native coordinate power** `Induced.power B N` to give the same image equality for complete-mask OLD `UClosureHull`.

The exact weak source carrier is `S=weak_lineEmbedding(W)⁻¹(Test)`; the exact target is `Test`, not its function-closed hull. All generator seeds `Q⊆S` are handled. The native line is full even though the EHN part projection only weakly preserves functions; no `ProjectionHom` oracle is inserted. The theorem is specialized to any actual EHN Stage.

This does **NOT** identify the distinct 2019 tag languages, assert that OLD tagging commutes with an independently constructed relational power, or provide the still separate Track C H-valued local completion / Track D strict mixed-root B-tree theorem.

Additive Lean source, named `#print axioms`, active-root registration and documentation only. Frozen survey prose and existing TODO/validation-marker decisions untouched. DRAFT until exact-head build + axiom audit.
