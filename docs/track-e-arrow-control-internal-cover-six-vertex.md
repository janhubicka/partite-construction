# Track E: Ramsey + same-map HE + externally compatible B-copies still lack internal B extension

**14 November 2026 — independent exhaustive finite regression.**
Run: \`python3 checks/track_e_arrow_external_internal_six_vertex.py\`.
The script enumerates all full induced embeddings and verifies every two-colouring. It is **NOT a Lean proof**, and it is **not a counterexample about the actual output of the coordinated 2019 tagged partite construction**.

Take the relation-only language of simple undirected graphs, A=K1, B=K2,
C=C5 disjoint union K1, control C0=K6, and the same selected vertex map f=id:C→C0.

- There are 6 distinct A-copies, 10 oriented B-copies, and 64 A-copy two-colourings. In every colouring, the odd C5 contains a monochromatic B-edge. Thus the Ramsey arrow C→(B)^A_2 is non-vacuous.
- The f-image of every edge is an edge of K6. For every irreducible induced source S, which is a clique of size at most 2, f|S is a full embedding. Hence f is a genuine homomorphism-embedding (but not a full embedding on all of C).
- Every one of the 12 irreducible induced source tests S embeds fully into B. Moreover **every f[S] is contained in some full B-copy in the control K6**, a stronger target-side compatibility property than the original external test coverage.
- The isolated source vertex v=5 is an irreducible singleton but belongs to no B-edge of C. Thus the *internal* extension \`IrreduciblesExtendTo B C\` fails.

**Implication for the actual 2019 two-pass witness.** Neither (i) its new kernel-checked same-map original native HE from upstream #1130, nor (ii) external protected closed U-irreducible B-test coverage, nor (iii) compatible B copies of the selected images *in the control*, yields internal B-copy extension. Any positive proof needs an actual *source-side B-copy lifting/extension invariant* or a final attachment step proving this while retaining the SAME output's global projection, Ramsey arrow and small-test H-relative certificates.

The separate native EHN route already constructs an output with \`IrreduciblesExtendTo B C\`, its own Ramsey arrow, global original-partial HE and strict **relational graph-tree** local control under the hereditary graph-irreducibility hypothesis. Its witness must not be identified with the actual coordinated two-pass H-class witness without a new theorem.

This regression strengthens the simpler **Lean-verified** abstract external-vs-internal separation \`StructuralRamsey.Structure.TrackEStatementAudit.externalUProtectedCover_doesNot_imply_internalCover\` in \`PartiteConstruction/Functional/TrackEProtectedCoverage2019.lean\`. It does not replace that axiom-audited theorem.
