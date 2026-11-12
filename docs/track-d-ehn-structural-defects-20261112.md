# Track D: structural source witnesses for all EHN full-embedding defects

**12 November 2026.** Candidate Lean module:
`PartiteConstruction/Functional/EHNGlobalDefectDecomposition.lean`.
This note is separate from the frozen numbered Appendix A manuscript.

## Exact input

Let `p : C → D` be an actual original-function-language EHN
homomorphism-embedding: weak globally, but represented by a FULL embedding on
every irreducible FULL source test. Source functions are set-valued and
**source-defined only** for the original 2019 partial semantics. Empty fibres
must not be silently identified with `Option (Set)` defined-empty fibres.

## Source-side trichotomy

If there is no FULL embedding `C ↪ D` with underlying vertex map `p`, then
one of the following **actual source** obstructions occurs:

1. **Collision.** Two distinct source vertices have the same `p` label.
   On a finite source, `C` itself has a proper FULL native free
   decomposition by the previously verified collision theorem.
2. **Relation reflection failure.** A specific positive target relation
   holds at `p ∘ xs` but not at the **actual original input tuple** `xs`.
   Its full function-closed source hull `closure(range xs)` admits a proper
   FULL native free decomposition. The corresponding Lean theorem is new.
3. **Function-domain reflection failure.** A specific target fibre at
   `p ∘ xs` is nonempty while the actual source fibre at `xs` is empty.
   The same input-generated hull admits a proper FULL decomposition by
   the existing `FibreExactness` theorem.

There is **no fourth defect** of missing target output values on a
source-defined input: `map_func_of_nonempty` already identifies the complete
source fibre image with the complete target fibre. The global trichotomy
uses `fullEmbedding_iff_inj_reflect_rel_domain` from merged PR #573;
the collision decomposition uses merged PR #575; and the fine within-atom
collision separation is merged PR #576.

## Adversarial limitations

The three certificates locate a source failure. They do **not** construct an
absolute or compatible relative strict `B`-tree extension of the outer HJ
attachment sides. The actual common root may have a noninjective **valid
original-partial** target map; forcing its global label map to be a full
embedding would be too strong. Further, a decomposition of the relation or
function **input hull** need not induce an aligned decomposition of the two
outer sides or preserve the preceding Hales–Jewett line-attachment histories.

A concrete next lemma would inductively realize the actual old side of a
selected ordered HJ attachment over the **same chosen root completion** as
the power core, protecting each old A-copy's intersection and every earlier
projected history. This is still open. The source certificates are reusable
negative gates, not a proof of the unrestricted native n-pass sparsening
theorem.

**Validation policy:** these three new declarations remain DRAFT until
the exact PR-head full Lean build, root-level named `#print axioms` tests,
and source/no-admissions checks pass. No numbered manuscript text or
previously removed collaborator TODO is changed.
