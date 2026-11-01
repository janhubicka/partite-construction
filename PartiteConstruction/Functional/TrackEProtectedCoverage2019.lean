import PartiteConstruction.Functional.PublishedTotalBinaryObstruction
import PartiteConstruction.Ramsey.ClosureUIrreducible2019
import PartiteConstruction.Iterated.FinalAttachment

/-!
# Track E: external 2019 protected B-coverage versus internal B-extensions

This is the *exact quantified shape* of the external closed-U,
U-irreducible B-coverage clause in the corrected 2019 two-pass
functional profile theorem. At its canonical whole-mask tagged
instantiation, Base is the tagged B and C the final tagged picture.

The target copy of Test lives IN Base, not inside the final C.
Even if C fully embeds into Base, this property does not imply
that an actual Base-copy embeds into C. No changes to test carriers,
no closure hulls, and no surrogate target classes are involved.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V W : Type v}

/-- The exact *external* 2019 B-coverage quantification: every CLOSED
U-irreducible test embedded in C embeds in Base. It does not demand
an embedding of Base into C. The canonical tagged 2019 hCover is an
instance of this predicate using the whole-mask closure rules. -/
def ExternalClosedUIrreducibleBCoverage
    (rules : ClosureDescription L)
    (Base : RelStructure L V) (C : RelStructure L W) : Prop :=
  ∀ {T : Type v}
    (Test : RelStructure L T),
    IsUClosed rules Test →
    IsUIrreducible rules Test →
    Embedding Test C →
    Nonempty (Embedding Test Base)

/-- A full embedding of C into Base gives the exact external test
coverage with the SAME test inclusion map, for arbitrary U rules.
It does NOT construct any embedding Base → C. -/
theorem ExternalClosedUIrreducibleBCoverage.ofEmbedding
    (rules : ClosureDescription L)
    {Base : RelStructure L V} {C : RelStructure L W}
    (e : Embedding C Base) :
    ExternalClosedUIrreducibleBCoverage rules Base C := by
  intro T Test _ _ j
  exact ⟨e.comp j⟩

end StructuralRamsey.RelStructure

namespace StructuralRamsey.Structure.TrackEStatementAudit

open StructuralRamsey
open StructuralRamsey.Structure

universe u

/-- Even the EXACT external 2019 U-protected test-coverage schema,
PLUS a genuine full functional embedding C → B, does not imply
internal irreducible-to-B-copy extension in C. Here C is the actual
one-point first-projection functional algebra, B is its two-point
counterpart; the counterexample works for ANY closure description.
This is an abstract 2019 relational-schema regression. It is NOT
a claim that an arbitrary such graph is itself a whole-mask-tagged
2019 profile witness. -/
theorem externalUProtectedCover_doesNot_imply_internalCover
    (rules : RelStructure.ClosureDescription
      PublishedTotalBinaryObstruction.language.graph) :
    RelStructure.ExternalClosedUIrreducibleBCoverage rules
      PublishedTotalBinaryObstruction.B.graph
      PublishedTotalBinaryObstruction.A.graph ∧
    ¬ RelStructure.IrreduciblesExtendTo
      PublishedTotalBinaryObstruction.B.graph
      PublishedTotalBinaryObstruction.A.graph := by
  let e : Embedding
      PublishedTotalBinaryObstruction.A
      PublishedTotalBinaryObstruction.B :=
    PublishedTotalBinaryObstruction.ofInjection
      (fun _ : Fin 1 => (0 : Fin 2))
      (by intro x y h; exact Subsingleton.elim x y)
  constructor
  · exact RelStructure.ExternalClosedUIrreducibleBCoverage.ofEmbedding
      rules e.graph
  · intro hInternal
    have hIrr :
        (PublishedTotalBinaryObstruction.A.graph.induce Set.univ).Irreducible := by
      intro x y hxy
      exact (hxy (Subtype.ext (Subsingleton.elim x.1 y.1))).elim
    obtain ⟨j, _⟩ := hInternal Set.univ hIrr
    have h01 : (0 : Fin 2) = 1 :=
      j.injective (Subsingleton.elim (j 0) (j 1))
    exact (by decide : (0 : Fin 2) ≠ 1) h01

end StructuralRamsey.Structure.TrackEStatementAudit
