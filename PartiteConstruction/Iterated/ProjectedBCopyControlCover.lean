import PartiteConstruction.Iterated.ProjectedBCopyFinalCompletion

/-!
# Track E: existing INTERNAL B-cover in the CONTROL makes finite B-saturation possible

The selected-target compatibility hypothesis of the projected final
B-saturation theorem is automatic when the actual control itself has
internal B-extension on every irreducible subset: the source global
HE embeds each exact irreducible test fully into the control, and the
control internal B-copy extends that literal full image.

This gives a positive SAME CONTROL result with no hereditary-graph
irreducibility, A↪B, or unrelated external test-copy assumption:
one finite enlargement of the original relational Ramsey witness
retains its original embedding, Ramsey arrow and selected HE, and
has actual internal B-extension.

For the coordinated tagged 2019 proof, the STRICT RELATIONAL first
sparsening stage P already has internal Bplus coverage, while the
second tagged stage Qplus has a selected ordinary HE to P. This
corollary can therefore be applied on the Qplus->P side. It does NOT
yet show the B-augmented source remains U-closed/canonical or that its
original exact small-H relative completions survive the attachment.
-/

namespace StructuralRamsey.RelStructure.ProjectedBCopyControl

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {O B Q : Type v}
variable (Orig : RelStructure L O)
variable (Base : RelStructure L B)
variable (Control : RelStructure L Q)
variable (pOrig : O → Q)

/-- An HE from Orig to a control internally covered by B has exact,
SAME-MAP B-copy extensions in that control for ALL irreducible source
subsets S, not only chosen test patterns. -/
theorem projected_images_extend_of_control_internalCover
    (hpOrig : Orig.IsHomomorphismEmbedding Control pOrig)
    (hControl : IrreduciblesExtendTo Base Control)
    (S : Set O)
    (hS : (Orig.induce S).Irreducible) :
    ∃ beta : Embedding Base Control,
      ∀ z : S, ∃ b : B, pOrig z.1 = beta b := by
  obtain ⟨e, he⟩ := hpOrig.embeddingOn S hS
  have hRange : (Control.induce (Set.range e)).Irreducible :=
    hS.range_embedding e
  obtain ⟨beta, hbeta⟩ := hControl (Set.range e) hRange
  refine ⟨beta, ?_⟩
  intro z
  obtain ⟨b, hb⟩ := hbeta ⟨e z, ⟨z, rfl⟩⟩
  exact ⟨b, (he z).symm.trans hb⟩

/-- Positive conditional finite B-saturation: one final C' preserves
the old full core, its selected original projection and its HE clause,
and acquires genuine internal B-coverage. No local-tree statement. -/
theorem build_all_of_control_internalCover
    [Fintype O] [Finite B]
    (hpOrig : Orig.IsHomomorphismEmbedding Control pOrig)
    (hControl : IrreduciblesExtendTo Base Control) :
    ∃ (W : Type v) (_ : Finite W)
      (C' : RelStructure L W)
      (j : Embedding Orig C') (pNew : W → Q),
      C'.IsHomomorphismEmbedding Control pNew ∧
      (∀ o : O, pNew (j o) = pOrig o) ∧
      IrreduciblesExtendTo Base C' :=
  build_all Orig Base Control pOrig hpOrig
    (fun S hS =>
      projected_images_extend_of_control_internalCover
        Orig Base Control pOrig hpOrig hControl S hS)

/-- Any original Ramsey arrow also survives the internally-B-covered
finite enlargement on the SAME source control map. -/
theorem build_all_with_arrow_of_control_internalCover
    [Fintype O] [Finite B]
    {VA : Type v} {A : RelStructure L VA}
    {Color : Type*}
    (hArrow : StructuralRamsey.Arrow A Base Orig Color)
    (hpOrig : Orig.IsHomomorphismEmbedding Control pOrig)
    (hControl : IrreduciblesExtendTo Base Control) :
    ∃ (W : Type v) (_ : Finite W)
      (C' : RelStructure L W) (pNew : W → Q),
      StructuralRamsey.Arrow A Base C' Color ∧
      C'.IsHomomorphismEmbedding Control pNew ∧
      IrreduciblesExtendTo Base C' ∧
      ∃ j : Embedding Orig C',
        ∀ o : O, pNew (j o) = pOrig o :=
  build_all_with_arrow Orig Base Control pOrig
    hArrow hpOrig (fun S hS =>
      projected_images_extend_of_control_internalCover
        Orig Base Control pOrig hpOrig hControl S hS)

end StructuralRamsey.RelStructure.ProjectedBCopyControl
