import PartiteConstruction.Iterated.RelativeTreeCompletion
import PartiteConstruction.Iterated.ProjectedPartialLocalTreeLike

/-! # Relative completions from projected-history witnesses

A projected finite side E -> D whose selected overlap projects inside one
full A-copy alpha(A) can be completed relative to the projected overlap,
provided D carries the projected-partial local-tree invariant.

The source overlap itself need not embed into D.  Its projection defines a
possibly non-injective quotient map to the induced projected overlap Q.  The
history invariant supplies an actual embedding of Q into the target tree,
agreeing with the side witness.  This is precisely the quotient-relative
completion datum needed for coherent mixed gluing.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB H E P : Type v}
variable {Control : RelStructure L UA}
variable {Base : RelStructure L VB}
variable {Dsrc : RelStructure L H}
variable {Esrc : RelStructure L E}
variable {D : RelStructure L P}

namespace ProjectedPartialLocallyTreeLike

/-- One projected side admits a quotient-relative completion over its selected
source overlap. -/
theorem relativeCompletion
    [Fintype E] [DecidableEq P]
    (hControl : Control.Irreducible)
    (hD : ProjectedPartialLocallyTreeLike
      (A := Control) (D := D) (C := D) Base id m)
    (s : Embedding Dsrc Esrc)
    (p : E → P)
    (hp : Esrc.IsHomomorphismEmbedding D p)
    (α : Embedding Control D)
    (hOverlap : ∀ d : H, ∃ a : UA, p (s d) = α a)
    (hcard : ((Finset.univ : Finset E).image p).card ≤ m) :
    let I : Finset P := (Finset.univ : Finset E).image p
    let q0 : H → P := fun d => p (s d)
    let Gset : Set P := Set.range q0
    let Q : RelStructure L Gset := D.induce Gset
    let q : H → Gset := fun d => ⟨q0 d, ⟨d, rfl⟩⟩
    QuotientRelativeTreeCompletion Q q Base s := by
  classical
  let I : Finset P := (Finset.univ : Finset E).image p
  obtain ⟨Y, T, hTree, g, hg, hPart⟩ := hD I hcard

  let pI : E → ↥(↑I : Set P) :=
    fun e => ⟨p e, Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩⟩
  have hpI :
      Esrc.IsHomomorphismEmbedding (D.induce (↑I : Set P)) pI :=
    hp.codRestrict (↑I : Set P)
      (fun e => Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩)
  let f : E → Y := g ∘ pI
  have hf : Esrc.IsHomomorphismEmbedding T f :=
    hg.comp hpI

  let q0 : H → P := fun d => p (s d)
  let Gset : Set P := Set.range q0
  let Q : RelStructure L Gset := D.induce Gset
  let incQD : Embedding Q D := inclusion D Gset

  have hQrange : ∀ z : Gset, ∃ a : UA, incQD z = α a := by
    intro z
    rcases z.2 with ⟨d, hd⟩
    obtain ⟨a, ha⟩ := hOverlap d
    exact ⟨a, hd.symm.trans ha⟩
  let eQA : Embedding Q Control :=
    incQD.factorThroughRange α hQrange
  have heQA (z : Gset) : α (eQA z) = z.1 := by
    exact (Classical.choose_spec (hQrange z)).symm

  let Hset : Set UA := Set.range eQA
  let eHA : Embedding (Control.induce Hset) D :=
    α.comp (inclusion Control Hset)
  have hHAproj :
      ∀ x : Hset, id (eHA x) = α x.1 := by
    intro x
    rfl
  have hHArange : ∀ x : Hset, eHA x ∈ I := by
    intro x
    rcases x.2 with ⟨z, hz⟩
    have hzI : z.1 ∈ I := by
      rcases z.2 with ⟨d, hd⟩
      apply Finset.mem_image.mpr
      refine ⟨s d, Finset.mem_univ _, ?_⟩
      exact hd
    change α x.1 ∈ I
    rw [← hz]
    rw [heQA z]
    exact hzI

  obtain ⟨bHA, hbHA, hcHA⟩ :=
    hPart α Hset eHA hHAproj hHArange

  let eQH : Embedding Q (Control.induce Hset) := {
    toFun := fun z => ⟨eQA z, ⟨z, rfl⟩⟩
    injective := by
      intro x y hxy
      apply eQA.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R x
      change Control.rel R (eQA ∘ x) ↔ Q.rel R x
      exact eQA.map_rel_iff R x
  }
  let bQ : Embedding Q T := bHA.comp eQH
  have hbQ (z : Gset) :
      bQ z = g ⟨z.1, by
        rcases z.2 with ⟨d, hd⟩
        apply Finset.mem_image.mpr
        exact ⟨s d, Finset.mem_univ _, hd⟩⟩ := by
    change bHA (eQH z) = _
    rw [hbHA (eQH z)]
    apply congrArg g
    apply Subtype.ext
    exact heQA z

  have hcQ : bQ.ContainedInIrreducible := by
    rcases hcHA with ⟨R, hR, hsub⟩
    refine ⟨R, hR, ?_⟩
    intro z
    exact hsub (eQH z)

  let q : H → Gset := fun d => ⟨q0 d, ⟨d, rfl⟩⟩
  have hagree : ∀ d : H, f (s d) = bQ (q d) := by
    intro d
    rw [hbQ (q d)]
    rfl

  exact QuotientRelativeTreeCompletion.mkOfBoundary
    hTree f hf bQ hagree hcQ

end ProjectedPartialLocallyTreeLike
end StructuralRamsey.RelStructure
