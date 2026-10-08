import PartiteConstruction.Functional.ProjectedIrreducibleCover
import PartiteConstruction.Functional.LooseTreeAmalgam
import PartiteConstruction.Functional.PublishedSparseningTarget

/-! # Full functional completion with a weak projected map

Assume that every irreducible full substructure of C projects into a full
B-copy in D. A finite free-decomposition induction embeds C fully into a
finite loose functional tree of B-copies and extends its EHN projection to D.
The target has genuine functions and closed gluing roots. Only the extra
requirement that each root lie in an irreducible piece is dropped.

This is a corrected version of the final B-extension step, not a strict
sparsening theorem. The whole completed witness is a loose tree, so no
vertex-size bound or closure-size substitution is involved.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V W P : Type v}

/-- A finite full completion retaining a prescribed weak EHN projection. -/
def HasProjectedLooseTreeCompletion
    (Base : Structure L V) (C : Structure L W) (D : Structure L P)
    (p : W → P) : Prop :=
  ∃ (Y : Type v) (_ : Finite Y) (T : Structure L Y),
    LooseTreeAmalgam Base Y T ∧
    ∃ e : Embedding C T, ∃ q : Y → P,
      T.IsEHNHomomorphismEmbedding D q ∧ ∀ x, q (e x) = p x

/-- The original final-extension idea works for genuine functional trees
with arbitrary closed roots, while keeping the prescribed weak projection. -/
theorem ProjectsIrreduciblesInto.projectedLooseCompletion
    {Base : Structure L V} {C : Structure L W} {D : Structure L P}
    [Finite V] [Finite W] {p : W → P}
    (hCov : ProjectsIrreduciblesInto Base C D p)
    (hp : C.IsEHNHomomorphismEmbedding D p) :
    HasProjectedLooseTreeCompletion Base C D p := by
  classical
  have aux : ∀ n : ℕ, ∀ {X : Type v} [Fintype X],
      ∀ (E : Structure L X) (q : X → P),
      Fintype.card X = n →
      E.IsEHNHomomorphismEmbedding D q →
      ProjectsIrreduciblesInto Base E D q →
      HasProjectedLooseTreeCompletion Base E D q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X instX E q hcard hq hCover
      by_cases hIrr : E.Irreducible
      · obtain ⟨g, hg⟩ := hq.2 E hIrr (Embedding.id E)
        obtain ⟨beta, hb⟩ := hCover E hIrr (Embedding.id E)
        have hrange : ∀ x : X, ∃ b : V, g x = beta b := by
          intro x
          obtain ⟨b, hxb⟩ := hb x
          exact ⟨b, (hg x).trans hxb⟩
        choose f hf using hrange
        let eBase : Embedding E Base := g.factorWithMap beta f hf
        refine ⟨V, inferInstance, Base,
          LooseTreeAmalgam.copy (Embedding.id Base) (fun x => ⟨x, rfl⟩),
          eBase, beta, beta.isEHNHomomorphismEmbedding, ?_⟩
        intro x
        exact (hf x).symm.trans (hg x)
      · have hDec : Nonempty (ProperFreeDecomposition E) := by
          by_contra hn
          exact hIrr ((irreducible_iff_noProperFreeDecomposition E).mpr hn)
        obtain ⟨d⟩ := hDec
        letI : Finite d.Left := Finite.of_injective d.leftIn d.leftIn.injective
        letI : Finite d.Right := Finite.of_injective d.rightIn d.rightIn.injective
        letI : Fintype d.Left := Fintype.ofFinite d.Left
        letI : Fintype d.Right := Fintype.ofFinite d.Right
        have hLeftCard : Fintype.card d.Left < n := by
          rw [← hcard]
          exact Fintype.card_lt_of_injective_not_surjective
            d.leftIn d.leftIn.injective d.leftProper
        have hRightCard : Fintype.card d.Right < n := by
          rw [← hcard]
          exact Fintype.card_lt_of_injective_not_surjective
            d.rightIn d.rightIn.injective d.rightProper
        obtain ⟨YL, hYL, TL, hTreeL, eL, pL, hpL, heL⟩ :=
          ih (Fintype.card d.Left) hLeftCard d.left (q ∘ d.leftIn) rfl
            (hq.comp d.leftIn.isEHNHomomorphismEmbedding)
            (hCover.precomp_weak d.leftIn.isWeakHomomorphism)
        obtain ⟨YR, hYR, TR, hTreeR, eR, pR, hpR, heR⟩ :=
          ih (Fintype.card d.Right) hRightCard d.right (q ∘ d.rightIn) rfl
            (hq.comp d.rightIn.isEHNHomomorphismEmbedding)
            (hCover.precomp_weak d.rightIn.isWeakHomomorphism)
        letI : Finite YL := hYL
        letI : Finite YR := hYR
        let tL : Embedding d.common TL := eL.comp d.toLeft
        let tR : Embedding d.common TR := eR.comp d.toRight
        let T := FreeAmalgam.amalgam d.common TL TR tL tR
        let jL := FreeAmalgam.leftEmbedding d.common TL TR tL tR
        let jR := FreeAmalgam.rightEmbedding d.common TL TR tL tR
        have hTgt : IsFreeAmalgam tL tR jL jR :=
          FreeAmalgam.isFreeAmalgam d.common TL TR tL tR
        have hcompat : ∀ z : d.Common, pL (tL z) = pR (tR z) := by
          intro z
          have hz : d.leftIn (d.toLeft z) = d.rightIn (d.toRight z) :=
            (d.free.overlap (d.toLeft z) (d.toRight z)).mpr ⟨z, rfl, rfl⟩
          exact (heL (d.toLeft z)).trans
            ((congrArg q hz).trans (heR (d.toRight z)).symm)
        obtain ⟨pT, hpT, hpTL, hpTR⟩ :=
          hTgt.exists_EHN_projection pL pR hpL hpR hcompat
        have hrootL : IsFreeAmalgam.RootIsolated d.toLeft tL id eL := by
          intro x z hxz
          exact ⟨z, eL.injective hxz, rfl⟩
        have hrootR : IsFreeAmalgam.RootIsolated d.toRight tR id eR := by
          intro x z hxz
          exact ⟨z, eR.injective hxz, rfl⟩
        let e : Embedding E T :=
          IsFreeAmalgam.functionalLiftEmbedding d.free hTgt
            id Function.injective_id eL eR
            (fun _ => rfl) (fun _ => rfl) hrootL hrootR
        have heLeft : ∀ x, e (d.leftIn x) = jL (eL x) := by
          intro x
          exact IsFreeAmalgam.functionalLiftMap_left d.free hTgt
            id eL eR (fun _ => rfl) (fun _ => rfl) x
        have heRight : ∀ x, e (d.rightIn x) = jR (eR x) := by
          intro x
          exact IsFreeAmalgam.functionalLiftMap_right d.free hTgt
            id eL eR (fun _ => rfl) (fun _ => rfl) x
        have hTree : LooseTreeAmalgam Base
            (FreeAmalgam.Vertex d.common TL TR tL tR) T :=
          LooseTreeAmalgam.glue hTreeL hTreeR tL tR jL jR hTgt
        refine ⟨_, inferInstance, T, hTree, e, pT, hpT, ?_⟩
        intro x
        rcases d.free.covers x with ⟨a, ha⟩ | ⟨b, hb⟩
        · rw [ha, heLeft, hpTL]
          exact heL a
        · rw [hb, heRight, hpTR]
          exact heR b
  letI : Fintype W := Fintype.ofFinite W
  exact aux (Fintype.card W) C p rfl hp hCov

/-- Every irreducible in a loose full-function B-tree already extends to
one of its actual full constituent B-copies. -/
theorem LooseTreeAmalgam.irreduciblesExtendTo
    {Base : Structure L V} {T : Structure L W}
    (hTree : LooseTreeAmalgam Base W T) : IrreduciblesExtendTo Base T := by
  intro S hS hIrr
  obtain ⟨e, he⟩ := hTree.irreducible_contained_in_copy hIrr (inclusion T S hS)
  exact ⟨e, he⟩

/-- A loose tree made from a member of a free-amalgamation class remains
in that class. -/
theorem LooseTreeAmalgam.mem_freeAmalgamationClass
    {K : StructureClass (L := L)} (hK : FreeAmalgamationClass K)
    {Base : Structure L V} {T : Structure L W}
    (hBase : K Base) (hTree : LooseTreeAmalgam Base W T) : K T := by
  induction hTree with
  | copy e hSurj =>
      let j := (Embedding.id _).factorThroughRange e
        (fun x => by obtain ⟨b, hb⟩ := hSurj x; exact ⟨b, hb.symm⟩)
      exact hK.hereditary hBase j
  | glue hL hR fL fR iL iR hfree ihL ihR =>
      exact hK.free ihL ihR hfree

/-- Functional final extension, with a weak projection and loose full-tree
local targets. This requires projected coverage, not a strict-tree oracle. -/
theorem ProjectsIrreduciblesInto.completeRamsey_loose
    {A : Structure L U} {Base : Structure L V}
    {C : Structure L W} {D : Structure L P}
    [Finite V] [Finite W] {p : W → P} {κ : Type*}
    (hCov : ProjectsIrreduciblesInto Base C D p)
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (hArrow : Arrow A Base C κ) :
    ∃ (Y : Type v) (_ : Finite Y) (T : Structure L Y),
      Arrow A Base T κ ∧ LooseTreeAmalgam Base Y T ∧
      IrreduciblesExtendTo Base T ∧
      ∃ q : Y → P, T.IsEHNHomomorphismEmbedding D q := by
  obtain ⟨Y, hY, T, hTree, e, q, hq, he⟩ := hCov.projectedLooseCompletion hp
  refine ⟨Y, hY, T, ?_, hTree, hTree.irreduciblesExtendTo, q, hq⟩
  intro χ
  obtain ⟨f, hf⟩ := hArrow (fun g => χ (e.comp g))
  refine ⟨e.comp f, ?_⟩
  intro g₁ g₂
  exact hf g₁ g₂

end StructuralRamsey.Structure
