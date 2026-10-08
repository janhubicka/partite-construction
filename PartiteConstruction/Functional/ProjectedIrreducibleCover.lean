import PartiteConstruction.Functional.WeakAttachment
import PartiteConstruction.Structure.GeneratedWeakHomImage

/-! # Projected irreducible coverage in the original functional argument

Every full irreducible of a picture must project into a prescribed full
B-copy in the original witness D. This is weaker than saying that it already
extends to a B-copy inside the picture, and is exactly the input needed by
the final extension step in the published proof.

The closed hull below is used only to localize an irreducible weak image.
No bounded weak vertex test is enlarged, and no local rank is charged to it.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V W X P : Type v}

/-- Every irreducible full substructure has its projected vertices inside
some full copy of Base in D. -/
def ProjectsIrreduciblesInto
    (Base : Structure L V) (C : Structure L W) (D : Structure L P)
    (p : W → P) : Prop :=
  ∀ {Y : Type v} (E : Structure L Y), E.Irreducible →
    ∀ e : Embedding E C,
      ∃ beta : Embedding Base D,
        ∀ x : Y, ∃ b : V, p (e x) = beta b

namespace ProjectsIrreduciblesInto

variable {Base : Structure L V} {C : Structure L W} {D : Structure L P}
variable {p : W → P}

/-- One placed Base-copy satisfies projected coverage. -/
theorem base (beta : Embedding Base D) :
    ProjectsIrreduciblesInto Base Base D beta := by
  intro Y E hE e
  exact ⟨beta, fun x => ⟨e x, rfl⟩⟩

/-- Changing a map pointwise does not change the coverage assertion. -/
theorem congr (h : ProjectsIrreduciblesInto Base C D p)
    {q : W → P} (heq : ∀ x, q x = p x) :
    ProjectsIrreduciblesInto Base C D q := by
  intro Y E hE e
  obtain ⟨beta, hb⟩ := h E hE e
  refine ⟨beta, ?_⟩
  intro x
  obtain ⟨b, hxb⟩ := hb x
  exact ⟨b, (heq (e x)).trans hxb⟩

/-- Coverage pulls back even through a weak functional homomorphism.
The closed hull of the weak image of an irreducible is irreducible. -/
theorem precomp_weak
    (h : ProjectsIrreduciblesInto Base C D p)
    {C' : Structure L X} {q : X → W}
    (hq : C'.IsWeakHomomorphism C q) :
    ProjectsIrreduciblesInto Base C' D (p ∘ q) := by
  intro Y E hE e
  let f : Y → W := q ∘ e
  have hf : E.IsWeakHomomorphism C f := hq.comp e.isWeakHomomorphism
  let S := C.functionClosure (Set.range f)
  have hS : C.IsClosed S := C.functionClosure_isClosed (Set.range f)
  let H := C.induce S hS
  have hH : H.Irreducible := hE.functionClosure_weakImage hf
  let inc : Embedding H C := inclusion C S hS
  obtain ⟨beta, hb⟩ := h H hH inc
  refine ⟨beta, ?_⟩
  intro x
  have hx : f x ∈ S := C.subset_functionClosure (Set.range f) ⟨x, rfl⟩
  exact hb ⟨f x, hx⟩

/-- Projected coverage is preserved by full free gluing. -/
theorem of_freeAmalgam
    {H E F Z : Type v}
    {Root : Structure L H} {Left : Structure L E}
    {Right : Structure L F} {Whole : Structure L Z}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hfree : IsFreeAmalgam sL sR iL iR)
    {pL : E → P} {pR : F → P} {q : Z → P}
    (hL : ProjectsIrreduciblesInto Base Left D pL)
    (hR : ProjectsIrreduciblesInto Base Right D pR)
    (hqL : ∀ x, q (iL x) = pL x)
    (hqR : ∀ x, q (iR x) = pR x) :
    ProjectsIrreduciblesInto Base Whole D q := by
  intro Y E0 hE0 e
  rcases hE0 hfree e with hleft | hright
  · choose f hf using hleft
    let eL := e.factorWithMap iL f hf
    obtain ⟨beta, hb⟩ := hL E0 hE0 eL
    refine ⟨beta, ?_⟩
    intro x
    obtain ⟨b, hxb⟩ := hb x
    exact ⟨b, (congrArg q (hf x)).trans ((hqL (f x)).trans hxb)⟩
  · choose f hf using hright
    let eR := e.factorWithMap iR f hf
    obtain ⟨beta, hb⟩ := hR E0 hE0 eR
    refine ⟨beta, ?_⟩
    intro x
    obtain ⟨b, hxb⟩ := hb x
    exact ⟨b, (congrArg q (hf x)).trans ((hqR (f x)).trans hxb)⟩

end ProjectsIrreduciblesInto

/-- Compatible weak EHN maps from the two sides define a weak EHN map
from their full free amalgam. No full-domain reflection is imposed. -/
theorem IsFreeAmalgam.exists_EHN_projection
    {H E F Z : Type v}
    {Root : Structure L H} {Left : Structure L E}
    {Right : Structure L F} {Whole : Structure L Z}
    {D : Structure L P}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hfree : IsFreeAmalgam sL sR iL iR)
    (pL : E → P) (pR : F → P)
    (hL : Left.IsEHNHomomorphismEmbedding D pL)
    (hR : Right.IsEHNHomomorphismEmbedding D pR)
    (hcompat : ∀ d, pL (sL d) = pR (sR d)) :
    ∃ q : Z → P,
      Whole.IsEHNHomomorphismEmbedding D q ∧
      (∀ x, q (iL x) = pL x) ∧ (∀ x, q (iR x) = pR x) := by
  classical
  have hex (z : Z) : ∃ t : P,
      (∀ a, z = iL a → t = pL a) ∧
      (∀ b, z = iR b → t = pR b) := by
    rcases hfree.covers z with ⟨a, ha⟩ | ⟨b, hb⟩
    · refine ⟨pL a, ?_, ?_⟩
      · intro a' ha'
        exact congrArg pL (iL.injective (ha.symm.trans ha'))
      · intro b hb
        obtain ⟨d, hdL, hdR⟩ := (hfree.overlap a b).mp (ha.symm.trans hb)
        rw [hdL, hdR]
        exact hcompat d
    · refine ⟨pR b, ?_, ?_⟩
      · intro a ha
        obtain ⟨d, hdL, hdR⟩ := (hfree.overlap a b).mp (ha.symm.trans hb)
        rw [hdL, hdR]
        exact (hcompat d).symm
      · intro b' hb'
        exact congrArg pR (iR.injective (hb.symm.trans hb'))
  let q : Z → P := fun z => Classical.choose (hex z)
  have hqL : ∀ a, q (iL a) = pL a := by
    intro a
    exact (Classical.choose_spec (hex (iL a))).1 a rfl
  have hqR : ∀ b, q (iR b) = pR b := by
    intro b
    exact (Classical.choose_spec (hex (iR b))).2 b rfl
  exact ⟨q, IsEHNHomomorphismEmbedding.of_freeAmalgam hfree hL hR hqL hqR,
    hqL, hqR⟩

end StructuralRamsey.Structure
