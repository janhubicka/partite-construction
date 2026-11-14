import PartiteConstruction.Functional.WeakAmbientACopyTraceRestorationBudget
import PartiteConstruction.Functional.WeakFunctionalFreeAmalgam
import PartiteConstruction.Functional.WeakWitnessRestriction

/-!
# Track D: literal pure-side weak functional completion transport

The English proof was committed FIRST:
docs/track-d-english-bare-pure-weak-transfer-rank-budget-20261114.md

Unlike the stronger ambient-A-copy intersection invariant,
a BARE strict functional weak-tree witness transports from a
FULL source side to a pure tested subset of a larger source.
The proof uses the genuine full inverse of a surjective
weak-induced source embedding, and full ambient function fibres,
not just positive relational edge preservation.

This is independent of any unproved multi-line partial-A
trace extension. The two source weak subsets are LITERAL
inverse images. No source function closure is taken.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {E C Z : Type v}

/-- Transfer an ambient-relative weak functional HE from a full
source side to the SAME literal tested vertices of an ambient
source, provided every tested vertex belongs to that full
source side. Source functions may be arbitrary set-valued and
inputs not in the original domain are NOT reflected.

No new target tree and no full external A-copy mark are assumed. -/
theorem IsAmbientRelativeWeakHE.of_full_pure_side
    {Side : Structure L E} {Whole : Structure L C}
    (i : Embedding Side Whole)
    (S : Set C)
    (hPure : ∀ z : C, z ∈ S → ∃ x : E, z = i x)
    {Target : Structure L Z}
    {fSide : (i ⁻¹' S) → Z}
    (hfSide : IsAmbientRelativeWeakHE
      Side (i ⁻¹' S) Target fSide) :
    ∃ f : S → Z,
      IsAmbientRelativeWeakHE Whole S Target f := by
  classical
  let S0 : Set E := i ⁻¹' S
  let j : Embedding (Side.weakInduce S0) (Whole.weakInduce S) :=
    i.weakRestrictExact S0 S (by intro x; rfl)
  have hSurj : Function.Surjective j := by
    intro z
    obtain ⟨x, hx⟩ := hPure z.1 z.2
    have hxS : x ∈ S0 := by
      change i x ∈ S
      rw [← hx]
      exact z.2
    refine ⟨⟨x, hxS⟩, ?_⟩
    apply Subtype.ext
    exact hx.symm
  have hFactor : ∀ z : S,
      ∃ x : S0,
        (Embedding.id (Whole.weakInduce S)) z = j x := by
    intro z
    obtain ⟨x, hx⟩ := hSurj z
    exact ⟨x, hx.symm⟩
  let inv : Embedding (Whole.weakInduce S) (Side.weakInduce S0) :=
    (Embedding.id (Whole.weakInduce S)).factorThroughClosedRange
      j hFactor
  have hInv (z : S) : i (inv z).1 = z.1 := by
    have hz : j (inv z) = z :=
      Embedding.factorThroughClosedRange_spec
        (Embedding.id (Whole.weakInduce S)) j hFactor z
    exact congrArg Subtype.val hz
  let f : S → Z := fSide ∘ inv
  have hWeak :
      (Whole.weakInduce S).IsWeakHomomorphism Target f :=
    hfSide.1.1.comp inv.isWeakHomomorphism
  have hFibre : ∀ F (xs : Fin (L.funcArity F) → S),
      (Whole.func F (Subtype.val ∘ xs)).Nonempty →
      (∀ y, y ∈ Whole.func F (Subtype.val ∘ xs) → y ∈ S) →
      imageSet f ((Whole.weakInduce S).func F xs) =
        Target.func F (f ∘ xs) := by
    intro F xs hNon hAll
    let ys : Fin (L.funcArity F) → S0 := inv ∘ xs
    let raw : Fin (L.funcArity F) → E := Subtype.val ∘ ys
    have hTuple : i ∘ raw = Subtype.val ∘ xs := by
      funext k
      exact hInv (xs k)
    obtain ⟨z, hz⟩ := hNon
    have hzS : z ∈ S := hAll z hz
    have hzOldWeak :
        inv ⟨z, hzS⟩ ∈
          (Side.weakInduce S0).func F ys := by
      rw [← inv.map_func F xs]
      exact ⟨(⟨z, hzS⟩ : S), hz, rfl⟩
    have hNonOld : (Side.func F raw).Nonempty :=
      ⟨(inv ⟨z, hzS⟩).1, hzOldWeak⟩
    have hAllOld : ∀ y, y ∈ Side.func F raw → y ∈ S0 := by
      intro y hy
      have hyWhole : i y ∈ Whole.func F (i ∘ raw) := by
        rw [← i.map_func F raw]
        exact ⟨y, hy, rfl⟩
      rw [hTuple] at hyWhole
      exact hAll (i y) hyWhole
    have hExact :=
      hfSide.1.2 F ys hNonOld hAllOld
    change imageSet fSide ((Side.weakInduce S0).func F ys) =
      Target.func F (fSide ∘ ys) at hExact
    ext t
    constructor
    · rintro ⟨w, hw, hwt⟩
      have hOldVal : inv w ∈
          (Side.weakInduce S0).func F ys := by
        rw [← inv.map_func F xs]
        exact ⟨w, hw, rfl⟩
      have ht : t ∈
          imageSet fSide ((Side.weakInduce S0).func F ys) :=
        ⟨inv w, hOldVal, hwt⟩
      rw [hExact] at ht
      exact ht
    · intro ht
      have htOld : t ∈ Target.func F (fSide ∘ ys) := ht
      rw [← hExact] at htOld
      obtain ⟨zOld, hzOld, htOldEq⟩ := htOld
      have hOldImg : zOld ∈
          imageSet inv ((Whole.weakInduce S).func F xs) := by
        rw [inv.map_func F xs]
        exact hzOld
      obtain ⟨w, hw, hwEq⟩ := hOldImg
      exact ⟨w, hw, (congrArg fSide hwEq).trans htOldEq⟩
  have hIrred :
      ∀ {X : Type v} (A : Structure L X), A.Irreducible →
        ∀ (e : Embedding A Whole) (he : ∀ x, e x ∈ S),
          ∃ g : Embedding A Target,
            ∀ x, g x = f ⟨e x, he x⟩ := by
    intro X A hA e he
    have hRange : ∀ x : X, ∃ y : E, e x = i y :=
      fun x => hPure (e x) (he x)
    let eSide : Embedding A Side :=
      e.factorThroughClosedRange i hRange
    have hE (x : X) : i (eSide x) = e x :=
      Embedding.factorThroughClosedRange_spec e i hRange x
    have hSideS (x : X) : eSide x ∈ S0 := by
      change i (eSide x) ∈ S
      rw [hE x]
      exact he x
    obtain ⟨g, hg⟩ := hfSide.2 A hA eSide hSideS
    refine ⟨g, ?_⟩
    intro x
    have hSubtype :
        (⟨eSide x, hSideS x⟩ : S0) =
          inv ⟨e x, he x⟩ := by
      apply Subtype.ext
      apply i.injective
      calc
        i (eSide x) = e x := hE x
        _ = i (inv ⟨e x, he x⟩).1 :=
          (hInv ⟨e x, he x⟩).symm
    calc
      g x = fSide ⟨eSide x, hSideS x⟩ := hg x
      _ = f ⟨e x, he x⟩ := congrArg fSide hSubtype
  exact ⟨f, ⟨⟨hWeak, hFibre⟩, hIrred⟩⟩

end StructuralRamsey.Structure
