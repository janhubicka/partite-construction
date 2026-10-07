import PartiteConstruction.Functional.HistoryTreeCompletion
import PartiteConstruction.Functional.ClosedGeneratorRank
import PartiteConstruction.Functional.WitnessGlue

/-! # Root-isolated functional witnesses from source histories

For functions it is not enough that a side witness agree with a target root:
a point outside the source overlap must not leak into that root.  The combined
history invariant already contains exactly the required bookkeeping.  We take
the function-closure of the side together with the whole ambient root and
record the root range as one source-history set.

The closure is paid for by generator rank, while irreducibility of the whole
root turns the homomorphism-embedding on that root into an actual embedding.
-/

namespace StructuralRamsey.Structure.FunctionalHistoryTreeLike

universe u v

variable {L : Language.{u}}
variable {U P VB H E K X : Type v}
variable {A : Structure L U}
variable {D : Structure L P}
variable {Base : Structure L VB}
variable {Core : Structure L X}
variable {Root : Structure L H}
variable {Side : Structure L E}
variable {Overlap : Structure L K}
variable {p : X → P}

/-- A finite embedded side together with a whole irreducible ambient root has
a tree witness whose target root is exact for a prescribed source overlap.

The hypotheses `hcompatSrc` and `hreflectSrc` say that the displayed
overlap is exactly the intersection of the side with the ambient root inside
`Core`. -/
theorem rootedWitness
    [Finite H] [Finite E] [Finite X]
    (hRoot : Root.Irreducible)
    (eRoot : Embedding Root Core)
    (eSide : Embedding Side Core)
    (s : Embedding Overlap Side)
    (q : K → H)
    (hcompatSrc : ∀ z, eSide (s z) = eRoot (q z))
    (hreflectSrc :
      ∀ x d, eSide x = eRoot d →
        ∃ z : K, x = s z ∧ q z = d)
    (n : ℕ)
    (hSideCard : Nat.card E ≤ n)
    (hCore :
      FunctionalHistoryTreeLike
        (A := A) (D := D) (C := Core) (Base := Base)
        p (n + Nat.card H)) :
    ∃ (Y : Type v) (T : Structure L Y),
      TreeAmalgam Base Y T ∧
      ∃ fSide : E → Y,
        Side.IsHomomorphismEmbedding T fSide ∧
        ∃ tRoot : Embedding Root T,
          (∀ z, fSide (s z) = tRoot (q z)) ∧
          IsFreeAmalgam.RootIsolated s tRoot q fSide := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype E := Fintype.ofFinite E

  let G : Finset X :=
    (Finset.univ.image eSide) ∪ (Finset.univ.image eRoot)
  let Hset : Set X := Core.functionClosure (↑G : Set X)
  let Hull : Structure L Hset :=
    Core.induce Hset (Core.functionClosure_isClosed (↑G : Set X))
  let inc : Embedding Hull Core :=
    inclusion Core Hset (Core.functionClosure_isClosed (↑G : Set X))

  have hSideRange : ∀ x : E, ∃ z : Hset, eSide x = inc z := by
    intro x
    have hxG : eSide x ∈ G := by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    have hxH : eSide x ∈ Hset :=
      Core.subset_functionClosure (↑G : Set X) (by
        simpa using hxG)
    exact ⟨⟨eSide x, hxH⟩, rfl⟩

  have hRootRange : ∀ d : H, ∃ z : Hset, eRoot d = inc z := by
    intro d
    have hdG : eRoot d ∈ G := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩
    have hdH : eRoot d ∈ Hset :=
      Core.subset_functionClosure (↑G : Set X) (by
        simpa using hdG)
    exact ⟨⟨eRoot d, hdH⟩, rfl⟩

  let iSide : Embedding Side Hull :=
    eSide.factorThroughClosedRange inc hSideRange
  let iRoot : Embedding Root Hull :=
    eRoot.factorThroughClosedRange inc hRootRange

  have hGcard : G.card ≤ n + Nat.card H := by
    calc
      G.card ≤
          (Finset.univ.image eSide).card +
            (Finset.univ.image eRoot).card :=
        Finset.card_union_le _ _
      _ ≤ Fintype.card E + Fintype.card H := by
        exact Nat.add_le_add
          (by
            simpa using
              (Finset.card_image_le
                (s := (Finset.univ : Finset E)) (f := eSide)))
          (by
            simpa using
              (Finset.card_image_le
                (s := (Finset.univ : Finset H)) (f := eRoot)))
      _ ≤ n + Nat.card H := by
        simpa only [Nat.card_eq_fintype_card] using
          Nat.add_le_add_right hSideCard (Nat.card H)

  have hHullGen :
      Hull.GeneratedByAtMost (n + Nat.card H) := by
    have h0 := functionClosure_finset_generatedByAtMost Core G
    exact h0.mono hGcard

  have hHull :
      FunctionalHistoryTreeLike
        (A := A) (D := D) (C := Hull) (Base := Base)
        (p ∘ inc) (n + Nat.card H) :=
    hCore.pullback_embedding inc

  letI : Fintype Hset := Fintype.ofFinite Hset
  let S : Finset Hset := Finset.univ
  have hS : Hull.IsClosed (↑S : Set Hset) := by
    intro F args _ y _
    simp [S]
  let Small := Hull.induce (↑S : Set Hset) hS
  let incSmall : Embedding Small Hull :=
    inclusion Hull (↑S : Set Hset) hS
  let allEmb : Embedding Hull Small :=
    (Embedding.id Hull).factorWithMap incSmall
      (fun x => ⟨x, Finset.mem_univ x⟩)
      (fun _ => rfl)
  have hsurj : Function.Surjective allEmb := by
    intro y
    refine ⟨y.1, ?_⟩
    apply Subtype.ext
    rfl
  have hSmallGen :
      Small.GeneratedByAtMost (n + Nat.card H) :=
    hHullGen.of_surjective_embedding allEmb hsurj

  let rootRange : Set Hset := Set.range iRoot
  obtain ⟨Y, T, hTree, f0, hf0, _hPart, _hProj, hHist⟩ :=
    hHull S hS hSmallGen [] [rootRange]

  let f : Hset → Y := f0 ∘ allEmb
  have hf : Hull.IsHomomorphismEmbedding T f :=
    hf0.comp allEmb.isHomomorphismEmbedding

  obtain ⟨tRoot, htRoot⟩ :=
    hf.2 Root hRoot iRoot

  let fSide : E → Y := f ∘ iSide
  have hfSide : Side.IsHomomorphismEmbedding T fSide :=
    hf.comp iSide.isHomomorphismEmbedding

  have hHistory :
      ∀ x y : Hset, f x = f y →
        (x ∈ rootRange ↔ y ∈ rootRange) := by
    intro x y hxy
    exact hHist rootRange (by simp)
      (allEmb x) (allEmb y) hxy

  have hcompat :
      ∀ z, fSide (s z) = tRoot (q z) := by
    intro z
    calc
      fSide (s z) = f (iSide (s z)) := rfl
      _ = f (iRoot (q z)) := by
        apply congrArg f
        apply inc.injective
        calc
          inc (iSide (s z)) = eSide (s z) :=
            Embedding.factorThroughClosedRange_spec
              eSide inc hSideRange (s z)
          _ = eRoot (q z) := hcompatSrc z
          _ = inc (iRoot (q z)) :=
            (Embedding.factorThroughClosedRange_spec
              eRoot inc hRootRange (q z)).symm
      _ = tRoot (q z) := (htRoot (q z)).symm

  have hroot :
      IsFreeAmalgam.RootIsolated s tRoot q fSide := by
    intro x d hxd
    have heq :
        f (iSide x) = f (iRoot d) := by
      calc
        f (iSide x) = fSide x := rfl
        _ = tRoot d := hxd
        _ = f (iRoot d) := htRoot d
    have hmemRoot : iRoot d ∈ rootRange := ⟨d, rfl⟩
    have hmemSide : iSide x ∈ rootRange :=
      (hHistory (iSide x) (iRoot d) heq).2 hmemRoot
    rcases hmemSide with ⟨d', hd'⟩
    have hsourceEq : eSide x = eRoot d' := by
      calc
        eSide x = inc (iSide x) :=
          (Embedding.factorThroughClosedRange_spec
            eSide inc hSideRange x).symm
        _ = inc (iRoot d') := congrArg inc hd'.symm
        _ = eRoot d' :=
          Embedding.factorThroughClosedRange_spec
            eRoot inc hRootRange d'
    obtain ⟨z, hxz, hqz⟩ := hreflectSrc x d' hsourceEq
    have hdd : d' = d := by
      apply tRoot.injective
      calc
        tRoot d' = f (iRoot d') := htRoot d'
        _ = f (iSide x) := congrArg f hd'
        _ = fSide x := rfl
        _ = tRoot d := hxd
    refine ⟨z, hxz, ?_⟩
    exact hqz.trans hdd

  exact ⟨Y, T, hTree, fSide, hfSide, tRoot, hcompat, hroot⟩

end StructuralRamsey.Structure.FunctionalHistoryTreeLike
