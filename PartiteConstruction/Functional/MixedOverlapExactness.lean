import PartiteConstruction.Functional.HistoryTreeCompletion

/-! # Exact functional lifting across mixed free amalgams

For set-valued functions, root isolation is exactly the overlap-reflection
condition needed to prevent leakage into the target gluing root.  When the
overlap labels are injective and the two side maps are full embeddings, the
compatible functional lift is therefore itself a full embedding.

Function fibres need no separate reflection argument: the previously proved
functional lift is already a full homomorphism.  The only extra work here is
injectivity and reflection of relation symbols.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v

variable {L : Language.{u}}
variable {H E F C G E₂ F₂ T : Type v}
variable {D₁ : Structure L H} {A₁ : Structure L E}
variable {B₁ : Structure L F} {C₁ : Structure L C}
variable {D₂ : Structure L G} {A₂ : Structure L E₂}
variable {B₂ : Structure L F₂} {C₂ : Structure L T}
variable {sA : Embedding D₁ A₁} {sB : Embedding D₁ B₁}
variable {iA : Embedding A₁ C₁} {iB : Embedding B₁ C₁}
variable {tA : Embedding D₂ A₂} {tB : Embedding D₂ B₂}
variable {jA : Embedding A₂ C₂} {jB : Embedding B₂ C₂}

/-- Root isolation on both sides and injectivity of the overlap labels prevent
all collisions of the compatible functional lift. -/
theorem functionalLiftMap_injective_of_rootIsolated
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G) (hq : Function.Injective q)
    (hA : Embedding A₁ A₂) (hB : Embedding B₁ B₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d))
    (hrootA : RootIsolated sA tA q hA)
    (hrootB : RootIsolated sB tB q hB) :
    Function.Injective
      (functionalLiftMap hSrc hTgt q hA hB hcompatA hcompatB) := by
  classical
  intro x y hxy
  let history : List (Set C) := [({x} : Set C)]
  have hHistA :
      ∀ Hset ∈ history, ∀ a a' : E,
        hA a = hA a' → (iA a ∈ Hset ↔ iA a' ∈ Hset) := by
    intro Hset _ a a' haa
    have haa' : a = a' := hA.injective haa
    subst a'
    rfl
  have hHistB :
      ∀ Hset ∈ history, ∀ b b' : F,
        hB b = hB b' → (iB b ∈ Hset ↔ iB b' ∈ Hset) := by
    intro Hset _ b b' hbb
    have hbb' : b = b' := hB.injective hbb
    subst b'
    rfl
  have hsets :
      ∀ Hset ∈ history, ∀ z w : C,
        functionalLiftMap hSrc hTgt q hA hB hcompatA hcompatB z =
            functionalLiftMap hSrc hTgt q hA hB hcompatA hcompatB w →
          (z ∈ Hset ↔ w ∈ Hset) :=
    functionalLiftMap_respectsSourceSets
      hSrc hTgt q hq hA hB hcompatA hcompatB
      hrootA hrootB history hHistA hHistB
  have hmem :=
    hsets ({x} : Set C) (by simp [history]) x y hxy
  have hy : y ∈ ({x} : Set C) := hmem.mp (by simp)
  have hyx : y = x := by simpa using hy
  exact hyx.symm

/-- Compatible side embeddings lift to a full embedding of the source free
amalgam when both sides reflect the target root exactly. -/
noncomputable def functionalLiftEmbedding
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G) (hq : Function.Injective q)
    (hA : Embedding A₁ A₂) (hB : Embedding B₁ B₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d))
    (hrootA : RootIsolated sA tA q hA)
    (hrootB : RootIsolated sB tB q hB) :
    Embedding C₁ C₂ := by
  classical
  let Fmap :=
    functionalLiftMap hSrc hTgt q hA hB hcompatA hcompatB
  have hf :
      C₁.IsHomomorphismEmbedding C₂ Fmap :=
    functionalLiftMap_isHomomorphismEmbedding
      hSrc hTgt q hA hB hcompatA hcompatB
      hA.isHomomorphismEmbedding hB.isHomomorphismEmbedding
      hrootA hrootB
  refine {
    toFun := Fmap
    injective := ?_
    map_rel_iff := ?_
    map_func := hf.1.2
  }
  · exact functionalLiftMap_injective_of_rootIsolated
      hSrc hTgt q hq hA hB hcompatA hcompatB hrootA hrootB
  · intro R x
    constructor
    · intro htarget
      rcases (hTgt.rel_iff R (Fmap ∘ x)).mp htarget with hleft | hright
      · rcases hleft with ⟨y, hy, hFy⟩
        have hexistsA (k : Fin (L.relArity R)) :
            ∃ a : E, x k = iA a := by
          rcases hSrc.covers (x k) with hxA | hxB
          · rcases hxA with ⟨a, hxa⟩
            exact ⟨a, hxa⟩
          · rcases hxB with ⟨b, hxb⟩
            have hEq :
                jB (hB b) = jA (y k) := by
              calc
                jB (hB b) =
                    Fmap (iB b) :=
                  (functionalLiftMap_right hSrc hTgt q hA hB
                    hcompatA hcompatB b).symm
                _ = Fmap (x k) := congrArg Fmap hxb.symm
                _ = jA (y k) := congrFun hFy k
            obtain ⟨g, _hyg, hbg⟩ :=
              (hTgt.overlap (y k) (hB b)).mp hEq.symm
            obtain ⟨d, hbd, _hqd⟩ := hrootB b g hbg
            have hov : iA (sA d) = iB (sB d) :=
              (hSrc.overlap (sA d) (sB d)).mpr ⟨d, rfl, rfl⟩
            exact ⟨sA d,
              hxb.trans ((congrArg iB hbd).trans hov.symm)⟩
        let pre : Fin (L.relArity R) → E :=
          fun k => Classical.choose (hexistsA k)
        have hpre (k : Fin (L.relArity R)) : x k = iA (pre k) :=
          Classical.choose_spec (hexistsA k)
        have hmap : hA ∘ pre = y := by
          funext k
          apply jA.injective
          calc
            jA (hA (pre k)) =
                Fmap (iA (pre k)) :=
              (functionalLiftMap_left hSrc hTgt q hA hB
                hcompatA hcompatB (pre k)).symm
            _ = Fmap (x k) := congrArg Fmap (hpre k).symm
            _ = jA (y k) := congrFun hFy k
        have hArel : A₁.rel R pre := by
          have hy' : A₂.rel R (hA ∘ pre) := by
            rw [hmap]
            exact hy
          exact (hA.map_rel_iff R pre).mp hy'
        exact (hSrc.rel_iff R x).mpr
          (Or.inl ⟨pre, hArel, by
            funext k
            exact hpre k⟩)
      · rcases hright with ⟨y, hy, hFy⟩
        have hexistsB (k : Fin (L.relArity R)) :
            ∃ b : F, x k = iB b := by
          rcases hSrc.covers (x k) with hxA | hxB
          · rcases hxA with ⟨a, hxa⟩
            have hEq :
                jA (hA a) = jB (y k) := by
              calc
                jA (hA a) =
                    Fmap (iA a) :=
                  (functionalLiftMap_left hSrc hTgt q hA hB
                    hcompatA hcompatB a).symm
                _ = Fmap (x k) := congrArg Fmap hxa.symm
                _ = jB (y k) := congrFun hFy k
            obtain ⟨g, hag, _hyg⟩ :=
              (hTgt.overlap (hA a) (y k)).mp hEq
            obtain ⟨d, had, _hqd⟩ := hrootA a g hag
            have hov : iA (sA d) = iB (sB d) :=
              (hSrc.overlap (sA d) (sB d)).mpr ⟨d, rfl, rfl⟩
            exact ⟨sB d,
              hxa.trans ((congrArg iA had).trans hov)⟩
          · rcases hxB with ⟨b, hxb⟩
            exact ⟨b, hxb⟩
        let pre : Fin (L.relArity R) → F :=
          fun k => Classical.choose (hexistsB k)
        have hpre (k : Fin (L.relArity R)) : x k = iB (pre k) :=
          Classical.choose_spec (hexistsB k)
        have hmap : hB ∘ pre = y := by
          funext k
          apply jB.injective
          calc
            jB (hB (pre k)) =
                Fmap (iB (pre k)) :=
              (functionalLiftMap_right hSrc hTgt q hA hB
                hcompatA hcompatB (pre k)).symm
            _ = Fmap (x k) := congrArg Fmap (hpre k).symm
            _ = jB (y k) := congrFun hFy k
        have hBrel : B₁.rel R pre := by
          have hy' : B₂.rel R (hB ∘ pre) := by
            rw [hmap]
            exact hy
          exact (hB.map_rel_iff R pre).mp hy'
        exact (hSrc.rel_iff R x).mpr
          (Or.inr ⟨pre, hBrel, by
            funext k
            exact hpre k⟩)
    · intro hsource
      exact hf.1.1 R x hsource

end StructuralRamsey.Structure.IsFreeAmalgam
