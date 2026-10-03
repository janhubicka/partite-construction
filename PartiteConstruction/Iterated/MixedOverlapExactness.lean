import PartiteConstruction.Iterated.Glue
import PartiteConstruction.Iterated.MixedOverlapObstruction

/-! # Exactness at a target gluing overlap

Kernel agreement on the source overlap is necessary but not sufficient for
the mixed step.  A side witness can also send a vertex outside the source
overlap into the target overlap at an unrelated overlap point.  Such
"overlap leakage" creates cross-side collisions and can create reflected
relations that were absent in the source.

The exact condition needed by free-amalgam lifting is one-sided reflection of
the target overlap: a side point lands in the target overlap iff it comes from
the corresponding source overlap, with the same overlap label.

Under this condition, compatible induced embeddings of the two source sides
lift to an induced embedding of the whole source free amalgam.
-/
namespace StructuralRamsey.RelStructure.IsFreeAmalgam

universe u v
variable {L : RelLanguage.{u}}
variable {H E F C G E₂ F₂ T : Type v}
variable {D₁ : RelStructure L H} {A₁ : RelStructure L E}
variable {B₁ : RelStructure L F} {C₁ : RelStructure L C}
variable {D₂ : RelStructure L G} {A₂ : RelStructure L E₂}
variable {B₂ : RelStructure L F₂} {C₂ : RelStructure L T}
variable {sA : Embedding D₁ A₁} {sB : Embedding D₁ B₁}
variable {iA : Embedding A₁ C₁} {iB : Embedding B₁ C₁}
variable {tA : Embedding D₂ A₂} {tB : Embedding D₂ B₂}
variable {jA : Embedding A₂ C₂} {jB : Embedding B₂ C₂}

/-- A side embedding reflects membership in the target overlap back to the
source overlap, preserving the overlap coordinate. -/
def ReflectsOverlap
    (q : H → G) (s : Embedding D₁ A₁) (t : Embedding D₂ A₂)
    (h : Embedding A₁ A₂) : Prop :=
  ∀ a g, h a = t g →
    ∃ d : H, a = s d ∧ q d = g

/-- Compatibility through an induced side embedding makes q injective. -/
theorem overlapMap_injective
    (q : H → G) (hA : Embedding A₁ A₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d)) :
    Function.Injective q := by
  intro x y hxy
  apply sA.injective
  apply hA.injective
  rw [hcompatA x, hcompatA y, hxy]

/-- If both side embeddings leak to the same target-overlap point from source
points not identified in the source amalgam, the lifted map is not injective. -/
theorem liftMap_collision_of_overlap_leakage
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G) (hA : E → E₂) (hB : F → F₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d))
    (a : E) (b : F) (g : G)
    (ha : hA a = tA g) (hb : hB b = tB g) :
    liftMap hSrc hTgt q hA hB hcompatA hcompatB (iA a) =
      liftMap hSrc hTgt q hA hB hcompatA hcompatB (iB b) := by
  rw [liftMap_left hSrc hTgt q hA hB hcompatA hcompatB a,
    liftMap_right hSrc hTgt q hA hB hcompatA hcompatB b,
    ha, hb]
  exact (hTgt.overlap (tA g) (tB g)).mpr ⟨g, rfl, rfl⟩

/-- Exact overlap reflection on both sides prevents every cross-side collision
of the lifted map. -/
theorem liftMap_injective_of_reflectsOverlap
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G)
    (hA : Embedding A₁ A₂) (hB : Embedding B₁ B₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d))
    (hexA : ReflectsOverlap q sA tA hA)
    (hexB : ReflectsOverlap q sB tB hB) :
    Function.Injective
      (liftMap hSrc hTgt q hA hB hcompatA hcompatB) := by
  classical
  let Fmap := liftMap hSrc hTgt q hA hB hcompatA hcompatB
  have hqinj : Function.Injective q :=
    overlapMap_injective q hA hcompatA
  intro x y hxy
  rcases hSrc.covers x with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rcases hSrc.covers y with ⟨a', rfl⟩ | ⟨b, rfl⟩
    · apply congrArg iA
      apply hA.injective
      apply jA.injective
      rw [← liftMap_left hSrc hTgt q hA hB hcompatA hcompatB a,
        ← liftMap_left hSrc hTgt q hA hB hcompatA hcompatB a']
      exact hxy
    · have hcross :
          jA (hA a) = jB (hB b) := by
        rw [← liftMap_left hSrc hTgt q hA hB hcompatA hcompatB a,
          ← liftMap_right hSrc hTgt q hA hB hcompatA hcompatB b]
        exact hxy
      obtain ⟨g, hag, hbg⟩ :=
        (hTgt.overlap (hA a) (hB b)).mp hcross
      obtain ⟨da, hda, hqA⟩ := hexA a g hag
      obtain ⟨db, hdb, hqB⟩ := hexB b g hbg
      have hdd : da = db := hqinj (hqA.trans hqB.symm)
      subst db
      exact (hSrc.overlap a b).mpr
        ⟨da, hda, hdb⟩
  · rcases hSrc.covers y with ⟨a, rfl⟩ | ⟨b', rfl⟩
    · symm
      have hcross :
          jA (hA a) = jB (hB b) := by
        rw [← liftMap_left hSrc hTgt q hA hB hcompatA hcompatB a,
          ← liftMap_right hSrc hTgt q hA hB hcompatA hcompatB b]
        exact hxy.symm
      obtain ⟨g, hag, hbg⟩ :=
        (hTgt.overlap (hA a) (hB b)).mp hcross
      obtain ⟨da, hda, hqA⟩ := hexA a g hag
      obtain ⟨db, hdb, hqB⟩ := hexB b g hbg
      have hdd : da = db := hqinj (hqA.trans hqB.symm)
      subst db
      exact (hSrc.overlap a b).mpr
        ⟨da, hda, hdb⟩
    · apply congrArg iB
      apply hB.injective
      apply jB.injective
      rw [← liftMap_right hSrc hTgt q hA hB hcompatA hcompatB b,
        ← liftMap_right hSrc hTgt q hA hB hcompatA hcompatB b']
      exact hxy

/-- Compatible induced embeddings of both sides lift to an induced embedding
of the whole free amalgam when both sides reflect the target overlap exactly. -/
noncomputable def liftEmbedding
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G)
    (hA : Embedding A₁ A₂) (hB : Embedding B₁ B₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d))
    (hexA : ReflectsOverlap q sA tA hA)
    (hexB : ReflectsOverlap q sB tB hB) :
    Embedding C₁ C₂ where
  toFun := liftMap hSrc hTgt q hA hB hcompatA hcompatB
  injective :=
    liftMap_injective_of_reflectsOverlap
      hSrc hTgt q hA hB hcompatA hcompatB hexA hexB
  map_rel_iff := by
    intro R x
    constructor
    · intro htarget
      let Fmap := liftMap hSrc hTgt q hA hB hcompatA hcompatB
      rcases (hTgt.rel_iff R (Fmap ∘ x)).mp htarget with hleft | hright
      · rcases hleft with ⟨y, hy, hFy⟩
        have hexistsA (k : Fin (L.arity R)) :
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
                  (liftMap_right hSrc hTgt q hA hB
                    hcompatA hcompatB b).symm
                _ = Fmap (x k) := congrArg Fmap hxb.symm
                _ = jA (y k) := congrFun hFy k
            obtain ⟨g, _hyg, hbg⟩ :=
              (hTgt.overlap (y k) (hB b)).mp hEq.symm
            obtain ⟨d, hbd, _hqd⟩ := hexB b g hbg
            have hov : iA (sA d) = iB (sB d) :=
              (hSrc.overlap (sA d) (sB d)).mpr ⟨d, rfl, rfl⟩
            exact ⟨sA d,
              hxb.trans ((congrArg iB hbd).trans hov.symm)⟩
        let pre : Fin (L.arity R) → E :=
          fun k => Classical.choose (hexistsA k)
        have hpre (k : Fin (L.arity R)) : x k = iA (pre k) :=
          Classical.choose_spec (hexistsA k)
        have hmap : hA ∘ pre = y := by
          funext k
          apply jA.injective
          calc
            jA (hA (pre k)) =
                Fmap (iA (pre k)) :=
              (liftMap_left hSrc hTgt q hA hB
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
        have hexistsB (k : Fin (L.arity R)) :
            ∃ b : F, x k = iB b := by
          rcases hSrc.covers (x k) with hxA | hxB
          · rcases hxA with ⟨a, hxa⟩
            have hEq :
                jA (hA a) = jB (y k) := by
              calc
                jA (hA a) =
                    Fmap (iA a) :=
                  (liftMap_left hSrc hTgt q hA hB
                    hcompatA hcompatB a).symm
                _ = Fmap (x k) := congrArg Fmap hxa.symm
                _ = jB (y k) := congrFun hFy k
            obtain ⟨g, hag, _hyg⟩ :=
              (hTgt.overlap (hA a) (y k)).mp hEq
            obtain ⟨d, had, _hqd⟩ := hexA a g hag
            have hov : iA (sA d) = iB (sB d) :=
              (hSrc.overlap (sA d) (sB d)).mpr ⟨d, rfl, rfl⟩
            exact ⟨sB d,
              hxa.trans ((congrArg iA had).trans hov)⟩
          · rcases hxB with ⟨b, hxb⟩
            exact ⟨b, hxb⟩
        let pre : Fin (L.arity R) → F :=
          fun k => Classical.choose (hexistsB k)
        have hpre (k : Fin (L.arity R)) : x k = iB (pre k) :=
          Classical.choose_spec (hexistsB k)
        have hmap : hB ∘ pre = y := by
          funext k
          apply jB.injective
          calc
            jB (hB (pre k)) =
                Fmap (iB (pre k)) :=
              (liftMap_right hSrc hTgt q hA hB
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
      exact
        (liftMap_isHomomorphismEmbedding
          hSrc hTgt q hA hB hcompatA hcompatB
          hA.isHomomorphismEmbedding hB.isHomomorphismEmbedding).map_rel
          hsource

end StructuralRamsey.RelStructure.IsFreeAmalgam
