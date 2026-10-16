import PartiteConstruction.Functional.AmbientRelativeTargetPostcomp
import PartiteConstruction.Functional.WeakFunctionalFreeAmalgam

/-!
# Compatible ambient-relative weak maps glue across FULL functional free amalgams

Let Whole be a genuine full functional free amalgam of Left and Right
over Root, and let S be an ARBITRARY exact weak vertex test.
An ambient-relative weak map of each source side into the SAME genuine
functional target, with compatible values on the exact common weak
root, combines into one ambient-relative weak map of Whole|ᵂS.

* No closure of S, its sides or their root is assumed.
* Function fibres are genuinely SET-VALUED. Positive incidences are
  preserved on any weak subset; complete fibres are preserved when
  ALL ambient outputs survive in S.
* Embedded ambient irreducible source pieces factor through one side
  of the original full free amalgam, so their full target embeddings
  remain protected.
* The source parts may be reused by nonadjacent vertices: NO global
  injectivity of the part projection is assumed.

The lemma is a sound geometric COMBINATION step. It does NOT assert
that arbitrary independently chosen strict B-tree witnesses can be
made to agree on the weak common root: supplying a single compatible
target is precisely the missing maximal-mixed-root task.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {H E F C Y : Type v}

/-- Compatible maps on the exact weak core and side restrictions of a
full functional free amalgam define a unique-on-sides global map of
the tested carrier, with no closure hull or target assumptions. -/
theorem exists_weakMap_of_compatible
    {Root : Structure L H} {Left : Structure L E}
    {Right : Structure L F} {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (S : Set C)
    (fL : (iL ⁻¹' S) → Y) (fR : (iR ⁻¹' S) → Y)
    (hAgree : ∀ (d : H)
      (hdL : iL (sL d) ∈ S) (hdR : iR (sR d) ∈ S),
      fL ⟨sL d, hdL⟩ = fR ⟨sR d, hdR⟩) :
    ∃ f : S → Y,
      (∀ a : iL ⁻¹' S, f ⟨iL a.1, a.2⟩ = fL a) ∧
      (∀ b : iR ⁻¹' S, f ⟨iR b.1, b.2⟩ = fR b) := by
  classical
  have hExist (z : S) :
      ∃ t : Y,
        (∀ (a : E) (ha : iL a ∈ S),
          z.1 = iL a → t = fL ⟨a, ha⟩) ∧
        (∀ (b : F) (hb : iR b ∈ S),
          z.1 = iR b → t = fR ⟨b, hb⟩) := by
    rcases hFree.covers z.1 with ⟨a, hza⟩ | ⟨b, hzb⟩
    · have haS : iL a ∈ S := by
        rw [← hza]
        exact z.2
      refine ⟨fL ⟨a, haS⟩, ?_, ?_⟩
      · intro a' haS' hza'
        have haa' : a = a' :=
          iL.injective (hza.symm.trans hza')
        apply congrArg fL
        apply Subtype.ext
        exact haa'
      · intro b hbS hzb
        obtain ⟨d, hdL, hdR⟩ :=
          (hFree.overlap a b).mp (hza.symm.trans hzb)
        have hdLeft : iL (sL d) ∈ S := by
          rw [← hdL]
          exact haS
        have hdRight : iR (sR d) ∈ S := by
          rw [← hdR]
          exact hbS
        calc
          fL ⟨a, haS⟩ = fL ⟨sL d, hdLeft⟩ := by
            congr 1
            apply Subtype.ext
            exact hdL
          _ = fR ⟨sR d, hdRight⟩ :=
            hAgree d hdLeft hdRight
          _ = fR ⟨b, hbS⟩ := by
            congr 1
            apply Subtype.ext
            exact hdR.symm
    · have hbS : iR b ∈ S := by
        rw [← hzb]
        exact z.2
      refine ⟨fR ⟨b, hbS⟩, ?_, ?_⟩
      · intro a haS hza
        obtain ⟨d, hdL, hdR⟩ :=
          (hFree.overlap a b).mp (hza.symm.trans hzb)
        have hdLeft : iL (sL d) ∈ S := by
          rw [← hdL]
          exact haS
        have hdRight : iR (sR d) ∈ S := by
          rw [← hdR]
          exact hbS
        calc
          fR ⟨b, hbS⟩ = fR ⟨sR d, hdRight⟩ := by
            congr 1
            apply Subtype.ext
            exact hdR
          _ = fL ⟨sL d, hdLeft⟩ :=
            (hAgree d hdLeft hdRight).symm
          _ = fL ⟨a, haS⟩ := by
            congr 1
            apply Subtype.ext
            exact hdL.symm
      · intro b' hbS' hzb'
        have hbb' : b = b' :=
          iR.injective (hzb.symm.trans hzb')
        apply congrArg fR
        apply Subtype.ext
        exact hbb'
  let f : S → Y := fun z => Classical.choose (hExist z)
  have hLf (a : iL ⁻¹' S) :
      f ⟨iL a.1, a.2⟩ = fL a :=
    (Classical.choose_spec (hExist ⟨iL a.1, a.2⟩)).1 a.1 a.2 rfl
  have hRf (b : iR ⁻¹' S) :
      f ⟨iR b.1, b.2⟩ = fR b :=
    (Classical.choose_spec (hExist ⟨iR b.1, b.2⟩)).2 b.1 b.2 rfl
  exact ⟨f, hLf, hRf⟩

end StructuralRamsey.Structure.IsFreeAmalgam
