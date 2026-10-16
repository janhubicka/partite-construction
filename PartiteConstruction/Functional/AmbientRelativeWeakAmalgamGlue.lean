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


/-- Compatible ambient-relative weak functional HEs on the exact weak
side subsets of a FULL functional free amalgam combine to a single
ambient-relative weak HE of the WHOLE original source on S.

This is the exact weak functional analogue of EHN projection gluing:
positive relations/function incidences hold on every weak tuple,
while complete fibres are required only when every output of the
original ambient operation lies inside S. Full ambient irreducible
source pieces localize in one side, so full target embeddings survive.

The side target maps must ALREADY agree on their exact weak common
root. This theorem does not incorrectly derive compatibility from
independent strict B-tree completions. -/
theorem ambientRelativeWeakHE_glue
    {Root : Structure L H} {Left : Structure L E}
    {Right : Structure L F} {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (S : Set C) (Target : Structure L Y)
    (fL : (iL ⁻¹' S) → Y) (fR : (iR ⁻¹' S) → Y)
    (hL : IsAmbientRelativeWeakHE Left (iL ⁻¹' S) Target fL)
    (hR : IsAmbientRelativeWeakHE Right (iR ⁻¹' S) Target fR)
    (hAgree : ∀ (d : H)
      (hdL : iL (sL d) ∈ S) (hdR : iR (sR d) ∈ S),
      fL ⟨sL d, hdL⟩ = fR ⟨sR d, hdR⟩) :
    ∃ f : S → Y,
      IsAmbientRelativeWeakHE Whole S Target f ∧
      (∀ a : iL ⁻¹' S, f ⟨iL a.1, a.2⟩ = fL a) ∧
      (∀ b : iR ⁻¹' S, f ⟨iR b.1, b.2⟩ = fR b) := by
  classical
  obtain ⟨f, hfL, hfR⟩ :=
    hFree.exists_weakMap_of_compatible S fL fR hAgree
  have hWeak : (Whole.weakInduce S).IsWeakHomomorphism Target f := by
    constructor
    · intro R x hx
      rcases (hFree.rel_iff R (Subtype.val ∘ x)).mp hx with
          ⟨a, ha, hxa⟩ | ⟨a, ha, hxa⟩
      · have haS : ∀ i, iL (a i) ∈ S := by
          intro i
          change (iL ∘ a) i ∈ S
          rw [← congrFun hxa i]
          exact (x i).2
        let xs : Fin (L.relArity R) → iL ⁻¹' S :=
          fun i => ⟨a i, haS i⟩
        have hEq : f ∘ x = fL ∘ xs := by
          funext i
          have hxi : x i = (⟨iL (a i), haS i⟩ : S) := by
            apply Subtype.ext
            exact congrFun hxa i
          change f (x i) = fL (xs i)
          rw [hxi]
          exact hfL ⟨a i, haS i⟩
        rw [hEq]
        exact hL.1.1.1 R xs ha
      · have haS : ∀ i, iR (a i) ∈ S := by
          intro i
          change (iR ∘ a) i ∈ S
          rw [← congrFun hxa i]
          exact (x i).2
        let xs : Fin (L.relArity R) → iR ⁻¹' S :=
          fun i => ⟨a i, haS i⟩
        have hEq : f ∘ x = fR ∘ xs := by
          funext i
          have hxi : x i = (⟨iR (a i), haS i⟩ : S) := by
            apply Subtype.ext
            exact congrFun hxa i
          change f (x i) = fR (xs i)
          rw [hxi]
          exact hfR ⟨a i, haS i⟩
        rw [hEq]
        exact hR.1.1.1 R xs ha
    · intro Func x y hy
      rcases (hFree.func_iff Func (Subtype.val ∘ x) y.1).mp hy with
          ⟨a, b, hb, hxa, hyb⟩ |
          ⟨a, b, hb, hxa, hyb⟩
      · have haS : ∀ i, iL (a i) ∈ S := by
          intro i
          change (iL ∘ a) i ∈ S
          rw [← congrFun hxa i]
          exact (x i).2
        have hbS : iL b ∈ S := by
          rw [← hyb]
          exact y.2
        let xs : Fin (L.funcArity Func) → iL ⁻¹' S :=
          fun i => ⟨a i, haS i⟩
        let ys : iL ⁻¹' S := ⟨b, hbS⟩
        have hEq : f ∘ x = fL ∘ xs := by
          funext i
          have hxi : x i = (⟨iL (a i), haS i⟩ : S) := by
            apply Subtype.ext
            exact congrFun hxa i
          change f (x i) = fL (xs i)
          rw [hxi]
          exact hfL ⟨a i, haS i⟩
        have hyEq : f y = fL ys := by
          have hY : y = (⟨iL b, hbS⟩ : S) := by
            apply Subtype.ext
            exact hyb
          rw [hY]
          exact hfL ys
        rw [hEq, hyEq]
        exact hL.1.1.2 Func xs ys hb
      · have haS : ∀ i, iR (a i) ∈ S := by
          intro i
          change (iR ∘ a) i ∈ S
          rw [← congrFun hxa i]
          exact (x i).2
        have hbS : iR b ∈ S := by
          rw [← hyb]
          exact y.2
        let xs : Fin (L.funcArity Func) → iR ⁻¹' S :=
          fun i => ⟨a i, haS i⟩
        let ys : iR ⁻¹' S := ⟨b, hbS⟩
        have hEq : f ∘ x = fR ∘ xs := by
          funext i
          have hxi : x i = (⟨iR (a i), haS i⟩ : S) := by
            apply Subtype.ext
            exact congrFun hxa i
          change f (x i) = fR (xs i)
          rw [hxi]
          exact hfR ⟨a i, haS i⟩
        have hyEq : f y = fR ys := by
          have hY : y = (⟨iR b, hbS⟩ : S) := by
            apply Subtype.ext
            exact hyb
          rw [hY]
          exact hfR ys
        rw [hEq, hyEq]
        exact hR.1.1.2 Func xs ys hb
  have hExact : ∀ Func (x : Fin (L.funcArity Func) → S),
      (Whole.func Func (Subtype.val ∘ x)).Nonempty →
      (∀ y, y ∈ Whole.func Func (Subtype.val ∘ x) → y ∈ S) →
      imageSet f ((Whole.weakInduce S).func Func x) =
        Target.func Func (f ∘ x) := by
    intro Func x hNonempty hAll
    obtain ⟨y, hy⟩ := hNonempty
    rcases (hFree.func_iff Func (Subtype.val ∘ x) y).mp hy with
        ⟨a, b, hb, hxa, _hyb⟩ |
        ⟨a, b, hb, hxa, _hyb⟩
    · have haS : ∀ i, iL (a i) ∈ S := by
        intro i
        change (iL ∘ a) i ∈ S
        rw [← congrFun hxa i]
        exact (x i).2
      let xs : Fin (L.funcArity Func) → iL ⁻¹' S :=
        fun i => ⟨a i, haS i⟩
      have hAllL : ∀ t, t ∈ Left.func Func a → t ∈ iL ⁻¹' S := by
        intro t ht
        have htWhole : iL t ∈ Whole.func Func (iL ∘ a) := by
          rw [← iL.map_func Func a]
          exact ⟨t, ht, rfl⟩
        apply hAll (iL t)
        rw [hxa]
        exact htWhole
      have hTargetL := hL.1.2 Func xs (show (Left.func Func a).Nonempty
        from ⟨b, hb⟩) hAllL
      have hEq : f ∘ x = fL ∘ xs := by
        funext i
        have hxi : x i = (⟨iL (a i), haS i⟩ : S) := by
          apply Subtype.ext
          exact congrFun hxa i
        change f (x i) = fL (xs i)
        rw [hxi]
        exact hfL ⟨a i, haS i⟩
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hWeak.2 Func x w hw
      · intro hz
        have hzL : z ∈ Target.func Func (fL ∘ xs) := by
          rw [← hEq]
          exact hz
        rw [← hTargetL] at hzL
        obtain ⟨w, hw, hwz⟩ := hzL
        let u : S := ⟨iL w.1, w.2⟩
        have hu : u ∈ (Whole.weakInduce S).func Func x := by
          change iL w.1 ∈ Whole.func Func (Subtype.val ∘ x)
          rw [hxa, ← iL.map_func Func a]
          exact ⟨w.1, hw, rfl⟩
        refine ⟨u, hu, ?_⟩
        calc
          f u = fL w := hfL w
          _ = z := hwz
    · have haS : ∀ i, iR (a i) ∈ S := by
        intro i
        change (iR ∘ a) i ∈ S
        rw [← congrFun hxa i]
        exact (x i).2
      let xs : Fin (L.funcArity Func) → iR ⁻¹' S :=
        fun i => ⟨a i, haS i⟩
      have hAllR : ∀ t, t ∈ Right.func Func a → t ∈ iR ⁻¹' S := by
        intro t ht
        have htWhole : iR t ∈ Whole.func Func (iR ∘ a) := by
          rw [← iR.map_func Func a]
          exact ⟨t, ht, rfl⟩
        apply hAll (iR t)
        rw [hxa]
        exact htWhole
      have hTargetR := hR.1.2 Func xs (show (Right.func Func a).Nonempty
        from ⟨b, hb⟩) hAllR
      have hEq : f ∘ x = fR ∘ xs := by
        funext i
        have hxi : x i = (⟨iR (a i), haS i⟩ : S) := by
          apply Subtype.ext
          exact congrFun hxa i
        change f (x i) = fR (xs i)
        rw [hxi]
        exact hfR ⟨a i, haS i⟩
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hWeak.2 Func x w hw
      · intro hz
        have hzR : z ∈ Target.func Func (fR ∘ xs) := by
          rw [← hEq]
          exact hz
        rw [← hTargetR] at hzR
        obtain ⟨w, hw, hwz⟩ := hzR
        let u : S := ⟨iR w.1, w.2⟩
        have hu : u ∈ (Whole.weakInduce S).func Func x := by
          change iR w.1 ∈ Whole.func Func (Subtype.val ∘ x)
          rw [hxa, ← iR.map_func Func a]
          exact ⟨w.1, hw, rfl⟩
        refine ⟨u, hu, ?_⟩
        calc
          f u = fR w := hfR w
          _ = z := hwz
  have hProtect : ∀ {X : Type v} (Test : Structure L X),
      Test.Irreducible → ∀ (e : Embedding Test Whole)
      (he : ∀ x, e x ∈ S),
      ∃ g : Embedding Test Target,
        ∀ x, g x = f ⟨e x, he x⟩ := by
    intro X Test hIrr e he
    rcases hIrr hFree e with hOnL | hOnR
    · choose lift hLift using hOnL
      let eL : Embedding Test Left :=
        e.factorWithMap iL lift hLift
      have hInto : ∀ x, eL x ∈ iL ⁻¹' S := by
        intro x
        change iL (lift x) ∈ S
        rw [← hLift x]
        exact he x
      obtain ⟨g, hg⟩ := hL.2 Test hIrr eL hInto
      refine ⟨g, ?_⟩
      intro x
      calc
        g x = fL ⟨eL x, hInto x⟩ := hg x
        _ = f ⟨e x, he x⟩ := by
          have hx : (⟨e x, he x⟩ : S) =
              ⟨iL (eL x), hInto x⟩ := by
            apply Subtype.ext
            exact hLift x
          rw [hx]
          exact (hfL ⟨eL x, hInto x⟩).symm
    · choose lift hLift using hOnR
      let eR : Embedding Test Right :=
        e.factorWithMap iR lift hLift
      have hInto : ∀ x, eR x ∈ iR ⁻¹' S := by
        intro x
        change iR (lift x) ∈ S
        rw [← hLift x]
        exact he x
      obtain ⟨g, hg⟩ := hR.2 Test hIrr eR hInto
      refine ⟨g, ?_⟩
      intro x
      calc
        g x = fR ⟨eR x, hInto x⟩ := hg x
        _ = f ⟨e x, he x⟩ := by
          have hx : (⟨e x, he x⟩ : S) =
              ⟨iR (eR x), hInto x⟩ := by
            apply Subtype.ext
            exact hLift x
          rw [hx]
          exact (hfR ⟨eR x, hInto x⟩).symm
  exact ⟨f, ⟨⟨hWeak, hExact⟩, hProtect⟩, hfL, hfR⟩

end StructuralRamsey.Structure.IsFreeAmalgam
