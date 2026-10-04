import PartiteConstruction.Structure.RootedCorrectness

set_option autoImplicit false

/-! # Free amalgamation through the fixed-root reduction

Adjoining the same fixed root to every moving structure preserves concrete free
amalgams.  This is the class-theoretic bridge needed to apply the positive
arity EHN theorem after eliminating constants.
-/
namespace StructuralRamsey.Rooted

open StructuralRamsey Structure

universe u v
variable {L : Language.{u}} {R H E F C : Type v}

/-- A side tuple pulled back from a canonical padded target tuple is itself
canonical. -/
theorem Pattern.side_pad_eq
    {A B : Type v} {S : Structure (language L R) A}
    {T : Structure (language L R) B}
    (e : Structure.Embedding S T)
    (t : Fin n → Sum R B) (h : (Pattern.ofTuple t).HasMoving)
    (x : Fin n → A) (heq : Pattern.pad t h = e ∘ x) :
    let a := Pattern.sumFill (Pattern.ofTuple t) x
    let ha : (Pattern.ofTuple a).HasMoving := by
      rw [Pattern.ofTuple_sumFill]
      exact h
    Pattern.pad a ha = x := by
  dsimp only
  let a := Pattern.sumFill (Pattern.ofTuple t) x
  let ha : (Pattern.ofTuple a).HasMoving := by
    rw [Pattern.ofTuple_sumFill]
    exact h
  have hnormTarget := Pattern.normalize_pad t h
  have hnormX :
      Pattern.normalize (Pattern.ofTuple t) h x = x :=
    Pattern.normalize_eq_self_of_comp
      (Pattern.ofTuple t) h e e.injective (Pattern.pad t h) x
      (hnormTarget.trans heq)
  have hp := Pattern.pad_sumFill (Pattern.ofTuple t) h x
  dsimp only at hp
  exact hp.trans hnormX

/-- Decoding a free amalgam of moving structures gives the free amalgam of
the decoded rooted structures. -/
theorem decode_isFreeAmalgam
    (Root : Structure L R)
    {D : Structure (language L R) H}
    {A : Structure (language L R) E}
    {B : Structure (language L R) F}
    {X : Structure (language L R) C}
    {sA : Structure.Embedding D A} {sB : Structure.Embedding D B}
    {iA : Structure.Embedding A X} {iB : Structure.Embedding B X}
    (hfree : Structure.IsFreeAmalgam sA sB iA iB) :
    Structure.IsFreeAmalgam
      (decodeEmbedding Root sA) (decodeEmbedding Root sB)
      (decodeEmbedding Root iA) (decodeEmbedding Root iB) := by
  classical
  let dsA := decodeEmbedding Root sA
  let dsB := decodeEmbedding Root sB
  let diA := decodeEmbedding Root iA
  let diB := decodeEmbedding Root iB
  constructor
  · intro z
    cases z with
    | inl r =>
        exact Or.inl ⟨Sum.inl r, rfl⟩
    | inr z =>
        rcases hfree.covers z with ⟨a, ha⟩ | ⟨b, hb⟩
        · exact Or.inl ⟨Sum.inr a, congrArg Sum.inr ha⟩
        · exact Or.inr ⟨Sum.inr b, congrArg Sum.inr hb⟩
  · intro a b
    cases a with
    | inl r =>
        cases b with
        | inl s =>
            constructor
            · intro hrs
              have hrs' : r = s := Sum.inl.inj hrs
              subst s
              exact ⟨Sum.inl r, rfl, rfl⟩
            · rintro ⟨d, ha, hb⟩
              cases d with
              | inl q =>
                  have hrq : r = q := by
                    simpa [dsA, decodeEmbedding_apply, sumMap] using ha
                  have hsq : s = q := by
                    simpa [dsB, decodeEmbedding_apply, sumMap] using hb
                  exact congrArg Sum.inl (hrq.trans hsq.symm)
              | inr d =>
                  simp [dsA, dsB, decodeEmbedding_apply, sumMap] at ha
        | inr b =>
            constructor
            · intro h
              cases h
            · rintro ⟨d, ha, hb⟩
              cases d <;>
                simp [dsA, dsB, decodeEmbedding_apply, sumMap] at ha hb
    | inr a =>
        cases b with
        | inl s =>
            constructor
            · intro h
              cases h
            · rintro ⟨d, ha, hb⟩
              cases d <;>
                simp [dsA, dsB, decodeEmbedding_apply, sumMap] at ha hb
        | inr b =>
            constructor
            · intro hab
              have hab' : iA a = iB b := Sum.inr.inj hab
              obtain ⟨d, ha, hb⟩ := (hfree.overlap a b).mp hab'
              exact ⟨Sum.inr d,
                congrArg Sum.inr ha,
                congrArg Sum.inr hb⟩
            · rintro ⟨d, ha, hb⟩
              cases d with
              | inl q =>
                  simp [dsA, dsB, decodeEmbedding_apply, sumMap] at ha
              | inr d =>
                  have ha' : a = sA d := by
                    exact Sum.inr.inj (by
                      simpa [dsA, decodeEmbedding_apply, sumMap] using ha)
                  have hb' : b = sB d := by
                    exact Sum.inr.inj (by
                      simpa [dsB, decodeEmbedding_apply, sumMap] using hb)
                  apply congrArg Sum.inr
                  exact (hfree.overlap a b).mpr ⟨d, ha', hb'⟩
  · intro S z
    constructor
    · intro hz
      by_cases h : (Pattern.ofTuple z).HasMoving
      · have hred :
            X.rel (.base S (Pattern.ofTuple z)) (Pattern.pad z h) := by
          change
            (if h' : (Pattern.ofTuple z).HasMoving then
              X.rel (.base S (Pattern.ofTuple z)) (Pattern.pad z h')
            else Root.rel S (Pattern.rootTuple z h')) at hz
          rw [dite_eq_left h] at hz
          exact hz
        rcases (hfree.rel_iff (.base S (Pattern.ofTuple z))
          (Pattern.pad z h)).mp hred with
          ⟨x, hx, heq⟩ | ⟨x, hx, heq⟩
        · let a := Pattern.sumFill (Pattern.ofTuple z) x
          let ha : (Pattern.ofTuple a).HasMoving := by
            rw [Pattern.ofTuple_sumFill]
            exact h
          have hpad : Pattern.pad a ha = x :=
            Pattern.side_pad_eq iA z h x heq
          have hrel : (decode Root A).rel S a := by
            change
              (if h' : (Pattern.ofTuple a).HasMoving then
                A.rel (.base S (Pattern.ofTuple a)) (Pattern.pad a h')
              else Root.rel S (Pattern.rootTuple a h'))
            rw [dite_eq_left ha, Pattern.ofTuple_sumFill, hpad]
            exact hx
          have hmap :=
            Pattern.sumMap_sumFill_of_pad_eq iA z h x heq
          exact Or.inl ⟨a, hrel, hmap.symm⟩
        · let a := Pattern.sumFill (Pattern.ofTuple z) x
          let ha : (Pattern.ofTuple a).HasMoving := by
            rw [Pattern.ofTuple_sumFill]
            exact h
          have hpad : Pattern.pad a ha = x :=
            Pattern.side_pad_eq iB z h x heq
          have hrel : (decode Root B).rel S a := by
            change
              (if h' : (Pattern.ofTuple a).HasMoving then
                B.rel (.base S (Pattern.ofTuple a)) (Pattern.pad a h')
              else Root.rel S (Pattern.rootTuple a h'))
            rw [dite_eq_left ha, Pattern.ofTuple_sumFill, hpad]
            exact hx
          have hmap :=
            Pattern.sumMap_sumFill_of_pad_eq iB z h x heq
          exact Or.inr ⟨a, hrel, hmap.symm⟩
      · have hroot : Root.rel S (Pattern.rootTuple z h) := by
          change
            (if h' : (Pattern.ofTuple z).HasMoving then
              X.rel (.base S (Pattern.ofTuple z)) (Pattern.pad z h')
            else Root.rel S (Pattern.rootTuple z h')) at hz
          rw [dite_eq_right h] at hz
          exact hz
        let a : Fin (L.relArity S) → Sum R E :=
          Sum.inl ∘ Pattern.rootTuple z h
        have hrel : (decode Root A).rel S a :=
          ((rootEmbedding Root A).map_rel_iff S _).mpr hroot
        refine Or.inl ⟨a, hrel, ?_⟩
        funext j
        have hzj := Pattern.rootTuple_spec z h j
        simpa [a, diA, decodeEmbedding_apply, sumMap] using hzj.symm
    · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact ((decodeEmbedding Root iA).map_rel_iff S a).mpr ha
      · exact ((decodeEmbedding Root iB).map_rel_iff S b).mpr hb
  · intro G x y
    constructor
    · intro hy
      by_cases h : (Pattern.ofTuple x).HasMoving
      · cases y with
        | inl r =>
            have hred :
                X.rel (.output G (Pattern.ofTuple x) r)
                  (Pattern.pad x h) := by
              change
                (if h' : (Pattern.ofTuple x).HasMoving then
                  X.rel (.output G (Pattern.ofTuple x) r)
                    (Pattern.pad x h')
                else r ∈ Root.func G (Pattern.rootTuple x h')) at hy
              rw [dite_eq_left h] at hy
              exact hy
            rcases (hfree.rel_iff (.output G (Pattern.ofTuple x) r)
              (Pattern.pad x h)).mp hred with
              ⟨q, hq, heq⟩ | ⟨q, hq, heq⟩
            · let a := Pattern.sumFill (Pattern.ofTuple x) q
              let ha : (Pattern.ofTuple a).HasMoving := by
                rw [Pattern.ofTuple_sumFill]
                exact h
              have hpad : Pattern.pad a ha = q :=
                Pattern.side_pad_eq iA x h q heq
              have hb : Sum.inl r ∈ (decode Root A).func G a := by
                change
                  (if h' : (Pattern.ofTuple a).HasMoving then
                    A.rel (.output G (Pattern.ofTuple a) r)
                      (Pattern.pad a h')
                  else r ∈ Root.func G (Pattern.rootTuple a h'))
                rw [dite_eq_left ha, Pattern.ofTuple_sumFill, hpad]
                exact hq
              have hmap :=
                Pattern.sumMap_sumFill_of_pad_eq iA x h q heq
              exact Or.inl ⟨a, Sum.inl r, hb, hmap.symm, rfl⟩
            · let a := Pattern.sumFill (Pattern.ofTuple x) q
              let ha : (Pattern.ofTuple a).HasMoving := by
                rw [Pattern.ofTuple_sumFill]
                exact h
              have hpad : Pattern.pad a ha = q :=
                Pattern.side_pad_eq iB x h q heq
              have hb : Sum.inl r ∈ (decode Root B).func G a := by
                change
                  (if h' : (Pattern.ofTuple a).HasMoving then
                    B.rel (.output G (Pattern.ofTuple a) r)
                      (Pattern.pad a h')
                  else r ∈ Root.func G (Pattern.rootTuple a h'))
                rw [dite_eq_left ha, Pattern.ofTuple_sumFill, hpad]
                exact hq
              have hmap :=
                Pattern.sumMap_sumFill_of_pad_eq iB x h q heq
              exact Or.inr ⟨a, Sum.inl r, hb, hmap.symm, rfl⟩
        | inr z =>
            have hred :
                z ∈ X.func ⟨G, Pattern.ofTuple x⟩
                  (Structure.funcTuple (Pattern.pad x h)
                    (Pattern.dummy x h)) := by
              change
                (if h' : (Pattern.ofTuple x).HasMoving then
                  z ∈ X.func ⟨G, Pattern.ofTuple x⟩
                    (Structure.funcTuple (Pattern.pad x h')
                      (Pattern.dummy x h'))
                else False) at hy
              rw [dite_eq_left h] at hy
              exact hy
            rcases (hfree.func_iff ⟨G, Pattern.ofTuple x⟩
              (Structure.funcTuple (Pattern.pad x h)
                (Pattern.dummy x h)) z).mp hred with
              ⟨q, b, hb, hargs, hout⟩ |
              ⟨q, b, hb, hargs, hout⟩
            · let q0 : Fin (L.funcArity G) → E :=
                fun i => q i.castSucc
              let a := Pattern.sumFill (Pattern.ofTuple x) q0
              let ha : (Pattern.ofTuple a).HasMoving := by
                rw [Pattern.ofTuple_sumFill]
                exact h
              have hcanon :
                  Structure.funcTuple (Pattern.pad a ha)
                      (Pattern.dummy a ha) = q :=
                Pattern.funcTuple_preimage_canonical
                  iA iA.injective x h q hargs
              have hside : Sum.inr b ∈ (decode Root A).func G a := by
                change
                  (if h' : (Pattern.ofTuple a).HasMoving then
                    b ∈ A.func ⟨G, Pattern.ofTuple a⟩
                      (Structure.funcTuple (Pattern.pad a h')
                        (Pattern.dummy a h'))
                  else False)
                rw [dite_eq_left ha, Pattern.ofTuple_sumFill, hcanon]
                exact hb
              have hinput :
                  Pattern.pad x h = iA ∘ q0 := by
                funext j
                have hj := congrFun hargs j.castSucc
                simpa [q0, Structure.funcTuple_castSucc] using hj
              have hmap :=
                Pattern.sumMap_sumFill_of_pad_eq iA x h q0 hinput
              exact Or.inl ⟨a, Sum.inr b, hside, hmap.symm,
                congrArg Sum.inr hout⟩
            · let q0 : Fin (L.funcArity G) → F :=
                fun i => q i.castSucc
              let a := Pattern.sumFill (Pattern.ofTuple x) q0
              let ha : (Pattern.ofTuple a).HasMoving := by
                rw [Pattern.ofTuple_sumFill]
                exact h
              have hcanon :
                  Structure.funcTuple (Pattern.pad a ha)
                      (Pattern.dummy a ha) = q :=
                Pattern.funcTuple_preimage_canonical
                  iB iB.injective x h q hargs
              have hside : Sum.inr b ∈ (decode Root B).func G a := by
                change
                  (if h' : (Pattern.ofTuple a).HasMoving then
                    b ∈ B.func ⟨G, Pattern.ofTuple a⟩
                      (Structure.funcTuple (Pattern.pad a h')
                        (Pattern.dummy a h'))
                  else False)
                rw [dite_eq_left ha, Pattern.ofTuple_sumFill, hcanon]
                exact hb
              have hinput :
                  Pattern.pad x h = iB ∘ q0 := by
                funext j
                have hj := congrFun hargs j.castSucc
                simpa [q0, Structure.funcTuple_castSucc] using hj
              have hmap :=
                Pattern.sumMap_sumFill_of_pad_eq iB x h q0 hinput
              exact Or.inr ⟨a, Sum.inr b, hside, hmap.symm,
                congrArg Sum.inr hout⟩
      · cases y with
        | inl r =>
            have hr : r ∈ Root.func G (Pattern.rootTuple x h) := by
              change
                (if h' : (Pattern.ofTuple x).HasMoving then
                  X.rel (.output G (Pattern.ofTuple x) r)
                    (Pattern.pad x h')
                else r ∈ Root.func G (Pattern.rootTuple x h')) at hy
              rw [dite_eq_right h] at hy
              exact hy
            let a : Fin (L.funcArity G) → Sum R E :=
              Sum.inl ∘ Pattern.rootTuple x h
            have hb : Sum.inl r ∈ (decode Root A).func G a := by
              have himg :
                  Sum.inl r ∈ Structure.imageSet (rootEmbedding Root A)
                    (Root.func G (Pattern.rootTuple x h)) :=
                ⟨r, hr, rfl⟩
              rw [(rootEmbedding Root A).map_func G
                (Pattern.rootTuple x h)] at himg
              exact himg
            refine Or.inl ⟨a, Sum.inl r, hb, ?_, rfl⟩
            funext j
            have hxj := Pattern.rootTuple_spec x h j
            simpa [a, diA, decodeEmbedding_apply, sumMap] using hxj.symm
        | inr z =>
            change
              (if h' : (Pattern.ofTuple x).HasMoving then
                z ∈ X.func ⟨G, Pattern.ofTuple x⟩
                  (Structure.funcTuple (Pattern.pad x h')
                    (Pattern.dummy x h'))
              else False) at hy
            rw [dite_eq_right h] at hy
            exact False.elim hy
    · rintro (⟨a, b, hb, rfl, rfl⟩ | ⟨a, b, hb, rfl, rfl⟩)
      · let e := decodeEmbedding Root iA
        have himg :
            e b ∈ Structure.imageSet e ((decode Root A).func G a) :=
          ⟨b, hb, rfl⟩
        rw [e.map_func G a] at himg
        exact himg
      · let e := decodeEmbedding Root iB
        have himg :
            e b ∈ Structure.imageSet e ((decode Root B).func G a) :=
          ⟨b, hb, rfl⟩
        rw [e.map_func G a] at himg
        exact himg

end StructuralRamsey.Rooted
