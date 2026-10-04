import PartiteConstruction.Functional.FullFreeAmalgam
import PartiteConstruction.Functional.ClosedLocalTreeCompletion

/-! # Gluing full functional tree-completion witnesses

The relational mixed-glue proof needs only homomorphism-embeddings.  For
set-valued functions, fibre-surjectivity can fail unless the common target root
has no points unaccounted for by the source overlap.

The hypothesis `Surjective q` records exactly the additional information
available in the closed-substructure argument: the common target root is the
image of the whole source overlap.  Injectivity of the two side witnesses then
prevents a point outside the source overlap from leaking into the target root.
Under these two hypotheses the compatible lift is again a full
homomorphism-embedding.
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

/-- Candidate value of the compatible lift. -/
def FunctionalLiftOutput
    (iA : Embedding A₁ C₁) (iB : Embedding B₁ C₁)
    (jA : Embedding A₂ C₂) (jB : Embedding B₂ C₂)
    (hA : E → E₂) (hB : F → F₂) (z : C) (w : T) : Prop :=
  (∃ a : E, z = iA a ∧ w = jA (hA a)) ∨
  (∃ b : F, z = iB b ∧ w = jB (hB b))

theorem functionalLiftOutput_existsUnique
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G) (hA : E → E₂) (hB : F → F₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d))
    (z : C) :
    ∃! w : T, FunctionalLiftOutput iA iB jA jB hA hB z w := by
  classical
  rcases hSrc.covers z with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · refine ⟨jA (hA a), Or.inl ⟨a, rfl, rfl⟩, ?_⟩
    intro w hw
    rcases hw with ⟨a', ha', rfl⟩ | ⟨b, hb, rfl⟩
    · have haa : a = a' := iA.injective ha'
      subst a'
      rfl
    · obtain ⟨d, had, hbd⟩ := (hSrc.overlap a b).mp hb
      subst a
      subst b
      rw [hcompatA d, hcompatB d]
      exact ((hTgt.overlap (tA (q d)) (tB (q d))).mpr
        ⟨q d, rfl, rfl⟩).symm
  · refine ⟨jB (hB b), Or.inr ⟨b, rfl, rfl⟩, ?_⟩
    intro w hw
    rcases hw with ⟨a, ha, rfl⟩ | ⟨b', hb', rfl⟩
    · obtain ⟨d, had, hbd⟩ := (hSrc.overlap a b).mp ha.symm
      subst a
      subst b
      rw [hcompatA d, hcompatB d]
      exact (hTgt.overlap (tA (q d)) (tB (q d))).mpr
        ⟨q d, rfl, rfl⟩
    · have hbb : b = b' := iB.injective hb'
      subst b'
      rfl

noncomputable def functionalLiftMap
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G) (hA : E → E₂) (hB : F → F₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d)) :
    C → T :=
  fun z => Classical.choose
    (functionalLiftOutput_existsUnique hSrc hTgt q hA hB
      hcompatA hcompatB z)

theorem functionalLiftMap_left
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G) (hA : E → E₂) (hB : F → F₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d))
    (a : E) :
    functionalLiftMap hSrc hTgt q hA hB hcompatA hcompatB (iA a) =
      jA (hA a) := by
  let huniq :=
    functionalLiftOutput_existsUnique hSrc hTgt q hA hB
      hcompatA hcompatB (iA a)
  exact huniq.unique
    (Classical.choose_spec huniq).1
    (Or.inl ⟨a, rfl, rfl⟩)

theorem functionalLiftMap_right
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G) (hA : E → E₂) (hB : F → F₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d))
    (b : F) :
    functionalLiftMap hSrc hTgt q hA hB hcompatA hcompatB (iB b) =
      jB (hB b) := by
  let huniq :=
    functionalLiftOutput_existsUnique hSrc hTgt q hA hB
      hcompatA hcompatB (iB b)
  exact huniq.unique
    (Classical.choose_spec huniq).1
    (Or.inr ⟨b, rfl, rfl⟩)

/-- Compatible full homomorphism-embeddings lift across free amalgams when
the common target root is exhausted by the source overlap and both side maps
are injective. -/
theorem functionalLiftMap_isHomomorphismEmbedding
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G) (hq : Function.Surjective q)
    (hA : E → E₂) (hB : F → F₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d))
    (hhA : A₁.IsHomomorphismEmbedding A₂ hA)
    (hhB : B₁.IsHomomorphismEmbedding B₂ hB)
    (hinjA : Function.Injective hA)
    (hinjB : Function.Injective hB) :
    C₁.IsHomomorphismEmbedding C₂
      (functionalLiftMap hSrc hTgt q hA hB hcompatA hcompatB) := by
  classical
  let Fmap :=
    functionalLiftMap hSrc hTgt q hA hB hcompatA hcompatB
  have hhom : C₁.IsHomomorphism C₂ Fmap := by
    constructor
    · intro R x hx
      rcases (hSrc.rel_iff R x).mp hx with
        ⟨a, ha, hxa⟩ | ⟨b, hb, hxb⟩
      · have hside : A₂.rel R (hA ∘ a) :=
          hhA.1.1 R a ha
        have htgt : C₂.rel R (jA ∘ (hA ∘ a)) :=
          (jA.map_rel_iff R (hA ∘ a)).2 hside
        convert htgt using 1
        funext k
        have hxk := congrFun hxa k
        change Fmap (x k) = jA (hA (a k))
        rw [hxk]
        exact functionalLiftMap_left hSrc hTgt q hA hB
          hcompatA hcompatB (a k)
      · have hside : B₂.rel R (hB ∘ b) :=
          hhB.1.1 R b hb
        have htgt : C₂.rel R (jB ∘ (hB ∘ b)) :=
          (jB.map_rel_iff R (hB ∘ b)).2 hside
        convert htgt using 1
        funext k
        have hxk := congrFun hxb k
        change Fmap (x k) = jB (hB (b k))
        rw [hxk]
        exact functionalLiftMap_right hSrc hTgt q hA hB
          hcompatA hcompatB (b k)
    · intro F0 x
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases (hSrc.func_iff F0 x z).mp hz with
          ⟨a, b, hb, hxa, hzb⟩ |
          ⟨a, b, hb, hxa, hzb⟩
        · apply (hTgt.func_iff F0 (Fmap ∘ x) (Fmap z)).mpr
          refine Or.inl ⟨hA ∘ a, hA b, ?_, ?_, ?_⟩
          · have hm :
                hA b ∈ imageSet hA (A₁.func F0 a) :=
              ⟨b, hb, rfl⟩
            rw [hhA.1.2 F0 a] at hm
            exact hm
          · funext k
            have hxk := congrFun hxa k
            change Fmap (x k) = jA (hA (a k))
            rw [hxk]
            exact functionalLiftMap_left hSrc hTgt q hA hB
              hcompatA hcompatB (a k)
          · change Fmap z = jA (hA b)
            rw [hzb]
            exact functionalLiftMap_left hSrc hTgt q hA hB
              hcompatA hcompatB b
        · apply (hTgt.func_iff F0 (Fmap ∘ x) (Fmap z)).mpr
          refine Or.inr ⟨hB ∘ a, hB b, ?_, ?_, ?_⟩
          · have hm :
                hB b ∈ imageSet hB (B₁.func F0 a) :=
              ⟨b, hb, rfl⟩
            rw [hhB.1.2 F0 a] at hm
            exact hm
          · funext k
            have hxk := congrFun hxa k
            change Fmap (x k) = jB (hB (a k))
            rw [hxk]
            exact functionalLiftMap_right hSrc hTgt q hA hB
              hcompatA hcompatB (a k)
          · change Fmap z = jB (hB b)
            rw [hzb]
            exact functionalLiftMap_right hSrc hTgt q hA hB
              hcompatA hcompatB b
      · intro hy
        rcases (hTgt.func_iff F0 (Fmap ∘ x) y).mp hy with
          ⟨a₂, b₂, hb₂, hargs, hout⟩ |
          ⟨a₂, b₂, hb₂, hargs, hout⟩
        · have hex :
              ∀ k, ∃ a : E, x k = iA a ∧ hA a = a₂ k := by
            intro k
            rcases hSrc.covers (x k) with ⟨a, hxa⟩ | ⟨b, hxb⟩
            · refine ⟨a, hxa, ?_⟩
              apply jA.injective
              calc
                jA (hA a) = Fmap (iA a) :=
                  (functionalLiftMap_left hSrc hTgt q hA hB
                    hcompatA hcompatB a).symm
                _ = Fmap (x k) := congrArg Fmap hxa.symm
                _ = jA (a₂ k) := congrFun hargs k
            · have hcross :
                  jA (a₂ k) = jB (hB b) := by
                calc
                  jA (a₂ k) = Fmap (x k) := (congrFun hargs k).symm
                  _ = Fmap (iB b) := congrArg Fmap hxb
                  _ = jB (hB b) :=
                    functionalLiftMap_right hSrc hTgt q hA hB
                      hcompatA hcompatB b
              obtain ⟨g, hag, hbg⟩ :=
                (hTgt.overlap (a₂ k) (hB b)).mp hcross
              obtain ⟨d, hqd⟩ := hq g
              have hbEq : b = sB d := by
                apply hinjB
                calc
                  hB b = tB g := hbg
                  _ = tB (q d) := congrArg tB hqd.symm
                  _ = hB (sB d) := (hcompatB d).symm
              have hxleft : x k = iA (sA d) := by
                calc
                  x k = iB b := hxb
                  _ = iB (sB d) := congrArg iB hbEq
                  _ = iA (sA d) :=
                    ((hSrc.overlap (sA d) (sB d)).mpr
                      ⟨d, rfl, rfl⟩).symm
              refine ⟨sA d, hxleft, ?_⟩
              calc
                hA (sA d) = tA (q d) := hcompatA d
                _ = tA g := congrArg tA hqd
                _ = a₂ k := hag.symm
          choose a ha hha using hex
          have hAargs : hA ∘ a = a₂ := funext hha
          have hb₂' : b₂ ∈ A₂.func F0 (hA ∘ a) := by
            rw [hAargs]
            exact hb₂
          rw [← hhA.1.2 F0 a] at hb₂'
          rcases hb₂' with ⟨b, hb, hbb⟩
          refine ⟨iA b, ?_, ?_⟩
          · apply (hSrc.func_iff F0 x (iA b)).mpr
            refine Or.inl ⟨a, b, hb, ?_, rfl⟩
            funext k
            exact ha k
          · calc
              Fmap (iA b) = jA (hA b) :=
                functionalLiftMap_left hSrc hTgt q hA hB
                  hcompatA hcompatB b
              _ = jA b₂ := congrArg jA hbb
              _ = y := hout.symm
        · have hex :
              ∀ k, ∃ b : F, x k = iB b ∧ hB b = a₂ k := by
            intro k
            rcases hSrc.covers (x k) with ⟨a, hxa⟩ | ⟨b, hxb⟩
            · have hcross :
                  jA (hA a) = jB (a₂ k) := by
                calc
                  jA (hA a) =
                      Fmap (iA a) :=
                    (functionalLiftMap_left hSrc hTgt q hA hB
                      hcompatA hcompatB a).symm
                  _ = Fmap (x k) := congrArg Fmap hxa.symm
                  _ = jB (a₂ k) := congrFun hargs k
              obtain ⟨g, hag, hbg⟩ :=
                (hTgt.overlap (hA a) (a₂ k)).mp hcross
              obtain ⟨d, hqd⟩ := hq g
              have haEq : a = sA d := by
                apply hinjA
                calc
                  hA a = tA g := hag
                  _ = tA (q d) := congrArg tA hqd.symm
                  _ = hA (sA d) := (hcompatA d).symm
              have hxright : x k = iB (sB d) := by
                calc
                  x k = iA a := hxa
                  _ = iA (sA d) := congrArg iA haEq
                  _ = iB (sB d) :=
                    (hSrc.overlap (sA d) (sB d)).mpr
                      ⟨d, rfl, rfl⟩
              refine ⟨sB d, hxright, ?_⟩
              calc
                hB (sB d) = tB (q d) := hcompatB d
                _ = tB g := congrArg tB hqd
                _ = a₂ k := hbg.symm
            · refine ⟨b, hxb, ?_⟩
              apply jB.injective
              calc
                jB (hB b) = Fmap (iB b) :=
                  (functionalLiftMap_right hSrc hTgt q hA hB
                    hcompatA hcompatB b).symm
                _ = Fmap (x k) := congrArg Fmap hxb.symm
                _ = jB (a₂ k) := congrFun hargs k
          choose a ha hha using hex
          have hBargs : hB ∘ a = a₂ := funext hha
          have hb₂' : b₂ ∈ B₂.func F0 (hB ∘ a) := by
            rw [hBargs]
            exact hb₂
          rw [← hhB.1.2 F0 a] at hb₂'
          rcases hb₂' with ⟨b, hb, hbb⟩
          refine ⟨iB b, ?_, ?_⟩
          · apply (hSrc.func_iff F0 x (iB b)).mpr
            refine Or.inr ⟨a, b, hb, ?_, rfl⟩
            funext k
            exact ha k
          · calc
              Fmap (iB b) = jB (hB b) :=
                functionalLiftMap_right hSrc hTgt q hA hB
                  hcompatA hcompatB b
              _ = jB b₂ := congrArg jB hbb
              _ = y := hout.symm
  refine ⟨hhom, ?_⟩
  intro X R hR e
  rcases hR hSrc e with hleft | hright
  · let eA : Embedding R A₁ :=
      e.factorThroughRange iA hleft
    obtain ⟨gA, hgA⟩ := hhA.2 R hR eA
    refine ⟨jA.comp gA, ?_⟩
    intro x
    have hex := Classical.choose_spec (hleft x)
    change jA (gA x) = Fmap (e x)
    calc
      jA (gA x) = jA (hA (eA x)) := congrArg jA (hgA x)
      _ = Fmap (iA (eA x)) :=
        (functionalLiftMap_left hSrc hTgt q hA hB
          hcompatA hcompatB (eA x)).symm
      _ = Fmap (e x) := congrArg Fmap hex.symm
  · let eB : Embedding R B₁ :=
      e.factorThroughRange iB hright
    obtain ⟨gB, hgB⟩ := hhB.2 R hR eB
    refine ⟨jB.comp gB, ?_⟩
    intro x
    have hex := Classical.choose_spec (hright x)
    change jB (gB x) = Fmap (e x)
    calc
      jB (gB x) = jB (hB (eB x)) := congrArg jB (hgB x)
      _ = Fmap (iB (eB x)) :=
        (functionalLiftMap_right hSrc hTgt q hA hB
          hcompatA hcompatB (eB x)).symm
      _ = Fmap (e x) := congrArg Fmap hex.symm

/-- The same hypotheses also make the compatible lift injective. -/
theorem functionalLiftMap_injective
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G) (hq : Function.Surjective q)
    (hA : E → E₂) (hB : F → F₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d))
    (hinjA : Function.Injective hA)
    (hinjB : Function.Injective hB) :
    Function.Injective
      (functionalLiftMap hSrc hTgt q hA hB hcompatA hcompatB) := by
  classical
  let Fmap :=
    functionalLiftMap hSrc hTgt q hA hB hcompatA hcompatB
  intro x y hxy
  rcases hSrc.covers x with ⟨a, hxa⟩ | ⟨b, hxb⟩
  · rcases hSrc.covers y with ⟨a', hya⟩ | ⟨b, hyb⟩
    · apply hxa.trans
      apply congrArg iA
      apply hinjA
      apply jA.injective
      calc
        jA (hA a) = Fmap (iA a) :=
          (functionalLiftMap_left hSrc hTgt q hA hB
            hcompatA hcompatB a).symm
        _ = Fmap x := congrArg Fmap hxa.symm
        _ = Fmap y := hxy
        _ = Fmap (iA a') := congrArg Fmap hya
        _ = jA (hA a') :=
          functionalLiftMap_left hSrc hTgt q hA hB
            hcompatA hcompatB a'
    · have hcross : jA (hA a) = jB (hB b) := by
        calc
          jA (hA a) = Fmap (iA a) :=
            (functionalLiftMap_left hSrc hTgt q hA hB
              hcompatA hcompatB a).symm
          _ = Fmap x := congrArg Fmap hxa.symm
          _ = Fmap y := hxy
          _ = Fmap (iB b) := congrArg Fmap hyb
          _ = jB (hB b) :=
            functionalLiftMap_right hSrc hTgt q hA hB
              hcompatA hcompatB b
      obtain ⟨g, hag, hbg⟩ :=
        (hTgt.overlap (hA a) (hB b)).mp hcross
      obtain ⟨d, hqd⟩ := hq g
      have ha : a = sA d := by
        apply hinjA
        calc
          hA a = tA g := hag
          _ = tA (q d) := congrArg tA hqd.symm
          _ = hA (sA d) := (hcompatA d).symm
      have hb : b = sB d := by
        apply hinjB
        calc
          hB b = tB g := hbg
          _ = tB (q d) := congrArg tB hqd.symm
          _ = hB (sB d) := (hcompatB d).symm
      calc
        x = iA a := hxa
        _ = iA (sA d) := congrArg iA ha
        _ = iB (sB d) :=
          (hSrc.overlap (sA d) (sB d)).mpr ⟨d, rfl, rfl⟩
        _ = iB b := congrArg iB hb.symm
        _ = y := hyb.symm
  · rcases hSrc.covers y with ⟨a, hya⟩ | ⟨b', hyb⟩
    · symm
      apply functionalLiftMap_injective hSrc hTgt q hq hA hB
        hcompatA hcompatB hinjA hinjB
      exact hxy.symm
    · apply hxb.trans
      apply congrArg iB
      apply hinjB
      apply jB.injective
      calc
        jB (hB b) = Fmap (iB b) :=
          (functionalLiftMap_right hSrc hTgt q hA hB
            hcompatA hcompatB b).symm
        _ = Fmap x := congrArg Fmap hxb.symm
        _ = Fmap y := hxy
        _ = Fmap (iB b') := congrArg Fmap hyb
        _ = jB (hB b') :=
          functionalLiftMap_right hSrc hTgt q hA hB
            hcompatA hcompatB b'

end StructuralRamsey.Structure.IsFreeAmalgam

namespace StructuralRamsey.Structure.LocallyClosedTreeCompletable

universe u v
variable {L : Language.{u}}
variable {UA VB H E F C G TE TF : Type v}
variable {Control : Structure L UA} {Base : Structure L VB}
variable {Dsrc : Structure L H} {Esrc : Structure L E}
variable {Fsrc : Structure L F} {Csrc : Structure L C}
variable {Gov : Structure L G} {ETgt : Structure L TE}
variable {FTgt : Structure L TF}
variable {sE : Embedding Dsrc Esrc} {sF : Embedding Dsrc Fsrc}
variable {iE : Embedding Esrc Csrc} {iF : Embedding Fsrc Csrc}
variable {tE : Embedding Gov ETgt} {tF : Embedding Gov FTgt}

/-- Glue two injective functional tree-completion witnesses over a target root
which is exactly covered by the source overlap. -/
theorem glueExactRoot
    (hSrc : IsFreeAmalgam sE sF iE iF)
    (hTreeE : TreeAmalgam Base TE ETgt)
    (hTreeF : TreeAmalgam Base TF FTgt)
    (hcE : tE.ContainedInIrreducible)
    (hcF : tF.ContainedInIrreducible)
    (q : H → G) (hq : Function.Surjective q)
    (hE : E → TE) (hF : F → TF)
    (hcompatE : ∀ d, hE (sE d) = tE (q d))
    (hcompatF : ∀ d, hF (sF d) = tF (q d))
    (hhE : Esrc.IsHomomorphismEmbedding ETgt hE)
    (hhF : Fsrc.IsHomomorphismEmbedding FTgt hF)
    (hinjE : Function.Injective hE)
    (hinjF : Function.Injective hF) :
    ∃ (T : Type v) (Target : Structure L T),
      TreeAmalgam Base T Target ∧
      ∃ f : C → T,
        Csrc.IsHomomorphismEmbedding Target f ∧
        Function.Injective f := by
  classical
  let Target := FreeAmalgam.amalgam Gov ETgt FTgt tE tF
  let jE := FreeAmalgam.leftEmbedding Gov ETgt FTgt tE tF
  let jF := FreeAmalgam.rightEmbedding Gov ETgt FTgt tE tF
  have hTgt : IsFreeAmalgam tE tF jE jF :=
    FreeAmalgam.isFreeAmalgam Gov ETgt FTgt tE tF
  have hTree :
      TreeAmalgam Base
        (FreeAmalgam.Vertex Gov ETgt FTgt tE tF) Target :=
    FreeAmalgam.treeAmalgam Gov ETgt FTgt tE tF Base
      hTreeE hTreeF hcE hcF
  let f : C → FreeAmalgam.Vertex Gov ETgt FTgt tE tF :=
    IsFreeAmalgam.functionalLiftMap hSrc hTgt q hE hF
      hcompatE hcompatF
  have hf : Csrc.IsHomomorphismEmbedding Target f :=
    IsFreeAmalgam.functionalLiftMap_isHomomorphismEmbedding
      hSrc hTgt q hq hE hF hcompatE hcompatF
      hhE hhF hinjE hinjF
  have hinj : Function.Injective f :=
    IsFreeAmalgam.functionalLiftMap_injective
      hSrc hTgt q hq hE hF hcompatE hcompatF
      hinjE hinjF
  exact ⟨_, Target, hTree, f, hf, hinj⟩

end StructuralRamsey.Structure.LocallyClosedTreeCompletable
