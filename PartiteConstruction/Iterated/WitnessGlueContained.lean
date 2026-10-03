import PartiteConstruction.Iterated.WitnessGlue

/-! # Gluing controlled witnesses over a reducible target overlap

The tree-amalgam definition does not require the common overlap itself to be
irreducible.  It only requires the image of each overlap embedding to lie
inside some irreducible substructure on its side.

The existing `glueControlled` derives this containment from irreducibility
of the target-overlap structure.  For the mixed step under merely irreducible
A, the target overlap is typically a reducible substructure of an A-copy.
This variant accepts the two containment certificates directly.
-/
namespace StructuralRamsey.RelStructure.LocallyTreeLike

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB H E F C G TE TF : Type v}
variable {Control : RelStructure L UA} {Base : RelStructure L VB}
variable {Dsrc : RelStructure L H} {Esrc : RelStructure L E}
variable {Fsrc : RelStructure L F} {Csrc : RelStructure L C}
variable {Gov : RelStructure L G} {ETgt : RelStructure L TE}
variable {FTgt : RelStructure L TF}
variable {sE : Embedding Dsrc Esrc} {sF : Embedding Dsrc Fsrc}
variable {iE : Embedding Esrc Csrc} {iF : Embedding Fsrc Csrc}
variable {tE : Embedding Gov ETgt} {tF : Embedding Gov FTgt}

/-- Glue two controlled tree witnesses when the (possibly reducible) target
overlap is known to lie inside irreducible substructures on both sides. -/
theorem glueControlled_of_contained
    (hControl : Control.Irreducible)
    (hSrc : IsFreeAmalgam sE sF iE iF)
    (hTreeE : TreeAmalgam Base TE ETgt)
    (hTreeF : TreeAmalgam Base TF FTgt)
    (hcE : tE.ContainedInIrreducible)
    (hcF : tF.ContainedInIrreducible)
    (q : H → G)
    (hE : E → TE) (hF : F → TF)
    (hcompatE : ∀ d, hE (sE d) = tE (q d))
    (hcompatF : ∀ d, hF (sF d) = tF (q d))
    (hhE : Esrc.IsHomomorphismEmbedding ETgt hE)
    (hhF : Fsrc.IsHomomorphismEmbedding FTgt hF)
    (ctrlE : ∀ α : Embedding Control Esrc,
      ∃ α' : Embedding Control ETgt,
        ∀ a : UA, ∃ a' : UA, hE (α a) = α' a')
    (ctrlF : ∀ α : Embedding Control Fsrc,
      ∃ α' : Embedding Control FTgt,
        ∀ a : UA, ∃ a' : UA, hF (α a) = α' a') :
    ∃ (T : Type v) (Target : RelStructure L T),
      TreeAmalgam Base T Target ∧
      ∃ f : C → T,
        Csrc.IsHomomorphismEmbedding Target f ∧
        ∀ α : Embedding Control Csrc,
          ∃ α' : Embedding Control Target,
            ∀ a : UA, ∃ a' : UA, f (α a) = α' a' := by
  classical
  let Target := FreeAmalgam.amalgam Gov ETgt FTgt tE tF
  let jE := FreeAmalgam.leftEmbedding Gov ETgt FTgt tE tF
  let jF := FreeAmalgam.rightEmbedding Gov ETgt FTgt tE tF
  have hTree :
      TreeAmalgam Base
        (FreeAmalgam.Vertex Gov ETgt FTgt tE tF) Target :=
    FreeAmalgam.treeAmalgam Gov ETgt FTgt tE tF Base
      hTreeE hTreeF hcE hcF
  have hTgt :
      IsFreeAmalgam tE tF jE jF :=
    FreeAmalgam.isFreeAmalgam Gov ETgt FTgt tE tF
  let f : C → FreeAmalgam.Vertex Gov ETgt FTgt tE tF :=
    IsFreeAmalgam.liftMap hSrc hTgt q hE hF hcompatE hcompatF
  have hf : Csrc.IsHomomorphismEmbedding Target f :=
    IsFreeAmalgam.liftMap_isHomomorphismEmbedding
      hSrc hTgt q hE hF hcompatE hcompatF hhE hhF
  refine ⟨FreeAmalgam.Vertex Gov ETgt FTgt tE tF, Target, hTree,
    f, hf, ?_⟩
  intro α
  let S : Set C := Set.range α
  have hS : (Csrc.induce S).Irreducible :=
    hControl.range_embedding α
  rcases hSrc.irreducible_side S hS with hleft | hright
  · have he : ∀ a : UA, ∃ x : E, α a = iE x := by
      intro a
      exact hleft ⟨α a, ⟨a, rfl⟩⟩
    let αE : Embedding Control Esrc :=
      α.factorThroughRange iE he
    obtain ⟨αT, hαT⟩ := ctrlE αE
    let α' : Embedding Control Target := jE.comp αT
    refine ⟨α', ?_⟩
    intro a
    obtain ⟨a', ha'⟩ := hαT a
    refine ⟨a', ?_⟩
    have hea := Classical.choose_spec (he a)
    change f (α a) = jE (αT a')
    calc
      f (α a) = f (iE (αE a)) := congrArg f hea
      _ = jE (hE (αE a)) :=
        IsFreeAmalgam.liftMap_left hSrc hTgt q hE hF
          hcompatE hcompatF (αE a)
      _ = jE (αT a') := congrArg jE ha'
  · have he : ∀ a : UA, ∃ x : F, α a = iF x := by
      intro a
      exact hright ⟨α a, ⟨a, rfl⟩⟩
    let αF : Embedding Control Fsrc :=
      α.factorThroughRange iF he
    obtain ⟨αT, hαT⟩ := ctrlF αF
    let α' : Embedding Control Target := jF.comp αT
    refine ⟨α', ?_⟩
    intro a
    obtain ⟨a', ha'⟩ := hαT a
    refine ⟨a', ?_⟩
    have hea := Classical.choose_spec (he a)
    change f (α a) = jF (αT a')
    calc
      f (α a) = f (iF (αF a)) := congrArg f hea
      _ = jF (hF (αF a)) :=
        IsFreeAmalgam.liftMap_right hSrc hTgt q hE hF
          hcompatE hcompatF (αF a)
      _ = jF (αT a') := congrArg jF ha'

end StructuralRamsey.RelStructure.LocallyTreeLike
