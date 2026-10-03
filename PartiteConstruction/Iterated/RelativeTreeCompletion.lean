import PartiteConstruction.Iterated.WitnessGlueContained

/-! # Relative tree completions

The mixed Picture step needs more than two unrelated tree completions of its
two sides.  The common source overlap must be preserved by an actual embedded
boundary on both sides.  This file isolates exactly that datum.

A relative tree completion of E over an embedded G -> E is a tree amalgam of
copies of Base together with a homomorphism-embedding of E whose restriction
to G is an ordinary embedding and whose boundary image is contained in an
irreducible target substructure.  Two relative completions over the same
source G glue canonically through a target free amalgam.

No hereditary irreducibility assumption is used.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {VB H E F C : Type v}
variable {Base : RelStructure L VB}
variable {G : RelStructure L H}
variable {Esrc : RelStructure L E}
variable {Fsrc : RelStructure L F}
variable {Csrc : RelStructure L C}

/-- Existence of an ordinary tree completion, forgetting any prescribed
boundary behaviour. -/
def HasTreeCompletion
    (Base : RelStructure L VB) (A : RelStructure L E) : Prop :=
  ∃ (Y : Type v) (T : RelStructure L Y),
    TreeAmalgam Base Y T ∧
    ∃ f : E → Y, A.IsHomomorphismEmbedding T f

/-- A tree completion which preserves a selected source overlap by an actual
embedded boundary. -/
structure RelativeTreeCompletion
    (Base : RelStructure L VB)
    (s : Embedding G Esrc) where
  TargetType : Type v
  target : RelStructure L TargetType
  tree : TreeAmalgam Base TargetType target
  map : E → TargetType
  mapHE : Esrc.IsHomomorphismEmbedding target map
  boundary : Embedding G target
  agrees : ∀ x : H, map (s x) = boundary x
  contained : boundary.ContainedInIrreducible

namespace RelativeTreeCompletion

variable {sE : Embedding G Esrc} {sF : Embedding G Fsrc}
variable {iE : Embedding Esrc Csrc} {iF : Embedding Fsrc Csrc}

/-- Forget the prescribed boundary. -/
theorem hasTreeCompletion
    (h : RelativeTreeCompletion Base sE) :
    HasTreeCompletion Base Esrc :=
  ⟨h.TargetType, h.target, h.tree, h.map, h.mapHE⟩

/-- Package already-constructed witness data as a relative completion. -/
def mkOfBoundary
    {Y : Type v} {T : RelStructure L Y}
    (hTree : TreeAmalgam Base Y T)
    (f : E → Y)
    (hf : Esrc.IsHomomorphismEmbedding T f)
    (b : Embedding G T)
    (hagrees : ∀ x : H, f (sE x) = b x)
    (hcontained : b.ContainedInIrreducible) :
    RelativeTreeCompletion Base sE where
  TargetType := Y
  target := T
  tree := hTree
  map := f
  mapHE := hf
  boundary := b
  agrees := hagrees
  contained := hcontained

/-- Relative completions of the two sides of a free amalgam glue to a tree
completion of the whole source.  The overlap itself may be reducible. -/
theorem glue
    (hSrc : IsFreeAmalgam sE sF iE iF)
    (hE : RelativeTreeCompletion Base sE)
    (hF : RelativeTreeCompletion Base sF) :
    HasTreeCompletion Base Csrc := by
  classical
  let Target :=
    FreeAmalgam.amalgam G hE.target hF.target
      hE.boundary hF.boundary
  let jE :=
    FreeAmalgam.leftEmbedding G hE.target hF.target
      hE.boundary hF.boundary
  let jF :=
    FreeAmalgam.rightEmbedding G hE.target hF.target
      hE.boundary hF.boundary
  have hTree :
      TreeAmalgam Base
        (FreeAmalgam.Vertex G hE.target hF.target
          hE.boundary hF.boundary)
        Target :=
    FreeAmalgam.treeAmalgam
      G hE.target hF.target hE.boundary hF.boundary Base
      hE.tree hF.tree hE.contained hF.contained
  have hTgt :
      IsFreeAmalgam hE.boundary hF.boundary jE jF :=
    FreeAmalgam.isFreeAmalgam
      G hE.target hF.target hE.boundary hF.boundary
  let f : C →
      FreeAmalgam.Vertex G hE.target hF.target
        hE.boundary hF.boundary :=
    IsFreeAmalgam.liftMap
      hSrc hTgt id hE.map hF.map hE.agrees hF.agrees
  have hf : Csrc.IsHomomorphismEmbedding Target f :=
    IsFreeAmalgam.liftMap_isHomomorphismEmbedding
      hSrc hTgt id hE.map hF.map hE.agrees hF.agrees
      hE.mapHE hF.mapHE
  exact ⟨_, Target, hTree, f, hf⟩

end RelativeTreeCompletion
end StructuralRamsey.RelStructure
