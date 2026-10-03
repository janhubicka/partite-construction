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

/-- Relative completion over a common quotient of the source overlap.
The compatibility map q need not be injective or relation-reflecting; the
target overlap Q itself is embedded on each side.  This is the form naturally
produced by a partite projection on a reducible source overlap. -/
structure QuotientRelativeTreeCompletion
    {K : Type v} (Q : RelStructure L K)
    (q : H → K)
    (Base : RelStructure L VB)
    (s : Embedding G Esrc) where
  TargetType : Type v
  target : RelStructure L TargetType
  tree : TreeAmalgam Base TargetType target
  map : E → TargetType
  mapHE : Esrc.IsHomomorphismEmbedding target map
  boundary : Embedding Q target
  agrees : ∀ x : H, map (s x) = boundary (q x)
  contained : boundary.ContainedInIrreducible

namespace QuotientRelativeTreeCompletion

variable {K : Type v} {Q : RelStructure L K} {q : H → K}
variable {sE : Embedding G Esrc} {sF : Embedding G Fsrc}
variable {iE : Embedding Esrc Csrc} {iF : Embedding Fsrc Csrc}

/-- Package quotient-boundary witness data. -/
def mkOfBoundary
    {Y : Type v} {T : RelStructure L Y}
    (hTree : TreeAmalgam Base Y T)
    (f : E → Y)
    (hf : Esrc.IsHomomorphismEmbedding T f)
    (b : Embedding Q T)
    (hagrees : ∀ x : H, f (sE x) = b (q x))
    (hcontained : b.ContainedInIrreducible) :
    QuotientRelativeTreeCompletion Q q Base sE where
  TargetType := Y
  target := T
  tree := hTree
  map := f
  mapHE := hf
  boundary := b
  agrees := hagrees
  contained := hcontained

/-- Two side completions through the same quotient overlap glue to a tree
completion of the source free amalgam. -/
theorem glue
    (hSrc : IsFreeAmalgam sE sF iE iF)
    (hE : QuotientRelativeTreeCompletion Q q Base sE)
    (hF : QuotientRelativeTreeCompletion Q q Base sF) :
    HasTreeCompletion Base Csrc := by
  classical
  let Target :=
    FreeAmalgam.amalgam Q hE.target hF.target
      hE.boundary hF.boundary
  let jE :=
    FreeAmalgam.leftEmbedding Q hE.target hF.target
      hE.boundary hF.boundary
  let jF :=
    FreeAmalgam.rightEmbedding Q hE.target hF.target
      hE.boundary hF.boundary
  have hTree :
      TreeAmalgam Base
        (FreeAmalgam.Vertex Q hE.target hF.target
          hE.boundary hF.boundary)
        Target :=
    FreeAmalgam.treeAmalgam
      Q hE.target hF.target hE.boundary hF.boundary Base
      hE.tree hF.tree hE.contained hF.contained
  have hTgt :
      IsFreeAmalgam hE.boundary hF.boundary jE jF :=
    FreeAmalgam.isFreeAmalgam
      Q hE.target hF.target hE.boundary hF.boundary
  let f : C →
      FreeAmalgam.Vertex Q hE.target hF.target
        hE.boundary hF.boundary :=
    IsFreeAmalgam.liftMap
      hSrc hTgt q hE.map hF.map hE.agrees hF.agrees
  have hf : Csrc.IsHomomorphismEmbedding Target f :=
    IsFreeAmalgam.liftMap_isHomomorphismEmbedding
      hSrc hTgt q hE.map hF.map hE.agrees hF.agrees
      hE.mapHE hF.mapHE
  exact ⟨_, Target, hTree, f, hf⟩

end QuotientRelativeTreeCompletion
end StructuralRamsey.RelStructure
