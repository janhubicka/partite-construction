import PartiteConstruction.Functional.OutputPartNativeHJPowerIso
import PartiteConstruction.Functional.OutputPartEmbeddingEquiv
import PartiteConstruction.HalesJewett.Finite

/-!
# Canonical output-part singletonization commutes with ACTUAL HJ lines

For the TRUE native functional Hales--Jewett Picture, full
partite letter embeddings e:(transversal A)↪B translate
bijectively to full singletonized letters, without changing
their underlying vertex maps. A HJ line is translated by
mapping every constant letter through this full embedding
equivalence while preserving EVERY parameter coordinate.

On all actual vertices, the HJ line map commutes with the
canonical positive-power full partite isomorphism:
  splitPowerVertex(lineMap W x) = lineMap (splitLine W) x.

Thus the ACTUAL full functional HJ line embedding, after
singletonization and power transport, agrees exactly with
the line embedding of the split system. This retains all
genuine multivalued source function outputs, part labels,
literal weak vertex sets, and HJ line/root geometry.

Only genuine FULL original partite projections are used.
Nothing asserts a globally full EHN/original-partial map,
or compatible strict target-root completions for arbitrary
different lines.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure
open StructuralRamsey.HalesJewett
open SuccessorTree

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}

/-- The fixed singleton-function control for original functional A.
It has precisely the same part carrier P as A. -/
abbrev outputSplitControl (A : Structure L P) :
    Structure (L.outputPartIndexed P) P :=
  ((transversal A).splitOutputParts).toStructure

/-- Each ORIGINAL full HJ letter canonically becomes a
full part-preserving letter of the SINGLETONIZED systems,
with the very same vertex map P→V. -/
def splitLetter (A : Structure L P) (B : System L P V)
    (e : Letter A B) :
    Letter (outputSplitControl A) (B.splitOutputParts) :=
  e.splitOutputParts

/-- The canonical action on true HJ line symbols:
constant letters become their full singleton split;
parameter symbols remain unchanged. -/
def splitLineSymbol (A : Structure L P) (B : System L P V) :
    LineSymbol (Letter A B) →
      LineSymbol (Letter (outputSplitControl A) (B.splitOutputParts))
  | .parameter => .parameter
  | .const e => .const (splitLetter A B e)

/-- The actual HJ line has EXACTLY the same parameter
positions after splitting all full partite letters. -/
def splitLine (A : Structure L P) (B : System L P V)
    {N : ℕ} (W : Line (Letter A B) N) :
    Line (Letter (outputSplitControl A) (B.splitOutputParts)) N where
  symbol i := splitLineSymbol A B (W.symbol i)
  hasParameter := by
    obtain ⟨i, hi⟩ := W.hasParameter
    refine ⟨i, ?_⟩
    change splitLineSymbol A B (W.symbol i) = .parameter
    rw [hi]
    rfl

/-- The coordinatewise POWER VERTEX obtained from a true native
HJ line is LITERALLY the same as the corresponding singletonized
line vertex, through the canonical full power isomorphism.
No existence argument or output-fibre truncation is hidden here. -/
theorem toSplitPowerVertex_lineMap
    (A : Structure L P) (B : System L P V)
    {N : ℕ} (W : Line (Letter A B) N) (x : V) :
    toSplitPowerVertex B N (lineMap W x) =
      lineMap (splitLine A B W) x := by
  apply Vertex.ext (B.splitOutputParts)
  · rfl
  · intro i
    cases h : W.symbol i with
    | parameter =>
        simp only [toSplitPowerVertex_coord, lineMap,
          splitLine, splitLineSymbol, h]
    | const e =>
        simp only [toSplitPowerVertex_coord, lineMap,
          splitLine, splitLineSymbol, splitLetter, h]
        change e.toFun (B.part x) = e.toFun (B.part x)
        rfl

/-- Natural transformation of the ACTUAL FULL Hales--Jewett line
attachment maps: singletonize an original line embedding and
transport it through the full singleton-power isomorphism,
or construct the line directly in the singletonized system.

Both maps are full native part-preserving embeddings and are
equal pointwise, including whole set-valued function fibres. -/
theorem splitPowerEmbedding_comp_lineEmbedding
    (A : Structure L P) (B : System L P V)
    (hB : B.ProjectionHom A)
    {N : ℕ} (W : Line (Letter A B) N) :
    (splitPowerEmbedding B N W.length_pos).comp
      ((lineEmbedding hB W).splitOutputParts) =
    lineEmbedding (B.splitOutputParts_projectionHom A hB)
      (splitLine A B W) := by
  apply FunctionalPartite.Embedding.ext
  intro x
  exact toSplitPowerVertex_lineMap A B W x

end StructuralRamsey.FunctionalPartite.Induced
