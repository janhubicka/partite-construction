import PartiteConstruction.Functional.ControlMissingOutputDichotomy

/-!
# Surviving functional output parts and control missing slots on one root

FULL functional partite embeddings preserve-and-reflect surviving
active output-part slots when weak subsets are pulled back exactly.
Thus two sides of a genuine full functional attachment, restricted
from the SAME weak ambient test, have identical surviving masks on
their ACTUAL common root, including when the root weak test is
not closed under function values.

The two sides also have identical control-part labels at those
common-root inputs. Therefore every output slot required by an
arbitrary functional CONTROL but absent in the exact weak SOURCE
tests is the same on both sides. This includes source-undefined
phantom slots, not just omitted ambient source output witnesses.

Only ACTUAL common-root tuples are covered: arbitrary additional
projected alpha-labelled side vertices may not lie in this root.
No common strict B-tree TARGET completion is constructed.
-/

namespace StructuralRamsey.FunctionalPartite

universe u v
variable {L : Language.{u}} {P V W H C : Type v}

/-- Two FULL partite functional root embeddings with equal exact
weak root preimages have the SAME surviving active output mask.

No function-closedness hypothesis is required for either weak set.
The entire fibre, not merely positive incidences, is reflected
by the two FULL embeddings. -/
theorem System.weakActiveOutputAtPart_commonWeakRoot_iff
    (Root : System L P H)
    (Left : System L P V) (Right : System L P W)
    (iLeft : Embedding Root Left)
    (iRight : Embedding Root Right)
    (SLeft : Set V) (SRight : Set W)
    (hRoot : ∀ r : H, iLeft r ∈ SLeft ↔ iRight r ∈ SRight)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → (iLeft.toFun ⁻¹' SLeft))
    (q : P) :
    (Left.weakInduce SLeft).ActiveOutputAtPart F
      (fun i => (⟨iLeft (xs i).1, (xs i).2⟩ : SLeft)) q ↔
    (Right.weakInduce SRight).ActiveOutputAtPart F
      (fun i =>
        (⟨iRight (xs i).1,
          (hRoot (xs i).1).mp (xs i).2⟩ : SRight)) q := by
  let ys : Fin (L.funcArity F) → (iRight.toFun ⁻¹' SRight) :=
    fun i => ⟨(xs i).1, (hRoot (xs i).1).mp (xs i).2⟩
  have hRootSurvives :
      (Root.weakInduce (iLeft.toFun ⁻¹' SLeft)).ActiveOutputAtPart F xs q ↔
      (Root.weakInduce (iRight.toFun ⁻¹' SRight)).ActiveOutputAtPart F ys q := by
    constructor
    · rintro ⟨z, hz, hq⟩
      exact ⟨⟨z.1, (hRoot z.1).mp z.2⟩, hz, hq⟩
    · rintro ⟨z, hz, hq⟩
      exact ⟨⟨z.1, (hRoot z.1).mpr z.2⟩, hz, hq⟩
  exact
    (iLeft.weakActiveOutputAtPart_preimage_iff
      SLeft F xs q).symm.trans
    (hRootSurvives.trans
      (iRight.weakActiveOutputAtPart_preimage_iff
        SRight F ys q))

/-- Complete BOOLEAN missing-control root profile coherence:
the control has an output at q but the exact weak source has none
iff the same holds on the other side of a FULL common root.

This uses only equality of the projected INPUT PARTS and agreement
of the surviving weak masks. It applies even when the source fibre
is itself empty and the control fibre is defined (the phantom
case allowed by original-partial EHN projections). -/
theorem System.controlMissing_commonWeakRoot_iff
    (Root : System L P H)
    (Left : System L P V) (Right : System L P W)
    (iLeft : Embedding Root Left)
    (iRight : Embedding Root Right)
    (SLeft : Set V) (SRight : Set W)
    (hRoot : ∀ r : H, iLeft r ∈ SLeft ↔ iRight r ∈ SRight)
    (D : Structure L P)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → (iLeft.toFun ⁻¹' SLeft))
    (q : P) :
    (q ∈ D.func F (fun i => Left.part (iLeft (xs i).1)) ∧
      ¬ (Left.weakInduce SLeft).ActiveOutputAtPart F
        (fun i => (⟨iLeft (xs i).1, (xs i).2⟩ : SLeft)) q) ↔
    (q ∈ D.func F (fun i => Right.part (iRight (xs i).1)) ∧
      ¬ (Right.weakInduce SRight).ActiveOutputAtPart F
        (fun i =>
          (⟨iRight (xs i).1,
            (hRoot (xs i).1).mp (xs i).2⟩ : SRight)) q) := by
  have hArgs :
      (fun i => Left.part (iLeft (xs i).1)) =
      (fun i => Right.part (iRight (xs i).1)) := by
    funext i
    exact (iLeft.map_part (xs i).1).trans
      (iRight.map_part (xs i).1).symm
  have hSurvives :=
    Root.weakActiveOutputAtPart_commonWeakRoot_iff
      Left Right iLeft iRight SLeft SRight hRoot F xs q
  constructor
  · rintro ⟨hControl, hNoLeft⟩
    refine ⟨?_, ?_⟩
    · rw [← hArgs]
      exact hControl
    · intro hRight
      exact hNoLeft (hSurvives.mpr hRight)
  · rintro ⟨hControl, hNoRight⟩
    refine ⟨?_, ?_⟩
    · rw [hArgs]
      exact hControl
    · intro hLeft
      exact hNoRight (hSurvives.mp hLeft)

/-- Exact cuts of TWO embedded sides from ONE ambient weak vertex
subset automatically satisfy the equality-of-weak-root-preimages
hypothesis. The control missing-output-root profile is therefore
equal on both sides, without ever treating weak inclusions as
full functional embeddings. -/
theorem System.controlMissing_commonWhole_iff
    (Root : System L P H)
    (Left : System L P V) (Right : System L P W)
    (Whole : System L P C)
    (iLeft : Embedding Root Left)
    (iRight : Embedding Root Right)
    (jLeft : Embedding Left Whole)
    (jRight : Embedding Right Whole)
    (hComm : ∀ r : H, jLeft (iLeft r) = jRight (iRight r))
    (S : Set C) (D : Structure L P)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) →
      (iLeft.toFun ⁻¹' (jLeft.toFun ⁻¹' S)))
    (q : P) :
    (q ∈ D.func F (fun i => Left.part (iLeft (xs i).1)) ∧
      ¬ (Left.weakInduce (jLeft.toFun ⁻¹' S)).ActiveOutputAtPart F
        (fun i => (⟨iLeft (xs i).1, (xs i).2⟩ :
          jLeft.toFun ⁻¹' S)) q) ↔
    (q ∈ D.func F (fun i => Right.part (iRight (xs i).1)) ∧
      ¬ (Right.weakInduce (jRight.toFun ⁻¹' S)).ActiveOutputAtPart F
        (fun i =>
          (⟨iRight (xs i).1,
            (show jRight (iRight (xs i).1) ∈ S from
              (hComm (xs i).1 ▸ (xs i).2))⟩ :
            jRight.toFun ⁻¹' S)) q) := by
  have hRoot : ∀ r : H,
      iLeft r ∈ jLeft.toFun ⁻¹' S ↔
      iRight r ∈ jRight.toFun ⁻¹' S := by
    intro r
    change jLeft (iLeft r) ∈ S ↔ jRight (iRight r) ∈ S
    rw [hComm r]
  exact Root.controlMissing_commonWeakRoot_iff
    Left Right iLeft iRight
    (jLeft.toFun ⁻¹' S) (jRight.toFun ⁻¹' S)
    hRoot D F xs q



/-- Named-control-predicate form of the common weak root theorem.

This wrapper combines the verified EHN-control-versus-source
dichotomy with exact full root-cut coherence, but requires no
global full/domain-reflecting projection. -/
theorem System.controlMissingAtPart_commonWeakRoot_iff
    (Root : System L P H)
    (Left : System L P V) (Right : System L P W)
    (iLeft : Embedding Root Left)
    (iRight : Embedding Root Right)
    (SLeft : Set V) (SRight : Set W)
    (hRoot : ∀ r : H, iLeft r ∈ SLeft ↔ iRight r ∈ SRight)
    (D : Structure L P)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → (iLeft.toFun ⁻¹' SLeft))
    (q : P) :
    Left.ControlMissingAtPart D SLeft F
      (fun i => (⟨iLeft (xs i).1, (xs i).2⟩ : SLeft)) q ↔
    Right.ControlMissingAtPart D SRight F
      (fun i =>
        (⟨iRight (xs i).1,
          (hRoot (xs i).1).mp (xs i).2⟩ : SRight)) q := by
  exact Root.controlMissing_commonWeakRoot_iff
    Left Right iLeft iRight SLeft SRight hRoot D F xs q

/-- Named-control-predicate form for two actual full attaching
sides restricted by one exact ambient weak test. -/
theorem System.controlMissingAtPart_commonWhole_iff
    (Root : System L P H)
    (Left : System L P V) (Right : System L P W)
    (Whole : System L P C)
    (iLeft : Embedding Root Left)
    (iRight : Embedding Root Right)
    (jLeft : Embedding Left Whole)
    (jRight : Embedding Right Whole)
    (hComm : ∀ r : H, jLeft (iLeft r) = jRight (iRight r))
    (S : Set C) (D : Structure L P)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) →
      (iLeft.toFun ⁻¹' (jLeft.toFun ⁻¹' S)))
    (q : P) :
    Left.ControlMissingAtPart D (jLeft.toFun ⁻¹' S) F
      (fun i => (⟨iLeft (xs i).1, (xs i).2⟩ :
        jLeft.toFun ⁻¹' S)) q ↔
    Right.ControlMissingAtPart D (jRight.toFun ⁻¹' S) F
      (fun i =>
        (⟨iRight (xs i).1,
          (show jRight (iRight (xs i).1) ∈ S from
            (hComm (xs i).1 ▸ (xs i).2))⟩ :
          jRight.toFun ⁻¹' S)) q := by
  exact Root.controlMissing_commonWhole_iff
    Left Right Whole iLeft iRight jLeft jRight
    hComm S D F xs q

end StructuralRamsey.FunctionalPartite
