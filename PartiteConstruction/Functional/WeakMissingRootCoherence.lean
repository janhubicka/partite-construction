import PartiteConstruction.Functional.WeakActiveRootPreimage

/-!
# Missing functional root slots have unique omitted outputs

An active output-part mask is not just a Boolean decoration: in a
transversal functional partite system a missing slot has a UNIQUE
ambient output vertex outside the exact weak test.

For two genuine full root embeddings into the sides of an attachment,
if the two exact side weak sets have the same inverse-image subset
of the common root, their missing slots agree, even if the weak
subsets themselves are NOT function-closed.

This is SOURCE root-profile coherence. It does not manufacture a
compatible B-tree TARGET completion of nonclosed weak root tests;
the history-dependent maximal mixed step remains open.
-/

namespace StructuralRamsey.FunctionalPartite

universe u v
variable {L : Language.{u}} {P V W H C : Type v}

/-- An output-part slot is missing exactly when its unique ambient
output lies OUTSIDE the exact weak vertex set.

The reverse direction uses the actual per-fibre transversality
condition: an output outside S cannot coexist with a different
retained output in the same part. -/
theorem System.missingActiveOutputAtPart_iff_outside
    (B : System L P V) (S : Set V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S) (q : P) :
    B.MissingActiveOutputAtPart S F xs q ↔
      ∃ y : V, y ∈ B.func F (Subtype.val ∘ xs) ∧
        B.part y = q ∧ y ∉ S := by
  constructor
  · rintro ⟨⟨y, hy, hq⟩, hNo⟩
    refine ⟨y, hy, hq, ?_⟩
    intro hyS
    apply hNo
    exact ⟨⟨y, hyS⟩, hy, hq⟩
  · rintro ⟨y, hy, hq, hOutside⟩
    refine ⟨⟨y, hy, hq⟩, ?_⟩
    rintro ⟨z, hz, hzPart⟩
    have heq : y = z.1 :=
      B.funcTransversal F (Subtype.val ∘ xs) y z.1
        hy hz (hq.trans hzPart.symm)
    apply hOutside
    rw [heq]
    exact z.2

/-- A missing functional output-part slot determines exactly one
omitted ambient output vertex. This holds for genuinely multivalued
fibres because distinct values must live in distinct parts. -/
theorem System.missingActiveOutputAtPart_uniqueOutside
    (B : System L P V) (S : Set V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S) (q : P)
    (hMissing : B.MissingActiveOutputAtPart S F xs q) :
    ∃! y : V, y ∈ B.func F (Subtype.val ∘ xs) ∧
      B.part y = q ∧ y ∉ S := by
  obtain ⟨y, hy, hq, hOutside⟩ :=
    (B.missingActiveOutputAtPart_iff_outside S F xs q).mp hMissing
  refine ⟨y, ⟨hy, hq, hOutside⟩, ?_⟩
  intro z hz
  exact B.funcTransversal F (Subtype.val ∘ xs) z y
    hz.1 hy (hz.2.1.trans hq.symm)

/-- Two FULL embeddings of a common functional root carry identical
MISSING output-part slots on exact side weak tests, provided the
two side tests cut out the SAME subset of the root.

Neither side weak test need be function-closed. This is stronger
than mere agreement of ambient active roots: it compares the
actual outputs lost by the two weak restrictions, for arbitrary
transversal set-valued functions. -/
theorem System.missingActiveOutputAtPart_commonWeakRoot_iff
    (Root : System L P H)
    (Left : System L P V) (Right : System L P W)
    (iLeft : Embedding Root Left)
    (iRight : Embedding Root Right)
    (SLeft : Set V) (SRight : Set W)
    (hRoot : ∀ r : H, iLeft r ∈ SLeft ↔ iRight r ∈ SRight)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → (iLeft.toFun ⁻¹' SLeft))
    (q : P) :
    Left.MissingActiveOutputAtPart SLeft F
      (fun i => (⟨iLeft (xs i).1, (xs i).2⟩ : SLeft)) q ↔
    Right.MissingActiveOutputAtPart SRight F
      (fun i =>
        (⟨iRight (xs i).1, (hRoot (xs i).1).mp (xs i).2⟩ : SRight)) q := by
  let ys : Fin (L.funcArity F) → (iRight.toFun ⁻¹' SRight) :=
    fun i => ⟨(xs i).1, (hRoot (xs i).1).mp (xs i).2⟩
  have hRootMissing :
      Root.MissingActiveOutputAtPart
        (iLeft.toFun ⁻¹' SLeft) F xs q ↔
      Root.MissingActiveOutputAtPart
        (iRight.toFun ⁻¹' SRight) F ys q := by
    constructor
    · intro hm
      obtain ⟨y, hy, hq, hOutside⟩ :=
        (Root.missingActiveOutputAtPart_iff_outside
          (iLeft.toFun ⁻¹' SLeft) F xs q).mp hm
      apply (Root.missingActiveOutputAtPart_iff_outside
        (iRight.toFun ⁻¹' SRight) F ys q).mpr
      refine ⟨y, hy, hq, ?_⟩
      intro hyR
      exact hOutside ((hRoot y).mpr hyR)
    · intro hm
      obtain ⟨y, hy, hq, hOutside⟩ :=
        (Root.missingActiveOutputAtPart_iff_outside
          (iRight.toFun ⁻¹' SRight) F ys q).mp hm
      apply (Root.missingActiveOutputAtPart_iff_outside
        (iLeft.toFun ⁻¹' SLeft) F xs q).mpr
      refine ⟨y, hy, hq, ?_⟩
      intro hyL
      exact hOutside ((hRoot y).mp hyL)
  exact
    (iLeft.missingActiveOutputAtPart_preimage_iff
      SLeft F xs q).symm.trans
      (hRootMissing.trans
        (iRight.missingActiveOutputAtPart_preimage_iff
          SRight F ys q))

/-- In an actual common ambient system, the root-image equality
automatically supplies the required identical weak-root cut.
Only FULL root embeddings are used to compare function fibres. -/
theorem System.missingActiveOutputAtPart_commonWhole_iff
    (Root : System L P H)
    (Left : System L P V) (Right : System L P W)
    (Whole : System L P C)
    (iLeft : Embedding Root Left)
    (iRight : Embedding Root Right)
    (jLeft : Embedding Left Whole)
    (jRight : Embedding Right Whole)
    (hComm : ∀ r : H, jLeft (iLeft r) = jRight (iRight r))
    (S : Set C)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) →
      (iLeft.toFun ⁻¹' (jLeft.toFun ⁻¹' S)))
    (q : P) :
    Left.MissingActiveOutputAtPart (jLeft.toFun ⁻¹' S) F
      (fun i => (⟨iLeft (xs i).1, (xs i).2⟩ :
        jLeft.toFun ⁻¹' S)) q ↔
    Right.MissingActiveOutputAtPart (jRight.toFun ⁻¹' S) F
      (fun i =>
        (⟨iRight (xs i).1,
          (show jRight (iRight (xs i).1) ∈ S from
            (hComm (xs i).1 ▸ (xs i).2))⟩ :
          jRight.toFun ⁻¹' S)) q := by
  have hRoot : ∀ r : H,
      iLeft r ∈ jLeft.toFun ⁻¹' S ↔
      iRight r ∈ jRight.toFun ⁻¹' S := by
    intro r
    change jLeft (iLeft r) ∈ S ↔ jRight (iRight r) ∈ S
    rw [hComm r]
  exact Root.missingActiveOutputAtPart_commonWeakRoot_iff
    Left Right iLeft iRight (jLeft.toFun ⁻¹' S)
    (jRight.toFun ⁻¹' S) hRoot F xs q

end StructuralRamsey.FunctionalPartite
