import PartiteConstruction.Functional.ActiveOutputRootTransport
import PartiteConstruction.Functional.WeakClosedActiveMasks
import PartiteConstruction.Functional.WeakTransversalTests

/-!
# Exact weak ambient closure-root masks commute with FULL functional pullbacks

A full partite functional embedding e:R↪B and an arbitrary EXACT
weak target set S⊆B induce the weak root set e⁻¹[S] in R.
The ACTIVE source function-output mask at each part q is preserved
and reflected in the ambient targets (already verified), and the
SURVIVING mask of the exact weak restrictions ALSO agrees.

Therefore the MISSING active U-closure output-part slot predicate
is invariant under such full functional embeddings on exact
weak preimages, even for multivalued functions and nonclosed tests.

This is the genuine source-root compatibility of the two sides
of a full functional Hales–Jewett attachment, not a claim that
arbitrary EHN projections reflect domains or that two strict
target B-tree completions are automatically compatible.
-/

namespace StructuralRamsey.FunctionalPartite

universe u v
variable {L : Language.{u}} {P V W : Type v}

/-- One specific missing U-closure output-part slot for the exact
weak vertex set S: an actual ambient function output exists in
part q, but no such output survives inside S.

Unlike a single nonempty-domain bit, this records independent
missing parts of genuinely multivalued function fibres. -/
def System.MissingActiveOutputAtPart
    (B : System L P V) (S : Set V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S)
    (q : P) : Prop :=
  B.ActiveOutputAtPart F (Subtype.val ∘ xs) q ∧
    ¬ (B.weakInduce S).ActiveOutputAtPart F xs q

/-- FULL functional embeddings preserve-and-reflect the
SURVIVING active output-part masks on EXACT weak preimages.

The crucial reverse direction uses full fibre-surjectivity.
No extra closure points or part saturation are assumed. -/
theorem Embedding.weakActiveOutputAtPart_preimage_iff
    {A : System L P V} {B : System L P W}
    (e : Embedding A B)
    (S : Set W)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → (e.toFun ⁻¹' S))
    (q : P) :
    (A.weakInduce (e.toFun ⁻¹' S)).ActiveOutputAtPart
      F xs q ↔
    (B.weakInduce S).ActiveOutputAtPart F
      (fun i => (⟨e (xs i).1, (xs i).2⟩ : S)) q := by
  constructor
  · rintro ⟨y, hy, hPart⟩
    let z : S := ⟨e y.1, y.2⟩
    refine ⟨z, ?_, ?_⟩
    · change e y.1 ∈ B.func F (e.toFun ∘ (Subtype.val ∘ xs))
      rw [← e.map_func F (Subtype.val ∘ xs)]
      exact ⟨y.1, hy, rfl⟩
    · change B.part (e y.1) = q
      exact (e.map_part y.1).trans hPart
  · rintro ⟨z, hz, hPart⟩
    have hB : z.1 ∈
        B.func F (e.toFun ∘ (Subtype.val ∘ xs)) := hz
    rw [← e.map_func F (Subtype.val ∘ xs)] at hB
    obtain ⟨y, hy, hImage⟩ := hB
    have hyS : e y ∈ S := by
      rw [hImage]
      exact z.2
    let t : e.toFun ⁻¹' S := ⟨y, hyS⟩
    refine ⟨t, hy, ?_⟩
    change A.part y = q
    calc
      A.part y = B.part (e y) := (e.map_part y).symm
      _ = B.part z.1 := congrArg B.part hImage
      _ = q := hPart

/-- The FULL ambient active mask and the SURVIVING weak active
mask are each invariant under genuine functional full embeddings;
hence the missing-closure-slot predicate is invariant as well. -/
theorem Embedding.missingActiveOutputAtPart_preimage_iff
    {A : System L P V} {B : System L P W}
    (e : Embedding A B)
    (S : Set W)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → (e.toFun ⁻¹' S))
    (q : P) :
    A.MissingActiveOutputAtPart (e.toFun ⁻¹' S) F xs q ↔
    B.MissingActiveOutputAtPart S F
      (fun i => (⟨e (xs i).1, (xs i).2⟩ : S)) q := by
  have hAmbient :
      A.ActiveOutputAtPart F (Subtype.val ∘ xs) q ↔
      B.ActiveOutputAtPart
        F (e.toFun ∘ (Subtype.val ∘ xs)) q :=
    e.activeOutputAtPart_iff F (Subtype.val ∘ xs) q
  have hSurviving :=
    e.weakActiveOutputAtPart_preimage_iff S F xs q
  constructor
  · rintro ⟨hAct, hNot⟩
    refine ⟨hAmbient.mp hAct, ?_⟩
    exact fun h => hNot (hSurviving.mpr h)
  · rintro ⟨hAct, hNot⟩
    refine ⟨hAmbient.mpr hAct, ?_⟩
    exact fun h => hNot (hSurviving.mp h)

/-- EXACT weak functional U-closedness can be checked by the
absence of missing active output-part root slots. This is
stronger than equality of a single global defined-domain bit:
multivalued functions may retain one output part while losing another.

Full functional embeddings transport this precise local defect
predicate by the preceding theorem. -/
theorem System.isClosed_iff_noMissingActiveOutputs
    (B : System L P V) (S : Set V) :
    B.toStructure.IsClosed S ↔
      ∀ (F : L.FuncSymbol)
        (xs : Fin (L.funcArity F) → S) (q : P),
        ¬ B.MissingActiveOutputAtPart S F xs q := by
  constructor
  · intro hc F xs q hMissing
    exact hMissing.2
      (((B.isClosed_iff_weakActiveOutputMasks S).mp hc F xs q).mp
        hMissing.1)
  · intro h
    apply (B.isClosed_iff_ambientActiveMasks_reflected S).mpr
    intro F xs q hActive
    by_contra hNo
    exact h F xs q ⟨hActive, hNo⟩

end StructuralRamsey.FunctionalPartite
