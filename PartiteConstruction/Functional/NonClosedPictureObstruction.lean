import PartiteConstruction.Functional.Closed
import PartiteConstruction.Relational.Attachment

/-! # Obstruction for non-closed Picture supports

For a non-U-closed support, an ordinary free attachment can destroy closedness
of a selected copy even if that copy itself comes from a closed source
embedding.  The mechanism is simple: a different attached copy can agree with
the selected copy on all inputs of a function application and contribute an
output outside the common overlap.  That output then lies over the selected
input tuple but cannot belong to the selected copy.

This is the local obstruction behind the arbitrary-alpha gap in the recursive
Picture construction.
-/
namespace StructuralRamsey.RelStructure.Attachment

open Structure

universe u v
variable {L : Language.{u}}
variable {U V W I : Type v}

variable (A : RelStructure L.graph U)
variable (B : RelStructure L.graph V)
variable (S : Set V)
variable (D : RelStructure L.graph W)
variable (f : I → Embedding (B.induce S) D)

/-- If another attached copy agrees with the selected copy on every function
input but has a function output outside the overlap, then the selected copy is
not U-closed in the free attachment. -/
theorem copy_comp_not_functionClosed
    (i j : I)
    (e : Embedding A B)
    (heS : ∀ a : U, e a ∈ S)
    (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → U)
    (q : Fin (L.funcArity F) → V)
    (y : V)
    (hy : y ∉ S)
    (hrel : B.rel (.inr F) (Structure.funcTuple q y))
    (hinputs :
      ∀ k : Fin (L.funcArity F),
        copyMap B S D f i (e (x k)) =
          copyMap B S D f j (q k)) :
    ¬ FunctionClosedMap A (attach B S D f)
      (copyMap B S D f i ∘ e) := by
  intro hclosed
  let out : Vertex S (W := W) (I := I) :=
    copyMap B S D f j y
  have htarget :
      (attach B S D f).rel (.inr F)
        (Structure.funcTuple ((copyMap B S D f i ∘ e) ∘ x) out) := by
    refine Or.inr ⟨j, Structure.funcTuple q y, hrel, ?_⟩
    funext k
    refine Fin.lastCases ?_ (fun t => ?_) k
    · dsimp [out]
      change
        copyMap B S D f j y =
          copyMap B S D f j
            (Structure.funcTuple q y (Fin.last (L.funcArity F)))
      rw [Structure.funcTuple_last]
    · change
        copyMap B S D f i (e (x t)) =
          copyMap B S D f j
            (Structure.funcTuple q y t.castSucc)
      rw [Structure.funcTuple_castSucc]
      exact hinputs t
  obtain ⟨z, _, hz⟩ := hclosed F x out htarget
  have hselected :
      copyMap B S D f i (e z) =
        Sum.inl (f i ⟨e z, heS z⟩) :=
    copyMap_mem i (e z) (heS z)
  have hout :
      out = Sum.inr (j, ⟨y, hy⟩) := by
    exact copyMap_not_mem j y hy
  change copyMap B S D f i (e z) = out at hz
  rw [hselected, hout] at hz
  have : False := by simpa using hz
  exact this

end StructuralRamsey.RelStructure.Attachment
