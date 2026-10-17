import PartiteConstruction.Structure.PartialSetFunctionsClosed

/-!
# Closed agreement roots for genuinely partial set-valued operations

This is the `Option (Set V)` analogue of the genuine functional
partite-system equalizer lemma, but without conflating an undefined
fibre (`none`) with a defined-empty value (`some ∅`).

Full partial-functional embeddings preserve and reflect both states.
If the target has transverse output fibres and the two full
embeddings respect the same part map, their exact pointwise
equalizer is function-closed. The proof works even with multivalued
outputs: each output has the same part under both embeddings, and
target transversality forces the images to agree.

This establishes closure of pairwise roots. It does NOT construct
compatible B-tree completions for maximal mixed weak tests, nor
does it resolve the multi-line Hales–Jewett cycle obstruction.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w p
variable {L : Language.{u}} {V : Type v} {W : Type w} {P : Type p}

/-- Each defined set-valued fibre contains at most one output of
each part. This makes sense also for `some ∅` and imposes no
condition at an undefined input. -/
def FibreTransversal (B : PartialSetStructure L W)
    (part : W → P) : Prop :=
  ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → W)
    (T : Set W), B.func F xs = some T →
      ∀ y, y ∈ T → ∀ z, z ∈ T →
        part y = part z → y = z

/-- Exact agreement of two FULL part-preserving embeddings is
closed under every explicitly partial, set-valued operation.
In particular no hypothesis rules out defined-empty fibres. -/
theorem Embedding.agreement_isClosed
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (f g : Embedding A B)
    (partA : V → P) (partB : W → P)
    (hfpart : ∀ x, partB (f.toFun x) = partA x)
    (hgpart : ∀ x, partB (g.toFun x) = partA x)
    (hTrans : FibreTransversal B partB) :
    IsClosed A {x : V | f.toFun x = g.toFun x} := by
  intro F xs T hArgs hFunc y hy
  have hTuple : (f.toFun ∘ xs) = (g.toFun ∘ xs) := by
    funext i
    exact hArgs i
  have hf :
      B.func F (f.toFun ∘ xs) =
        some (Structure.imageSet f.toFun T) := by
    simpa [hFunc] using (f.map_func F xs).symm
  have hg :
      B.func F (g.toFun ∘ xs) =
        some (Structure.imageSet g.toFun T) := by
    simpa [hFunc] using (g.map_func F xs).symm
  have hSome :
      some (Structure.imageSet f.toFun T) =
        some (Structure.imageSet g.toFun T) := by
    calc
      _ = B.func F (f.toFun ∘ xs) := hf.symm
      _ = B.func F (g.toFun ∘ xs) := congrArg (B.func F) hTuple
      _ = _ := hg
  have hImages :
      Structure.imageSet f.toFun T =
        Structure.imageSet g.toFun T := Option.some.inj hSome
  have hyf : f.toFun y ∈ Structure.imageSet f.toFun T :=
    ⟨y, hy, rfl⟩
  have hyg : g.toFun y ∈ Structure.imageSet f.toFun T := by
    rw [hImages]
    exact ⟨y, hy, rfl⟩
  have hPart : partB (f.toFun y) = partB (g.toFun y) :=
    (hfpart y).trans (hgpart y).symm
  exact hTrans F (f.toFun ∘ xs)
    (Structure.imageSet f.toFun T) hf
    (f.toFun y) hyf (g.toFun y) hyg hPart

end StructuralRamsey.PartialSetStructure
