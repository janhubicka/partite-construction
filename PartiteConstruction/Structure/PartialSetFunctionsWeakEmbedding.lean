import PartiteConstruction.Structure.PartialSetFunctionsClosed

/-!
# Exact weak restrictions preserve full embeddings for partial set-valued functions

Here a genuinely partial operation takes values in `Option (Set V)`.
The two states `none` (undefined) and `some ∅` (defined-empty) must
not be conflated. A weak restriction retains original defined-empty
inputs and turns an originally nonempty fibre with no surviving output
into `none`.

For ANY vertex map f:V→W and ANY target vertex set S, taking the
preimage f⁻¹(S) commutes with weak restriction of an operation value,
including these two distinct empty states. For a FULL embedding f,
we consequently obtain a FULL embedding of exact weak restrictions

  A|^w_{f⁻¹(S)} ↪ B|^w_S.

The proof does not enlarge a test by generated closure, and supports
arbitrary set-valued function fibres. The analogous fact is false for
arbitrary weak EHN projections without stronger lifting hypotheses.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- The exact map from a preimage weak carrier into its target weak
carrier. -/
def restrictMap (f : V → W) (S : Set W) :
    (f ⁻¹' S) → S :=
  fun x => ⟨f x.1, x.2⟩

/-- The image of retained outputs is the retained image of outputs.
No injectivity, closure, or singleton-valuedness is required. -/
theorem imageSet_restrictMap
    (f : V → W) (S : Set W) (T : Set V) :
    Structure.imageSet (restrictMap f S)
      {x : (f ⁻¹' S) | x.1 ∈ T} =
    {y : S | y.1 ∈ Structure.imageSet f T} := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    change (restrictMap f S) x = y at hxy
    have heq : f x.1 = y.1 :=
      congrArg Subtype.val hxy
    change y.1 ∈ Structure.imageSet f T
    exact ⟨x.1, hx, heq⟩
  · rintro ⟨x, hx, hxy⟩
    have hS : f x ∈ S := by
      rw [hxy]
      exact y.2
    refine ⟨⟨x, hS⟩, hx, ?_⟩
    apply Subtype.ext
    exact hxy

/-- Weak restriction commutes with the exact preimage/image diagram
for genuinely partial set-valued operations. In particular the
identity holds for `none`, `some ∅`, surviving nonempty fibres,
and nonempty fibres all of whose outputs were forgotten. -/
theorem weakValue_map_preimage
    (f : V → W) (S : Set W)
    (value : Option (Set V)) :
    (weakValue (f ⁻¹' S) value).map
      (Structure.imageSet (restrictMap f S)) =
    weakValue S (value.map (Structure.imageSet f)) := by
  classical
  cases value with
  | none =>
      rfl
  | some T =>
      by_cases hT : T.Nonempty
      · have hImg : (Structure.imageSet f T).Nonempty := by
          obtain ⟨x, hx⟩ := hT
          exact ⟨f x, ⟨x, hx, rfl⟩⟩
        by_cases hMeet : (T ∩ (f ⁻¹' S)).Nonempty
        · have hImgMeet : (Structure.imageSet f T ∩ S).Nonempty := by
            obtain ⟨x, hxT, hxS⟩ := hMeet
            exact ⟨f x, ⟨x, hxT, rfl⟩, hxS⟩
          simpa [weakValue, hT, hImg, hMeet, hImgMeet] using
            imageSet_restrictMap f S T
        · have hImgMeet : ¬(Structure.imageSet f T ∩ S).Nonempty := by
            rintro ⟨y, ⟨x, hxT, hxy⟩, hyS⟩
            apply hMeet
            refine ⟨x, hxT, ?_⟩
            change f x ∈ S
            rw [hxy]
            exact hyS
          simp [weakValue, hT, hImg, hMeet, hImgMeet]
      · have hEmpty : T = ∅ := by
          ext x
          constructor
          · intro hx
            exact (hT ⟨x, hx⟩).elim
          · simp
        subst T
        simp [weakValue, Structure.imageSet]

/-- Full embeddings restrict to exact WEAK vertex sets without
closing the source or target, while reflecting both domain bits and
every surviving function value. -/
def Embedding.weakRestrictToPreimage
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : Embedding A B) (S : Set W) :
    Embedding (weakInduce A (e.toFun ⁻¹' S)) (weakInduce B S) where
  toFun := restrictMap e.toFun S
  injective := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val hxy
  map_rel_iff := by
    intro R xs
    change B.rel R (e.toFun ∘ (Subtype.val ∘ xs)) ↔
      A.rel R (Subtype.val ∘ xs)
    exact e.map_rel_iff R (Subtype.val ∘ xs)
  map_func := by
    intro F xs
    change (weakValue (e.toFun ⁻¹' S)
      (A.func F (Subtype.val ∘ xs))).map
        (Structure.imageSet (restrictMap e.toFun S)) =
      weakValue S (B.func F (e.toFun ∘ (Subtype.val ∘ xs)))
    rw [← e.map_func F (Subtype.val ∘ xs)]
    exact weakValue_map_preimage e.toFun S
      (A.func F (Subtype.val ∘ xs))

end StructuralRamsey.PartialSetStructure
