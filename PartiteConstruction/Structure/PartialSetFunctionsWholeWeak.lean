import PartiteConstruction.Structure.PartialSetFunctionsWeakEmbedding

/-!
# Whole-fibre weak restrictions of genuinely partial set-valued functions

On a vertex subset, keep a defined function application exactly when its
ENTIRE value set survives. Otherwise it becomes undefined. In particular,
an originally defined-empty value remains defined-empty.

This differs from the existing `weakInduce`, which clips individual outputs.
The existing checked API is left unchanged. Exact preimages preserve full
embeddings for the whole-fibre convention, and arbitrary restrictions of
source-defined homomorphisms remain source-defined homomorphisms. Neither
statement enlarges a weak test by taking its generated closure.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- Retain a defined application precisely when its whole output set is
contained in the chosen carrier. Defined-empty stays defined-empty. -/
noncomputable def wholeWeakValue (S : Set V) :
    Option (Set V) → Option (Set S)
  | none => none
  | some U => by
      classical
      exact if U ⊆ S then some {y : S | y.1 ∈ U} else none

/-- The weak restriction that drops an entire application whenever any of
its outputs leaves the chosen carrier. This does not clip a value set. -/
noncomputable def wholeWeakInduce (A : PartialSetStructure L V)
    (S : Set V) : PartialSetStructure L S where
  rel R x := A.rel R (Subtype.val ∘ x)
  func F x := wholeWeakValue S (A.func F (Subtype.val ∘ x))

@[simp] theorem wholeWeakValue_none (S : Set V) :
    wholeWeakValue S (none : Option (Set V)) = none := rfl

@[simp] theorem wholeWeakValue_some_empty (S : Set V) :
    wholeWeakValue S (some (∅ : Set V)) =
      some (∅ : Set S) := by
  simp [wholeWeakValue]

theorem wholeWeakValue_of_subset
    (S U : Set V) (hU : U ⊆ S) :
    wholeWeakValue S (some U) =
      some {y : S | y.1 ∈ U} := by
  simp [wholeWeakValue, hU]

theorem wholeWeakValue_of_not_subset
    (S U : Set V) (hU : ¬ U ⊆ S) :
    wholeWeakValue S (some U) = none := by
  simp [wholeWeakValue, hU]

/-- A surviving value is an original complete value, all of whose outputs
belong to the chosen carrier. This also covers defined-empty values. -/
theorem wholeWeakValue_eq_some_iff
    (S : Set V) (value : Option (Set V)) (U : Set S) :
    wholeWeakValue S value = some U ↔
      ∃ T : Set V, value = some T ∧ T ⊆ S ∧
        U = {y : S | y.1 ∈ T} := by
  classical
  cases value with
  | none =>
      simp [wholeWeakValue]
  | some T =>
      by_cases hT : T ⊆ S
      · constructor
        · intro h
          have hU : {y : S | y.1 ∈ T} = U := by
            simpa [wholeWeakValue, hT] using h
          exact ⟨T, rfl, hT, hU.symm⟩
        · rintro ⟨T', hEq, _, rfl⟩
          have hTT' : T = T' := Option.some.inj hEq
          subst T'
          exact wholeWeakValue_of_subset S T hT
      · constructor
        · intro h
          simp [wholeWeakValue, hT] at h
        · rintro ⟨T', hEq, hSub, _⟩
          have hTT' : T = T' := Option.some.inj hEq
          exact (hT (hTT'.symm ▸ hSub)).elim

/-- Taking an exact preimage commutes with whole-fibre restriction and
the image of a partial value. No injectivity assumption is needed. -/
theorem wholeWeakValue_map_preimage
    (f : V → W) (S : Set W)
    (value : Option (Set V)) :
    (wholeWeakValue (f ⁻¹' S) value).map
      (Structure.imageSet (restrictMap f S)) =
    wholeWeakValue S (value.map (Structure.imageSet f)) := by
  classical
  cases value with
  | none =>
      rfl
  | some T =>
      have hSub : Structure.imageSet f T ⊆ S ↔ T ⊆ f ⁻¹' S := by
        constructor
        · intro h x hx
          exact h ⟨x, hx, rfl⟩
        · intro h y hy
          obtain ⟨x, hx, rfl⟩ := hy
          exact h hx
      by_cases hT : T ⊆ f ⁻¹' S
      · have hImage : Structure.imageSet f T ⊆ S := hSub.mpr hT
        simpa [wholeWeakValue, hT, hImage] using
          congrArg some (imageSet_restrictMap f S T)
      · have hImage : ¬ Structure.imageSet f T ⊆ S := by
          intro h
          exact hT (hSub.mp h)
        simp [wholeWeakValue, hT, hImage]

/-- A full embedding restricts to a full embedding on an arbitrary exact
target vertex set and its exact source preimage, including domain bits. -/
def Embedding.wholeWeakRestrictToPreimage
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : Embedding A B) (S : Set W) :
    Embedding (wholeWeakInduce A (e.toFun ⁻¹' S))
      (wholeWeakInduce B S) where
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
    change (wholeWeakValue (e.toFun ⁻¹' S)
      (A.func F (Subtype.val ∘ xs))).map
        (Structure.imageSet (restrictMap e.toFun S)) =
      wholeWeakValue S (B.func F (e.toFun ∘ (Subtype.val ∘ xs)))
    rw [← e.map_func F (Subtype.val ∘ xs)]
    exact wholeWeakValue_map_preimage e.toFun S
      (A.func F (Subtype.val ∘ xs))

/-- The same full restriction with a source carrier presented by an
explicit exact-preimage criterion. -/
def Embedding.wholeWeakRestrictExact
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : Embedding A B) (S : Set V) (T : Set W)
    (hExact : ∀ x, x ∈ S ↔ e.toFun x ∈ T) :
    Embedding (wholeWeakInduce A S) (wholeWeakInduce B T) where
  toFun x := ⟨e.toFun x.1, (hExact x.1).mp x.2⟩
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
    have hEq : S = e.toFun ⁻¹' T := Set.ext hExact
    subst S
    exact (e.wholeWeakRestrictToPreimage T).map_func F xs

@[simp] theorem Embedding.wholeWeakRestrictExact_val
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : Embedding A B) (S : Set V) (T : Set W)
    (hExact : ∀ x, x ∈ S ↔ e.toFun x ∈ T) (x : S) :
    ((e.wholeWeakRestrictExact S T hExact).toFun x).1 = e.toFun x.1 := rfl

/-- Source-defined partial homomorphisms restrict to ANY exact weak
carriers on which their underlying vertex map restricts. No reflection
of undefined source applications or closure of the carriers is needed. -/
theorem IsOriginalPartialHomomorphism.wholeWeakRestrict
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f)
    (S : Set V) (T : Set W) (g : S → T)
    (hg : ∀ x : S, (g x).1 = f x.1) :
    IsOriginalPartialHomomorphism
      (wholeWeakInduce A S) (wholeWeakInduce B T) g := by
  constructor
  · intro R xs hRel
    have hTuple : Subtype.val ∘ (g ∘ xs) =
        f ∘ (Subtype.val ∘ xs) := by
      funext i
      exact hg (xs i)
    change B.rel R (Subtype.val ∘ (g ∘ xs))
    rw [hTuple]
    exact hf.1 R (Subtype.val ∘ xs) hRel
  · intro F xs U hValue
    change wholeWeakValue S (A.func F (Subtype.val ∘ xs)) = some U at hValue
    obtain ⟨Q, hQ, hQS, rfl⟩ :=
      (wholeWeakValue_eq_some_iff S _ U).mp hValue
    have hTarget : B.func F (f ∘ (Subtype.val ∘ xs)) =
        some (Structure.imageSet f Q) :=
      hf.2 F (Subtype.val ∘ xs) Q hQ
    have hQT : Structure.imageSet f Q ⊆ T := by
      rintro y ⟨x, hx, rfl⟩
      have h := (g ⟨x, hQS hx⟩).2
      rw [hg] at h
      exact h
    have hTuple : Subtype.val ∘ (g ∘ xs) =
        f ∘ (Subtype.val ∘ xs) := by
      funext i
      exact hg (xs i)
    change wholeWeakValue T (B.func F (Subtype.val ∘ (g ∘ xs))) =
      some (Structure.imageSet g {x : S | x.1 ∈ Q})
    rw [hTuple, hTarget, wholeWeakValue_of_subset T _ hQT]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      refine ⟨⟨x, hQS hx⟩, hx, ?_⟩
      apply Subtype.ext
      exact (hg ⟨x, hQS hx⟩).trans hxy
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x.1, hx, (hg x).symm.trans (congrArg Subtype.val hxy)⟩

/-- The inclusion of a whole-fibre weak restriction is a source-defined
partial homomorphism. It need not reflect undefined applications. -/
theorem wholeWeakInclusion_originalPartial
    (A : PartialSetStructure L V) (S : Set V) :
    IsOriginalPartialHomomorphism (wholeWeakInduce A S) A Subtype.val := by
  constructor
  · intro R xs hRel
    exact hRel
  · intro F xs U hValue
    change wholeWeakValue S (A.func F (Subtype.val ∘ xs)) = some U at hValue
    obtain ⟨Q, hQ, hQS, rfl⟩ :=
      (wholeWeakValue_eq_some_iff S _ U).mp hValue
    rw [hQ]
    congr 1
    ext y
    constructor
    · intro hy
      exact ⟨⟨y, hQS hy⟩, hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx

/-- The literal map from a weak carrier onto its image. -/
def wholeWeakImageMap (f : V → W) (S : Set V) :
    S → Structure.imageSet f S :=
  fun x => ⟨f x.1, ⟨x.1, x.2, rfl⟩⟩

/-- The exact image of a whole-fibre weak test inherits the original
source-defined projection. The tested source set is never enlarged. -/
theorem IsOriginalPartialHomomorphism.wholeWeakImage
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f) (S : Set V) :
    IsOriginalPartialHomomorphism
      (wholeWeakInduce A S)
      (wholeWeakInduce B (Structure.imageSet f S))
      (wholeWeakImageMap f S) :=
  hf.wholeWeakRestrict S (Structure.imageSet f S)
    (wholeWeakImageMap f S) (fun _ => rfl)

/-- Whole-fibre deletion agrees with clipping when a value is either
wholly retained or wholly omitted. The originally empty case is retained
as defined-empty by both operations. -/
theorem wholeWeakValue_eq_weakValue_of_all_or_none
    (S U : Set V) (hU : U ⊆ S ∨ ¬ (U ∩ S).Nonempty) :
    wholeWeakValue S (some U) = weakValue S (some U) := by
  classical
  rcases hU with hSub | hDisjoint
  · rw [wholeWeakValue_of_subset S U hSub,
      weakValue_of_subset S U hSub]
  · by_cases hNonempty : U.Nonempty
    · have hNotSub : ¬ U ⊆ S := by
        intro hSub
        obtain ⟨x, hx⟩ := hNonempty
        exact hDisjoint ⟨x, hx, hSub hx⟩
      simp [wholeWeakValue, hNotSub, weakValue, hNonempty, hDisjoint]
    · have hEmpty : U = ∅ := by
        ext x
        constructor
        · intro hx
          exact (hNonempty ⟨x, hx⟩).elim
        · simp
      subst U
      simp

/-- Partially retaining a nonempty multivalued fibre separates the two
weak conventions. This is the precise obstruction to using a clipping
dictionary for the whole-fibre interpretation without an extra hypothesis. -/
theorem wholeWeakValue_ne_weakValue_of_partial
    (S U : Set V) (hMeet : (U ∩ S).Nonempty)
    (hEscape : ¬ U ⊆ S) :
    wholeWeakValue S (some U) ≠ weakValue S (some U) := by
  have hNonempty : U.Nonempty := by
    obtain ⟨x, hx, _⟩ := hMeet
    exact ⟨x, hx⟩
  simp [wholeWeakValue, hEscape, weakValue, hNonempty, hMeet]

end StructuralRamsey.PartialSetStructure
