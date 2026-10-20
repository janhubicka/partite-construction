import PartiteConstruction.Structure.PartialSetFunctionsWholeWeak
import PartiteConstruction.Structure.GeneratedWeakHomImage

/-!
# Vertex closure for genuinely partial set-valued operations

The independent domain bit distinguishes `none` from `some ∅`. Both states
force no new vertex into a closed set, so `collapseDomain` preserves vertex
closure exactly. It does not preserve all domain-sensitive information.

We reuse the native closure operation only for this vertex-closure purpose.
The whole-fibre weak closedness criterion below requires the ENTIRE original
value to be retained. It does not assert the analogous clipping criterion.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- Forgetting independent definedness preserves precisely vertex closedness.
It need not preserve the original operation domains or full-map semantics. -/
theorem isClosed_iff_collapseDomain_isClosed
    (A : PartialSetStructure L V) (S : Set V) :
    A.IsClosed S ↔ A.collapseDomain.IsClosed S := by
  constructor
  · intro h F x hx y hy
    cases hF : A.func F x with
    | none =>
        change y ∈ (A.func F x).getD ∅ at hy
        simp [hF] at hy
    | some U =>
        have hyU : y ∈ U := by
          simpa [collapseDomain, hF] using hy
        exact h F x U hx hF hyU
  · intro h F x U hx hF y hy
    apply h F x hx
    change y ∈ (A.func F x).getD ∅
    simpa [hF] using hy

/-- Least vertex set closed under all defined partial operations and
containing the given seed. Domain information is retained in A itself. -/
def functionClosure (A : PartialSetStructure L V) (S : Set V) : Set V :=
  A.collapseDomain.functionClosure S

/-- The reused native closure is exactly the intersection of the original
partial-function-closed supersets, including for nullary operations. -/
theorem mem_functionClosure_iff
    (A : PartialSetStructure L V) (S : Set V) (x : V) :
    x ∈ A.functionClosure S ↔
      ∀ T : Set V, A.IsClosed T → S ⊆ T → x ∈ T := by
  constructor
  · intro hx T hT hST
    exact hx T ((isClosed_iff_collapseDomain_isClosed A T).mp hT) hST
  · intro hx T hT hST
    exact hx T ((isClosed_iff_collapseDomain_isClosed A T).mpr hT) hST

theorem subset_functionClosure (A : PartialSetStructure L V) (S : Set V) :
    S ⊆ A.functionClosure S :=
  A.collapseDomain.subset_functionClosure S

theorem functionClosure_isClosed (A : PartialSetStructure L V) (S : Set V) :
    A.IsClosed (A.functionClosure S) :=
  (isClosed_iff_collapseDomain_isClosed A _).mpr
    (A.collapseDomain.functionClosure_isClosed S)

theorem functionClosure_least
    (A : PartialSetStructure L V) {S T : Set V}
    (hT : A.IsClosed T) (hST : S ⊆ T) :
    A.functionClosure S ⊆ T := by
  intro x hx
  exact (mem_functionClosure_iff A S x).mp hx T hT hST

theorem functionClosure_mono
    (A : PartialSetStructure L V) {S T : Set V} (hST : S ⊆ T) :
    A.functionClosure S ⊆ A.functionClosure T :=
  A.functionClosure_least (A.functionClosure_isClosed T)
    (hST.trans (A.subset_functionClosure T))

theorem functionClosure_eq_of_isClosed
    (A : PartialSetStructure L V) {S : Set V} (hS : A.IsClosed S) :
    A.functionClosure S = S :=
  Set.Subset.antisymm (A.functionClosure_least hS (Set.Subset.refl S))
    (A.subset_functionClosure S)

@[simp] theorem functionClosure_idem
    (A : PartialSetStructure L V) (S : Set V) :
    A.functionClosure (A.functionClosure S) = A.functionClosure S :=
  A.functionClosure_eq_of_isClosed (A.functionClosure_isClosed S)

/-- A seed generates all vertices under the defined partial operations. -/
def GeneratedBy (A : PartialSetStructure L V) (S : Set V) : Prop :=
  A.functionClosure S = Set.univ

/-- Generation by at most n literal vertices, without charging the size
of the possibly larger generated hull. -/
def GeneratedByAtMost (A : PartialSetStructure L V) (n : ℕ) : Prop :=
  ∃ S : Finset V, S.card ≤ n ∧ A.GeneratedBy (↑S : Set V)

theorem GeneratedByAtMost.mono
    {A : PartialSetStructure L V} {m n : ℕ}
    (h : A.GeneratedByAtMost m) (hmn : m ≤ n) :
    A.GeneratedByAtMost n := by
  obtain ⟨S, hS, hGen⟩ := h
  exact ⟨S, hS.trans hmn, hGen⟩

theorem GeneratedByAtMost.of_fintype
    (A : PartialSetStructure L V) [Fintype V] :
    A.GeneratedByAtMost (Fintype.card V) := by
  classical
  refine ⟨Finset.univ, by simp, ?_⟩
  change A.functionClosure (↑(Finset.univ : Finset V) : Set V) = Set.univ
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro x _
  exact A.subset_functionClosure _ (by simp)

/-- Intrinsic closedness on an exact whole-fibre weak carrier. Only complete
ambient values contained in S impose a closure requirement inside S. -/
theorem wholeWeakInduce_isClosed_iff
    (A : PartialSetStructure L V) (S : Set V) (Q : Set S) :
    (wholeWeakInduce A S).IsClosed Q ↔
      ∀ (F : L.FuncSymbol) (x : Fin (L.funcArity F) → S) (U : Set V),
        (∀ i, x i ∈ Q) → A.func F (Subtype.val ∘ x) = some U →
        U ⊆ S → ∀ y : S, y.1 ∈ U → y ∈ Q := by
  constructor
  · intro h F x U hx hValue hUS y hy
    have hWeak : (wholeWeakInduce A S).func F x =
        some {z : S | z.1 ∈ U} := by
      change wholeWeakValue S (A.func F (Subtype.val ∘ x)) = _
      rw [hValue]
      exact wholeWeakValue_of_subset S U hUS
    exact h F x _ hx hWeak hy
  · intro h F x U hx hValue
    change wholeWeakValue S (A.func F (Subtype.val ∘ x)) = some U at hValue
    obtain ⟨T, hT, hTS, rfl⟩ :=
      (wholeWeakValue_eq_some_iff S (A.func F (Subtype.val ∘ x)) U).mp hValue
    intro y hy
    exact h F x T hx hT hTS y hy

/-- Source-defined homomorphisms pull closed vertex sets back to closed
sets. Undefined source applications require no reflection. -/
theorem IsOriginalPartialHomomorphism.preimage_isClosed
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W} (hf : IsOriginalPartialHomomorphism A B f)
    (T : Set W) (hT : B.IsClosed T) :
    A.IsClosed (f ⁻¹' T) := by
  intro F x U hx hValue y hy
  exact hT F (f ∘ x) (Structure.imageSet f U) hx
    (hf.2 F x U hValue) ⟨y, hy, rfl⟩

/-- The image of a source closure is contained in the target closure of
the image seed; target undefinedness reflection is unnecessary. -/
theorem IsOriginalPartialHomomorphism.image_functionClosure_subset
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W} (hf : IsOriginalPartialHomomorphism A B f)
    (S : Set V) :
    f '' A.functionClosure S ⊆ B.functionClosure (f '' S) := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_functionClosure_iff A S x).mp hx
    (f ⁻¹' B.functionClosure (f '' S))
    (hf.preimage_isClosed _ (B.functionClosure_isClosed (f '' S)))
    (fun y hy => B.subset_functionClosure (f '' S) ⟨y, hy, rfl⟩)

/-- A surjective source-defined partial homomorphism cannot increase the
number of generators, even when it identifies output vertices. -/
theorem GeneratedByAtMost.of_surjective_originalPartialHomomorphism
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W} {n : ℕ}
    (hGen : A.GeneratedByAtMost n)
    (hf : IsOriginalPartialHomomorphism A B f)
    (hSurj : Function.Surjective f) :
    B.GeneratedByAtMost n := by
  classical
  obtain ⟨S, hCard, hSGen⟩ := hGen
  let G : Finset W := S.image f
  refine ⟨G, (Finset.card_image_le).trans hCard, ?_⟩
  change B.functionClosure (↑G : Set W) = Set.univ
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro y _
  obtain ⟨x, rfl⟩ := hSurj y
  have hx : x ∈ A.functionClosure (↑S : Set V) := by
    change A.functionClosure (↑S : Set V) = Set.univ at hSGen
    rw [hSGen]
    exact Set.mem_univ x
  have hImage : f x ∈ B.functionClosure (f '' (↑S : Set V)) :=
    hf.image_functionClosure_subset (↑S : Set V) ⟨x, hx, rfl⟩
  apply B.functionClosure_mono (S := f '' (↑S : Set V))
    (T := (↑G : Set W)) ?_ hImage
  rintro _ ⟨a, ha, rfl⟩
  exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

/-- The exact image of an exact whole-fibre weak test has no larger
intrinsic generator bound. Neither weak carrier is replaced by its
ambient function-closed hull. -/
theorem IsOriginalPartialHomomorphism.wholeWeakImage_generatedByAtMost
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W} (hf : IsOriginalPartialHomomorphism A B f)
    (S : Set V) {n : ℕ}
    (hGen : (wholeWeakInduce A S).GeneratedByAtMost n) :
    (wholeWeakInduce B (Structure.imageSet f S)).GeneratedByAtMost n := by
  apply hGen.of_surjective_originalPartialHomomorphism (hf.wholeWeakImage S)
  intro y
  obtain ⟨x, hx, hxy⟩ := y.2
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hxy

end StructuralRamsey.PartialSetStructure
