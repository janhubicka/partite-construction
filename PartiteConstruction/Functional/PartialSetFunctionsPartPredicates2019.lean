import PartiteConstruction.Functional.PartPredicates
import PartiteConstruction.Structure.PartialSetFunctionsTransversal
import PartiteConstruction.Functional.WholeMaskCanonicalFullEmbeddingForward2019

/-!
# Named part predicates on genuine Option(Set) structures

The verified 2019 two-pass sparsening theorem is RELATIONAL. A
canonical complete-mask OLD graph still treats the actual vertex-part
map as external data: its full embeddings need not preserve the parts
of isolated vertices. This prevents blindly interpreting an arbitrary
unlabelled relational Ramsey arrow as an arrow for PARTITE functional
embeddings.

The solution is the same as in the published partite construction:
expand the GENUINE partial-function language by unary part predicates
BEFORE forming complete-mask graphs, root tags and closure profiles.
Every source vertex carries its one actual part label. Full embeddings
of this expanded language automatically preserve original part labels.

The expansion does not change the underlying vertex set, the original
genuine Option(Set) operations, any generated closure, or weak tests.
It retains the distinction none versus some empty, and works for
multivalued functions and repeated input arguments.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {P : Type v}
variable {V W : Type w}

/-- The original genuine partial functions, with one unary relation
predicate naming the part of every vertex. No function input or output
is altered and no vertices are introduced. -/
def withParts (A : PartialSetStructure L V) (part : V → P) :
    PartialSetStructure (L.withParts P) V where
  rel
    | .inl R, x => A.rel R.down x
    | .inr p, x => part (x (0 : Fin 1)) = p
  func F x := A.func F.down x

/-- The expansion keeps the entire Option(Set) value for each primitive
function, including a genuinely defined-empty operation. -/
@[simp] theorem withParts_func (A : PartialSetStructure L V)
    (part : V → P) (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V) :
    (A.withParts part).func (ULift.up F) x = A.func F x := rfl

/-- A part-labelled structure retains exactly the original vertex
closure under defined function values, including nullary functions.
Only the relation language was expanded. -/
theorem withParts_isClosed_iff
    (A : PartialSetStructure L V) (part : V → P) (S : Set V) :
    (A.withParts part).IsClosed S ↔ A.IsClosed S := by
  constructor
  · intro h F xs T hxs hVal y hy
    exact h (ULift.up F) xs T hxs hVal hy
  · intro h F xs T hxs hVal y hy
    exact h F.down xs T hxs hVal hy

/-- Output transversality is literally unchanged by naming the input
vertex parts as unary relations. -/
theorem withParts_fibreTransversal_iff
    (A : PartialSetStructure L V) (part : V → P) :
    FibreTransversal (A.withParts part) part ↔
      FibreTransversal A part := by
  constructor
  · intro h F x T hValue y hy z hz hp
    exact h (ULift.up F) x T hValue y hy z hz hp
  · intro h F x T hValue y hy z hz hp
    exact h F.down x T hValue y hy z hz hp

/-- Every FULL genuine partial-function embedding respecting vertex
parts lifts to a FULL embedding of the expanded function structures.
The same map preserves and reflects defined-empty and undefined input
states, never adding a closure vertex. -/
def Embedding.withParts
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : Embedding A B)
    (partA : V → P) (partB : W → P)
    (hPart : ∀ x, partB (e.toFun x) = partA x) :
    Embedding (A.withParts partA) (B.withParts partB) where
  toFun := e.toFun
  injective := e.injective
  map_rel_iff := by
    intro R xs
    cases R with
    | inl R =>
        exact e.map_rel_iff R.down xs
    | inr p =>
        change
          (partB (e.toFun (xs (0 : Fin 1))) = p) ↔
          (partA (xs (0 : Fin 1)) = p)
        rw [hPart]
  map_func := by
    intro F xs
    exact e.map_func F.down xs

/-- A full embedding of the expanded function language necessarily
respects the original part label of EVERY vertex, including isolated
vertices that are not mentioned in an OLD complete output tuple. -/
theorem Embedding.withParts_preserves_part
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (partA : V → P) (partB : W → P)
    (e : Embedding (A.withParts partA) (B.withParts partB)) (x : V) :
    partB (e.toFun x) = partA x := by
  have h := (e.map_rel_iff (.inr (partA x)) (fun _ : Fin 1 => x)).mpr
    (show (A.withParts partA).rel (.inr (partA x))
      (fun _ : Fin 1 => x) from rfl)
  exact h

/-- Forgetting the part predicates gives a FULL genuine
Option(Set) embedding on the original vertex set and function symbols. -/
def Embedding.forgetParts
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {partA : V → P} {partB : W → P}
    (e : Embedding (A.withParts partA) (B.withParts partB)) :
    Embedding A B where
  toFun := e.toFun
  injective := e.injective
  map_rel_iff R xs := e.map_rel_iff (.inl (ULift.up R)) xs
  map_func F xs := e.map_func (ULift.up F) xs

/-- Naming every vertex's part does not affect the ACTUAL closure
of the original genuine partial functions on any vertex seed. -/
theorem withParts_functionClosure_eq
    (A : PartialSetStructure L V) (part : V → P) (S : Set V) :
    (A.withParts part).functionClosure S = A.functionClosure S := by
  apply Set.Subset.antisymm
  · exact (A.withParts part).functionClosure_least
      ((A.withParts_isClosed_iff part _).mpr
        (A.functionClosure_isClosed S))
      (A.subset_functionClosure S)
  · exact A.functionClosure_least
      ((A.withParts_isClosed_iff part _).mp
        ((A.withParts part).functionClosure_isClosed S))
      ((A.withParts part).subset_functionClosure S)

/-- Whole-fibre weak restriction commutes with the unary part expansion
on the ENTIRE Option(Set) value (not merely individual incidences).
A deleted nonempty value becomes none, and some empty stays defined. -/
theorem withParts_wholeWeak_func
    (A : PartialSetStructure L V) (part : V → P)
    (S : Set V)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S) :
    (wholeWeakInduce (A.withParts part) S).func (ULift.up F) xs =
      (wholeWeakInduce A S).func F xs := rfl

/-- The SAME exact weak subset of the expanded source has the SAME
intrinsic closure under surviving whole function fibres, independent
of the additional unary part labels. -/
theorem withParts_wholeWeak_functionClosure_eq
    (A : PartialSetStructure L V) (part : V → P)
    (S : Set V) (G : Set S) :
    (wholeWeakInduce (A.withParts part) S).functionClosure G =
      (wholeWeakInduce A S).functionClosure G := by
  apply Set.Subset.antisymm
  · apply (wholeWeakInduce (A.withParts part) S).functionClosure_least
    · intro F xs T hxs hFunc y hy
      exact (wholeWeakInduce A S).functionClosure_isClosed G
        F.down xs T hxs hFunc hy
    · exact (wholeWeakInduce A S).subset_functionClosure G
  · apply (wholeWeakInduce A S).functionClosure_least
    · intro F xs T hxs hFunc y hy
      exact (wholeWeakInduce (A.withParts part) S).functionClosure_isClosed G
        (ULift.up F) xs T hxs hFunc hy
    · exact (wholeWeakInduce (A.withParts part) S).subset_functionClosure G

/-- Hence the weak generator count is unchanged on EXACTLY the tested
vertex carrier. This is the bookkeeping needed to apply the verified
2019 profile-sparsening theorem after adding part predicates. -/
theorem withParts_wholeWeak_generatedByAtMost_iff
    (A : PartialSetStructure L V) (part : V → P)
    (S : Set V) (n : ℕ) :
    (wholeWeakInduce (A.withParts part) S).GeneratedByAtMost n ↔
      (wholeWeakInduce A S).GeneratedByAtMost n := by
  constructor
  · rintro ⟨G, hCard, hGenerated⟩
    refine ⟨G, hCard, ?_⟩
    change (wholeWeakInduce A S).functionClosure
      (↑G : Set S) = Set.univ
    rw [← A.withParts_wholeWeak_functionClosure_eq part S (↑G : Set S)]
    exact hGenerated
  · rintro ⟨G, hCard, hGenerated⟩
    refine ⟨G, hCard, ?_⟩
    change (wholeWeakInduce (A.withParts part) S).functionClosure
      (↑G : Set S) = Set.univ
    rw [A.withParts_wholeWeak_functionClosure_eq part S (↑G : Set S)]
    exact hGenerated

/-- Full partial-function embeddings are determined by their vertex
maps. Other fields are propositions, so no chosen proof data remains. -/
@[ext] theorem Embedding.ext
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f g : Embedding A B}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f with
  | mk f fi fr fv =>
    cases g with
    | mk g gi gr gv =>
      have heq : f = g := funext h
      cases heq
      rfl

/-- Adding and then forgetting part predicates returns the SAME full
partial embedding on its original vertex map. -/
theorem Embedding.forget_withParts
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : Embedding A B)
    (partA : V → P) (partB : W → P)
    (hPart : ∀ x, partB (e.toFun x) = partA x) :
    (e.withParts partA partB hPart).forgetParts = e := by
  apply Embedding.ext
  intro x
  rfl

/-- Every full embedding between PART-LABELLED genuine partial
structures is exactly a full part-preserving embedding of the
original structures, on the SAME vertices. -/
def Embedding.withPartsEquiv
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (partA : V → P) (partB : W → P) :
    {e : Embedding A B // ∀ x, partB (e.toFun x) = partA x} ≃
      Embedding (A.withParts partA) (B.withParts partB) where
  toFun e := e.1.withParts partA partB e.2
  invFun f := ⟨f.forgetParts, f.withParts_preserves_part partA partB⟩
  left_inv := by
    intro f
    apply Subtype.ext
    apply Embedding.ext
    intro x
    rfl
  right_inv := by
    intro f
    apply Embedding.ext
    intro x
    rfl

end StructuralRamsey.PartialSetStructure
