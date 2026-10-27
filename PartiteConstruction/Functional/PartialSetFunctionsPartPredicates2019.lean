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

end StructuralRamsey.PartialSetStructure
