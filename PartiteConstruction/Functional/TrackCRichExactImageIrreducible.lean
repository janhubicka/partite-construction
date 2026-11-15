import PartiteConstruction.Functional.TrackCOptionFullExactRange
import PartiteConstruction.Functional.TrackCOptionIrredNative

/-!
# Track C: rich closed-free irreducibility is invariant under full isomorphism

For genuinely partial Option(Set) functions, a defined empty input
can block a free cut even though its output set is empty. The
closed-free-cover irreducibility predicate therefore must be
transported under FULL genuine partial embeddings, not under the
domain-forgetting native collapse.

A full embedding that is surjective is an actual same-carrier
isomorphism. We prove directly that it transports domain-aware
closed-free-cover irreducibility: pull back both closed sides,
transport relation tuples and complete source-defined operations
via full map_func, and use surjectivity to return the whole-side
conclusion. No finiteness, nonempty-value, or arity assumption.

In particular, the exact image of any full embedding of a genuinely
rich irreducible source is rich irreducible under the literal whole
weak restriction. The full exact-image factor from merged #701
preserves none vs some(empty) without enlarging the vertex budget.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V : Type v}

/-- Domain-aware closed-free irreducibility passes along a SURJECTIVE
full genuine partial embedding. The proof only uses the exact
Option-valued full map and the same source and target vertices. -/
theorem IsOptionClosedFreeIrreducible.of_surjectiveFullEmbedding
    {A : PartialSetStructure L U}
    {B : PartialSetStructure L V}
    (hA : A.IsOptionClosedFreeIrreducible)
    (e : Embedding A B)
    (hsurj : Function.Surjective e.toFun) :
    B.IsOptionClosedFreeIrreducible := by
  classical
  intro S T hS hT hCoverage hRelations hDefined
  let S' : Set U := e.toFun ⁻¹' S
  let T' : Set U := e.toFun ⁻¹' T
  have hPreimageClosed (Q : Set V) (hQ : B.IsClosed Q) :
      A.IsClosed (e.toFun ⁻¹' Q) := by
    intro F xs R hArgs hVal
    have hMap : B.func F (e.toFun ∘ xs) =
        some (Structure.imageSet e.toFun R) := by
      simpa only [hVal, Option.map_some] using (e.map_func F xs).symm
    have hOut : Structure.imageSet e.toFun R ⊆ Q :=
      hQ F (e.toFun ∘ xs) (Structure.imageSet e.toFun R)
        hArgs hMap
    intro x hx
    exact hOut ⟨x, hx, rfl⟩
  have hCoverage' : ∀ x : U, x ∈ S' ∨ x ∈ T' := by
    intro x
    exact hCoverage (e.toFun x)
  have hRelations' :
      ∀ (R : L.RelSymbol) (xs : Fin (L.relArity R) → U),
        A.rel R xs →
        (∀ i, xs i ∈ S') ∨ (∀ i, xs i ∈ T') := by
    intro R xs hRel
    have hRelB : B.rel R (e.toFun ∘ xs) :=
      (e.map_rel_iff R xs).mpr hRel
    exact hRelations R (e.toFun ∘ xs) hRelB
  have hDefined' :
      ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → U)
        (R : Set U), A.func F xs = some R →
        (∀ i, xs i ∈ S') ∨ (∀ i, xs i ∈ T') := by
    intro F xs R hSome
    have hSomeB : B.func F (e.toFun ∘ xs) =
        some (Structure.imageSet e.toFun R) := by
      simpa only [hSome, Option.map_some] using (e.map_func F xs).symm
    exact hDefined F (e.toFun ∘ xs)
      (Structure.imageSet e.toFun R) hSomeB
  rcases hA S' T'
      (hPreimageClosed S hS) (hPreimageClosed T hT)
      hCoverage' hRelations' hDefined' with hAllS | hAllT
  · left
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    have hMem : e.toFun x ∈ S := hAllS x
    rwa [hx] at hMem
  · right
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    have hMem : e.toFun x ∈ T := hAllT x
    rwa [hx] at hMem

/-- A full genuinely partial E-copy has an EXACT rich irreducible
whole-weak image, on its literal vertex range, whenever E itself is
closed-free irreducible. This uses no closure hull or collapseDomain
and includes source-defined-empty applications. -/
theorem IsOptionClosedFreeIrreducible.exactWholeWeakRange
    {E : PartialSetStructure L U}
    {A : PartialSetStructure L V}
    (hE : E.IsOptionClosedFreeIrreducible)
    (e : Embedding E A) :
    (A.wholeWeakInduce (Set.range e.toFun)).IsOptionClosedFreeIrreducible := by
  classical
  let eWeak : Embedding E (A.wholeWeakInduce (Set.range e.toFun)) :=
    e.codRestrictWholeWeakRange
  have hSurj : Function.Surjective eWeak.toFun := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change e.toFun x = y.1
    exact hx
  exact hE.of_surjectiveFullEmbedding eWeak hSurj

end StructuralRamsey.PartialSetStructure
