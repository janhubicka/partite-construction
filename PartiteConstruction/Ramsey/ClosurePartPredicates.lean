import PartiteConstruction.Ramsey.ClosureClosedLocalFiniteness
import PartiteConstruction.Partite.Basic

/-! # Relational part predicates, without an invalid closure-rule lift

Adding unary part predicates is harmless for full relational embeddings:
an embedding of part-labelled expansions is exactly a part-preserving
embedding of the underlying relational structures. It also preserves
ordinary Gaifman irreducibility because a unary tuple cannot connect
two distinct vertices.

IMPORTANT: No lifted closure description is introduced in this file.
Simply reusing the same old closure-relation symbol for separate roots
whose unary part assignments differ is NOT a valid lift of Definition
2.12: each rule independently requires EVERY closure tuple bearing its
symbol to match its own root. A correct root-sensitive transport must
split closure-relation symbols by the root part pattern, or prove an
equivalent partial-root semantics separately. Theorems in this file do
not claim preservation of U-closedness or of U-irreducibility.
-/

namespace StructuralRamsey

universe u v w z

namespace RelLanguage

/-- Add a unary predicate naming each part, without modifying the old
relation symbols. This is the plain relational presentation of parts;
it does not automatically transport a closure description. -/
def withPartPredicates (L : RelLanguage.{u}) (P : Type v) :
    RelLanguage.{max u v} where
  Symbol := L.Symbol ⊕ P
  arity
    | .inl R => L.arity R
    | .inr _ => 1

@[simp] theorem withPartPredicates_arity_original
    (L : RelLanguage.{u}) (P : Type v) (R : L.Symbol) :
    (L.withPartPredicates P).arity (.inl R) = L.arity R := rfl

@[simp] theorem withPartPredicates_arity_part
    (L : RelLanguage.{u}) (P : Type v) (p : P) :
    (L.withPartPredicates P).arity (.inr p) = 1 := rfl

end RelLanguage

namespace RelStructure

variable {L : RelLanguage.{u}}
variable {V : Type w} {W : Type z} {P : Type v}

/-- Expand a relational structure with exactly one unary part predicate
at each vertex. Old relation tuples are unchanged, including nullary
relations and tuples with repeated entries. -/
def expandPartPredicates (A : RelStructure L V) (part : V → P) :
    RelStructure (L.withPartPredicates P) V where
  rel
    | .inl R, xs => A.rel R xs
    | .inr p, xs => part (xs 0) = p

/-- Forget only the unary part predicates. -/
def forgetPartPredicates
    (B : RelStructure (L.withPartPredicates P) V) :
    RelStructure L V where
  rel R xs := B.rel (.inl R) xs

@[simp] theorem forget_expandPartPredicates
    (A : RelStructure L V) (part : V → P) :
    (A.expandPartPredicates part).forgetPartPredicates = A := by
  cases A
  rfl

/-- A full embedding respecting part labels extends to the language
with unary part predicates. -/
def Embedding.expandPartPredicates
    {A : RelStructure L V} {B : RelStructure L W}
    (e : Embedding A B) (partA : V → P) (partB : W → P)
    (hPart : ∀ x, partB (e x) = partA x) :
    Embedding (A.expandPartPredicates partA)
      (B.expandPartPredicates partB) where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R xs
    cases R with
    | inl R => exact e.map_rel_iff R xs
    | inr p =>
        change (partB (e (xs 0)) = p) ↔ (partA (xs 0) = p)
        rw [hPart]

/-- Forgetting part predicates recovers an ordinary full embedding. -/
def Embedding.forgetPartPredicates
    {A : RelStructure L V} {B : RelStructure L W}
    {partA : V → P} {partB : W → P}
    (e : Embedding (A.expandPartPredicates partA)
      (B.expandPartPredicates partB)) :
    Embedding A B where
  toFun := e
  injective := e.injective
  map_rel_iff R xs := e.map_rel_iff (.inl R) xs

/-- Every embedding of expansions automatically preserves every part
label. No supplementary part-preservation hypothesis is hidden. -/
theorem Embedding.expanded_preserves_part
    {A : RelStructure L V} {B : RelStructure L W}
    {partA : V → P} {partB : W → P}
    (e : Embedding (A.expandPartPredicates partA)
      (B.expandPartPredicates partB)) (x : V) :
    partB (e x) = partA x := by
  have h := (e.map_rel_iff (.inr (partA x)) (fun _ : Fin 1 => x)).mpr
    (show (A.expandPartPredicates partA).rel (.inr (partA x))
      (fun _ : Fin 1 => x) from rfl)
  exact h

/-- The two translations are inverse on the underlying embeddings. -/
theorem Embedding.forget_expandPartPredicates
    {A : RelStructure L V} {B : RelStructure L W}
    (e : Embedding A B) (partA : V → P) (partB : W → P)
    (hPart : ∀ x, partB (e x) = partA x) :
    (e.expandPartPredicates partA partB hPart).forgetPartPredicates = e := by
  ext x
  rfl

/-- Conversely, every expanded embedding is recovered using only its
underlying embedding and its forced part-label equation. -/
theorem Embedding.expand_forgetPartPredicates
    {A : RelStructure L V} {B : RelStructure L W}
    {partA : V → P} {partB : W → P}
    (e : Embedding (A.expandPartPredicates partA)
      (B.expandPartPredicates partB)) :
    (e.forgetPartPredicates).expandPartPredicates partA partB
      (e.expanded_preserves_part) = e := by
  ext x
  rfl

/-- Old ordinary irreducibility passes to the part-predicate expansion:
the original witnessing tuple remains a witnessing tuple. -/
theorem Irreducible.expandPartPredicates
    {A : RelStructure L V} (hA : A.Irreducible) (part : V → P) :
    (A.expandPartPredicates part).Irreducible := by
  intro x y hxy
  obtain ⟨R, t, i, j, ht, hi, hj⟩ := hA hxy
  exact ⟨.inl R, t, i, j, ht, hi, hj⟩

/-- Conversely, a unary part relation cannot witness adjacency of
distinct vertices, so adding part predicates does not create ordinary
Gaifman irreducibility. -/
theorem Irreducible.forgetPartPredicates_of_expanded
    {A : RelStructure L V} (part : V → P)
    (hA : (A.expandPartPredicates part).Irreducible) :
    A.Irreducible := by
  intro x y hxy
  obtain ⟨R, t, i, j, ht, hi, hj⟩ := hA hxy
  cases R with
  | inl R => exact ⟨R, t, i, j, ht, hi, hj⟩
  | inr p =>
      have hij : i = j := Subsingleton.elim i j
      exact False.elim (hxy (hi.symm.trans (hij ▸ hj)))

end RelStructure

namespace Partite

variable {L : RelLanguage.{u}} {P : Type v}
variable {V : Type w} {W : Type z}

/-- The unary part-predicate representation of a partite system. -/
def System.expandPartPredicates (B : System L P V) :
    RelStructure (L.withPartPredicates P) V :=
  B.toRelStructure.expandPartPredicates B.part

/-- Every partite embedding is precisely an expanded relational
embedding after forgetting the existing partite-system wrapper. -/
def Embedding.expandPartPredicates
    {B : System L P V} {C : System L P W}
    (e : Embedding B C) :
    RelStructure.Embedding B.expandPartPredicates
      C.expandPartPredicates :=
  e.toEmbedding.expandPartPredicates B.part C.part e.map_part

/-- Any expanded embedding has a unique compatible partite structure. -/
def Embedding.ofExpandedPartPredicates
    {B : System L P V} {C : System L P W}
    (e : RelStructure.Embedding B.expandPartPredicates
      C.expandPartPredicates) : Embedding B C where
  toEmbedding := e.forgetPartPredicates
  map_part := e.expanded_preserves_part

@[simp] theorem Embedding.ofExpanded_expandPartPredicates
    {B : System L P V} {C : System L P W}
    (e : Embedding B C) :
    (e.expandPartPredicates).ofExpandedPartPredicates = e := by
  ext x
  rfl

@[simp] theorem Embedding.expand_ofExpandedPartPredicates
    {B : System L P V} {C : System L P W}
    (e : RelStructure.Embedding B.expandPartPredicates
      C.expandPartPredicates) :
    (e.ofExpandedPartPredicates).expandPartPredicates = e := by
  apply RelStructure.Embedding.ext
  intro x
  rfl

end Partite
end StructuralRamsey
