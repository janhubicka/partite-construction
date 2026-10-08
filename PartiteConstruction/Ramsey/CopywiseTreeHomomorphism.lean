import PartiteConstruction.Ramsey.StrongAmalgamationTreeCompletion

/-! # Homomorphism-embedding completions via copywise strict-tree maps

A K-copywise completion of a strict B-tree need NOT be a homomorphism
on the whole tree. Nevertheless every irreducible substructure of the
tree lies inside a B-copy, and is thus embedded by the completion map.

Since each relation tuple has irreducible support, the map IS a
homomorphism-embedding on the entire tree. Consequently a
homomorphism-embedding from a small tested structure into the tree
can be composed with this map to give a genuine (K, U=empty)-completion.

The distinction between the weak image and its generated closure
never arises here: local tests are *exact* relational induced
substructures on the tested vertex sets.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {VB W X Y : Type v}

/-- The vertex set of one true relation tuple always induces an
irreducible substructure, including the nullary and unary cases. -/
theorem relationTuple_range_irreducible
    (T : RelStructure L W)
    (R : L.Symbol) (xs : Fin (L.arity R) → W)
    (h : T.rel R xs) :
    (T.induce (Set.range xs)).Irreducible := by
  intro a b hab
  obtain ⟨i,hi⟩ := a.2
  obtain ⟨j,hj⟩ := b.2
  let t : Fin (L.arity R) → Set.range xs :=
    fun k => ⟨xs k,⟨k,rfl⟩⟩
  refine ⟨R,t,i,j,?_,?_,?_⟩
  · change T.rel R (Subtype.val ∘ t)
    have ht : Subtype.val ∘ t = xs := rfl
    rw [ht]
    exact h
  · apply Subtype.ext
    exact hi.symm
  · apply Subtype.ext
    exact hj.symm

/-- Preserving all B-copies of a strict B-tree also preserves any
embedded *irreducible* structure. -/
theorem CopywiseCompletion.on_irreducible_of_strictTree
    {Base : RelStructure L VB}
    {T : RelStructure L W} {Target : RelStructure L X}
    {f : W → X}
    (hTree : TreeAmalgam Base W T)
    (hCopy : CopywiseCompletion Base T Target f)
    {Y : Type v} {E : RelStructure L Y}
    (hE : E.Irreducible)
    (e : Embedding E T) :
    ∃ e' : Embedding E Target, ∀ y, e' y = f (e y) := by
  classical
  obtain ⟨β,hβ⟩ :=
    hTree.irreducible_contained_in_copy hE e
  let eB : Embedding E Base := e.factorThroughRange β hβ
  obtain ⟨β',hβ'⟩ := hCopy β
  refine ⟨β'.comp eB, ?_⟩
  intro y
  calc
    (β'.comp eB) y = β' (eB y) := rfl
    _ = f (β (eB y)) := hβ' (eB y)
    _ = f (e y) := by
      apply congrArg f
      exact (Classical.choose_spec (hβ y)).symm

/-- The first nontrivial closure bridge for U=empty: a map that
preserves every B-copy in a strict B-tree is automatically a
relational homomorphism-embedding.

In particular it may identify vertices in reducible unions, but is
an honest induced embedding on every irreducible part. -/
theorem CopywiseCompletion.toHomomorphismEmbedding_of_strictTree
    {Base : RelStructure L VB}
    {T : RelStructure L W} {Target : RelStructure L X}
    {f : W → X}
    (hTree : TreeAmalgam Base W T)
    (hCopy : CopywiseCompletion Base T Target f) :
    T.IsHomomorphismEmbedding Target f := by
  constructor
  · intro R xs hx
    let S : Set W := Set.range xs
    let inc : Embedding (T.induce S) T :=
      inclusion T S
    have hS : (T.induce S).Irreducible :=
      relationTuple_range_irreducible T R xs hx
    obtain ⟨g,hg⟩ :=
      hCopy.on_irreducible_of_strictTree hTree hS inc
    let args : Fin (L.arity R) → S :=
      fun i => ⟨xs i,⟨i,rfl⟩⟩
    have hSource : (T.induce S).rel R args := by
      change T.rel R (Subtype.val ∘ args)
      simpa only [Function.comp_apply] using hx
    have hTarget : Target.rel R (g ∘ args) :=
      (g.map_rel_iff R args).mpr hSource
    have hargs : g ∘ args = f ∘ xs := by
      funext i
      exact hg (args i)
    rwa [hargs] at hTarget
  · intro S hS
    let inc : Embedding (T.induce S) T := inclusion T S
    obtain ⟨g,hg⟩ :=
      hCopy.on_irreducible_of_strictTree hTree hS inc
    exact ⟨g,hg⟩

/-- A finite target in K together with a genuine relational
homomorphism-embedding from the tested structure. In the 2019
terminology this is a (K,empty)-completion, provided K consists of
irreducible structures. -/
def HasKHomCompletion
    (K : StructureClass.{u,v} (L := L))
    (A : RelStructure L W) : Prop :=
  ∃ (X : Type v) (_ : Finite X) (Target : RelStructure L X),
    K Target ∧
    ∃ f : W → X, A.IsHomomorphismEmbedding Target f

/-- Every structure that homomorphism-embeds into a strict B-tree has
a finite (K,empty)-completion whenever B belongs to a finite
strong-amalgamation class K. -/
theorem HasTreeCompletion.toKCompletion
    {K : StructureClass.{u,v} (L := L)}
    {Base : RelStructure L VB} {A : RelStructure L W}
    [Finite VB]
    (hBase : Base.Irreducible)
    (hK : FiniteStrongAmalgamationClass K)
    (hB : K Base)
    (hTree : HasTreeCompletion Base A) :
    HasKHomCompletion K A := by
  obtain ⟨Y,T,hT,f,hf⟩ := hTree
  obtain ⟨X,hX,Q,hQ,g,hCopy⟩ :=
    hT.copywiseCompletion_inStrongClass hBase hK hB
  have hg : T.IsHomomorphismEmbedding Q g :=
    hCopy.toHomomorphismEmbedding_of_strictTree hT
  exact ⟨X,hX,Q,hQ,g ∘ f,hg.comp hf⟩

/-- An irreducible full substructure of a sparse witness belongs to
the hereditary target class K whenever all irreducibles extend to
some full B-copy, with B in K. -/
theorem IrreduciblesExtendTo.mem_irreducibles
    {K : StructureClass.{u,v} (L := L)}
    {Base : RelStructure L VB} {C : RelStructure L W}
    (hK : FiniteStrongAmalgamationClass K)
    (hBase : K Base)
    (hExt : IrreduciblesExtendTo Base C)
    {Y : Type v} (E : RelStructure L Y)
    (hE : E.Irreducible) (e : Embedding E C) :
    K E := by
  classical
  have hS : (C.induce (Set.range e)).Irreducible :=
    hE.range_embedding e
  obtain ⟨β,hβ⟩ := hExt (Set.range e) hS
  have hrange : ∀ y : Y, ∃ b : VB, e y = β b := by
    intro y
    exact hβ ⟨e y,⟨y,rfl⟩⟩
  let toBase : Embedding E Base := e.factorThroughRange β hrange
  exact hK.hereditary hBase toBase

end StructuralRamsey.RelStructure
