import PartiteConstruction.Functional.DirectWeakIteration
import PartiteConstruction.Functional.WeakInvariant

/-! # Weak EHN projections act on induced function-graph substructures

The direct functional partite system only assumes a weak global projection,
full on genuine irreducible substructures.  This already yields the
*relational* homomorphism-embedding needed to test arbitrary weak
substructures after function-graph encoding.

The proof does **not** impose a U-closed condition on the partite stages.
For any irreducible weak graph test, its function-structure interpretation
is irreducible in the full functional sense. Its image in the ambient
structure can be completed to a closed irreducible hull. The EHN condition
embeds that hull fully into the target, and restriction gives the required
induced graph embedding of the original weak test.

This identifies the weak/graph projection interface required to import
relational size induction into the native functional partite construction.
It does not, on its own, make the output tree witnesses strict functional
tree amalgams or the weak projection fibre-surjective.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {V P : Type v}

/-- Every EHN weak projection of genuine function structures is a
relational homomorphism-embedding between their function graphs.
The local induced embedding is found through a closed irreducible hull,
not by replacing the whole partite construction with U-closed graphs. -/
theorem IsEHNHomomorphismEmbedding.graphHomomorphismEmbedding
    {C : Structure L V} {D : Structure L P}
    {p : V → P}
    (hp : C.IsEHNHomomorphismEmbedding D p) :
    C.graph.IsHomomorphismEmbedding D.graph p := by
  classical
  constructor
  · intro R z hz
    cases R with
    | inl R =>
        exact hp.1.1 R z hz
    | inr F =>
        change
          p (z (Fin.last (L.funcArity F))) ∈
            D.func F (fun i : Fin (L.funcArity F) => p (z i.castSucc))
        change z (Fin.last (L.funcArity F)) ∈
          C.func F (fun i : Fin (L.funcArity F) => z i.castSucc) at hz
        exact hp.1.2 F (fun i => z i.castSucc)
          (z (Fin.last (L.funcArity F))) hz
  · intro S hS
    let W : Structure L S := C.weakInduce S
    have hWGraph : W.graph.Irreducible := by
      intro x y hxy
      obtain ⟨R, z, i, j, hz, hzi, hzj⟩ := hS hxy
      exact ⟨R, z, i, j, (weakInduce_graph_rel_iff C S R z).mpr hz,
        hzi, hzj⟩
    have hW : W.Irreducible :=
      irreducible_of_graph_irreducible W hWGraph
    let q : S → V := Subtype.val
    have hq : W.IsWeakHomomorphism C q := by
      constructor
      · intro R z hz
        exact hz
      · intro F z y hy
        exact hy
    let HSet : Set V := C.functionClosure (Set.range q)
    let hHSet : C.IsClosed HSet :=
      C.functionClosure_isClosed (Set.range q)
    let H : Structure L HSet := C.induce HSet hHSet
    have hH : H.Irreducible := hW.functionClosure_weakImage hq
    let inc : Embedding H C := inclusion C HSet hHSet
    obtain ⟨g, hg⟩ := hp.2 H hH inc
    have hs (x : S) : x.1 ∈ HSet :=
      C.subset_functionClosure (Set.range q) ⟨x, rfl⟩
    let j : RelStructure.Embedding (C.graph.induce S) H.graph := {
      toFun := fun x => ⟨x.1, hs x⟩
      injective := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun t : HSet => t.1) hxy
      map_rel_iff := by
        intro R z
        cases R with
        | inl R => rfl
        | inr F => rfl
    }
    let e : RelStructure.Embedding (C.graph.induce S) D.graph :=
      g.graph.comp j
    refine ⟨e, ?_⟩
    intro x
    change g ⟨x.1, hs x⟩ = p x.1
    exact hg ⟨x.1, hs x⟩

end StructuralRamsey.Structure
