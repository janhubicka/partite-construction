import PartiteConstruction.Structure.WeakSubstructure

/-! # Weak images of weak substructures

For the vertex-size induction, the image of a weak test is again taken
weakly, on precisely the projected vertices. It is NOT the function-closed
hull of the projected vertices. This is the function-graph version of the
usual relational induced-image restriction of a homomorphism-embedding.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}} {V W : Type v}

/-- Restrict a weak homomorphism-embedding to an arbitrary weak source test,
with its target the weak substructure on the *set-theoretic image*. No
function closure is taken on either side. -/
theorem IsWeakHomomorphismEmbedding.weakImage
    {C : Structure L V} {D : Structure L W} {p : V → W}
    (hp : C.IsWeakHomomorphismEmbedding D p)
    (S : Set V) :
    (C.weakInduce S).IsWeakHomomorphismEmbedding
      (D.weakInduce (p '' S))
      (fun x : S => (⟨p x.1, ⟨x.1, x.2, rfl⟩⟩ : p '' S)) := by
  have hSource :
      (C.weakInduce S).graph.IsHomomorphismEmbedding D.graph
        (p ∘ Subtype.val) :=
    hp.comp (weakInclusion C S).isHomomorphismEmbedding
  have hImage :
      (C.weakInduce S).graph.IsHomomorphismEmbedding
        (D.graph.induce (p '' S))
        (fun x : S => (⟨p x.1, ⟨x.1, x.2, rfl⟩⟩ : p '' S)) :=
    hSource.codRestrict (p '' S) (fun x => ⟨x.1, x.2, rfl⟩)
  exact (weakGraphFromInduce D (p '' S)).isHomomorphismEmbedding.comp hImage

end StructuralRamsey.Structure
