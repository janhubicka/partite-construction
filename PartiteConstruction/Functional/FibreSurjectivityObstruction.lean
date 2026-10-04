import PartiteConstruction.Structure.WeakSubstructure
import PartiteConstruction.Structure.FreeAmalgam

/-! # Relational homomorphism-embeddings do not recover full function homomorphisms

The graph encoding forgets fibre surjectivity outside the image of the map.
This remains true even for an injective relational homomorphism-embedding.

The source has one vertex and an everywhere-empty unary partial function.
The target has two vertices and one value F(false) = {true}.  The injection of
the source vertex to false sees no function-graph tuple entirely inside its
image, so it is an induced embedding on every irreducible source subset and is
therefore a relational graph homomorphism-embedding.  It is nevertheless not a
full function homomorphism because the target fibre over false contains true,
which is outside the image.

This is the exact obstruction to deriving property (1) of the survey's
function-language sparsening theorem merely from the relational graph
projection.
-/

namespace StructuralRamsey.Structure.FibreSurjectivityObstruction

open StructuralRamsey

def language : Language where
  RelSymbol := Empty
  FuncSymbol := Unit
  relArity := Empty.elim
  funcArity _ := 1

def source : Structure language Unit where
  rel R := Empty.elim R
  func _ _ := ∅

def target : Structure language Bool where
  rel R := Empty.elim R
  func _ x := {y | x (0 : Fin 1) = false ∧ y = true}

def inject : Unit → Bool := fun _ => false

theorem inject_injective : Function.Injective inject := by
  intro x y _
  exact Subsingleton.elim x y

/-- The graph map is a relational homomorphism-embedding.  Extra function
values outside the image are invisible to induced relation reflection. -/
theorem inject_graph_homEmbedding :
    source.graph.IsHomomorphismEmbedding target.graph inject := by
  apply RelStructure.IsHomomorphismEmbedding.of_map_reflect
  · intro R x hx
    cases R with
    | inl R => exact Empty.elim R
    | inr F =>
        change False at hx
        exact hx.elim
  · intro S hS x hx y hy hxy
    exact inject_injective hxy
  · intro S hS R x hxS htarget
    cases R with
    | inl R => exact Empty.elim R
    | inr F =>
        change
          (inject (x (Fin.last 1)) ∈
            target.func ()
              (fun i : Fin 1 => inject (x i.castSucc))) at htarget
        change
          x (Fin.last 1) ∈
            source.func ()
              (fun i : Fin 1 => x i.castSucc)
        change False
        have hout : inject (x (Fin.last 1)) = false := rfl
        change
          (fun i : Fin 1 => inject (x i.castSucc)) 0 = false ∧
            inject (x (Fin.last 1)) = true at htarget
        exact Bool.noConfusion (hout.symm.trans htarget.2)

/-- The same injective map is not a full function homomorphism: the target
fibre over the image input has the extra value true. -/
theorem inject_not_full_homomorphism :
    ¬ source.IsHomomorphism target inject := by
  intro h
  have hf := h.2 () (fun _ : Fin 1 => ())
  have hy :
      true ∈ target.func () (inject ∘ (fun _ : Fin 1 => ())) := by
    change false = false ∧ true = true
    exact ⟨rfl, rfl⟩
  have himg :
      true ∈ imageSet inject (source.func () (fun _ : Fin 1 => ())) := by
    rw [hf]
    exact hy
  rcases himg with ⟨z, hz, _⟩
  change False at hz
  exact hz.elim

/-- Hence relational graph homomorphism-embedding is strictly weaker than the
survey's full function homomorphism-embedding. -/
theorem inject_not_full_homEmbedding :
    ¬ source.IsHomomorphismEmbedding target inject := by
  intro h
  exact inject_not_full_homomorphism h.1

end StructuralRamsey.Structure.FibreSurjectivityObstruction
