import PartiteConstruction.Functional.WeakPatternDomainBridge2019

/-!
# Two-vertex unary regression: a weak test forgets its active U-root

The ambient structure has vertices 0,1 and one unary function
F(0)={1}. On the EXACT singleton weak carrier S={0}, no output of
F(0) survives, so its recomputed OLD function-domain predicate
becomes false. Yet the domain ROOT relation of the ambient OLD
pattern graph, induced on the same singleton, remains true.

This explicitly refutes the false identification
  patternGraph (weakInduce A S) = (patternGraph A).induce S.
The OUTPUT incidences of these two records still coincide
(WeakPatternDomainBridge2019), and closed S restores domain equality.

The example is genuinely singleton-valued and uses no binary
relations, so neither singleton function outputs nor ordinary
function-graph encoding alone can repair the missing U-root mask.
-/

namespace StructuralRamsey.Structure.WeakPatternDomainRegression

open StructuralRamsey.Structure

def lang : Language where
  RelSymbol := Empty
  FuncSymbol := Unit
  relArity := Empty.elim
  funcArity _ := 1

def ambient : Structure lang (Fin 2) where
  rel R _ := Empty.elim R
  func F xs := by
    cases F
    exact {y | xs (0 : Fin 1) = 0 ∧ y = 1}

def test : Set (Fin 2) := {x | x = 0}

def root : Fin 1 → test :=
  fun _ => ⟨0, rfl⟩

def pat : Language.FunctionInputPattern lang where
  symbol := ()
  rootSize := 1
  argMap := fun _ => 0
  onto := by
    intro a
    refine ⟨⟨0, by decide⟩, ?_⟩
    fin_cases a
    rfl

/-- The ambient domain root remains active after relational induced
restriction, but disappears when partial function values are first
weakly restricted and the domain predicate is recomputed. -/
theorem unary_missing_output_loses_domain :
    (ambient.patternGraph.induce test).rel (.inr (.inl pat)) root ∧
      ¬ (ambient.weakInduce test).patternGraph.rel
        (.inr (.inl pat)) root := by
  have hInjective : Function.Injective root := by
    intro i j _
    fin_cases i
    fin_cases j
    rfl
  have hActive :
      (ambient.func pat.symbol
        ((Subtype.val ∘ root) ∘ pat.argMap)).Nonempty := by
    refine ⟨1, ?_⟩
    change ((0 : Fin 2) = 0) ∧ ((1 : Fin 2) = 1)
    exact ⟨rfl, rfl⟩
  have hMissing : ∀ y,
      y ∈ ambient.func pat.symbol
        ((Subtype.val ∘ root) ∘ pat.argMap) →
      y ∉ test := by
    intro y hy hyS
    have hOne : y = (1 : Fin 2) := hy.2
    have hZero : y = (0 : Fin 2) := hyS
    exact (by decide : (1 : Fin 2) ≠ 0)
      (hOne.symm.trans hZero)
  exact patternGraph_domain_lost_of_missing_outputs
    ambient test pat root hInjective hActive hMissing

end StructuralRamsey.Structure.WeakPatternDomainRegression
