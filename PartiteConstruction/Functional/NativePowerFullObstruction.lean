import PartiteConstruction.Functional.NativePowerConcreteStage

/-! # No full strict-tree homomorphism from the concrete native power

The actual tagged second power of the seven-vertex 3-edge stage contains
the staircase function-domain matrix. Any full function homomorphism
preserves and reflects *domain nonemptiness*, so its six selected inputs
would map to a 4-cycle in the domain relation of a strict full
B-tree. The latter is square-free by `strictTree_squareFree`.

The stronger **12-vertex closed-test** counterexample and the proof
that the seven-vertex stage is a genuine strict B-tree with EHN
projection remain separate obligations.
-/

namespace StructuralRamsey.Structure.NativePowerObstruction

open StructuralRamsey.Structure

/-- Full functional homomorphisms preserve and reflect nonempty fibres. -/
theorem domain_fullHom_iff
    {U W : Type}
    {S : Structure toyLanguage U} {T : Structure toyLanguage W}
    {f : U → W}
    (hf : S.IsHomomorphism T f) (x y : U) :
    Domain T (f x) (f y) ↔ Domain S x y := by
  have htuple : f ∘ ![x, y] = ![f x, f y] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · rintro ⟨z, hz⟩
    have hzT : z ∈ T.func () (f ∘ ![x, y]) :=
      Eq.mp (congrArg
        (fun a : Fin 2 → W => z ∈ T.func () a) htuple.symm) hz
    rw [← hf.2 () ![x, y]] at hzT
    rcases hzT with ⟨w, hw, _⟩
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    have hImage : f w ∈ imageSet f (S.func () ![x, y]) :=
      ⟨w, hw, rfl⟩
    rw [hf.2 () ![x, y]] at hImage
    refine ⟨f w, ?_⟩
    exact Eq.mp (congrArg
      (fun a : Fin 2 → W => f w ∈ T.func () a) htuple) hImage

theorem powerX_hasRole (i : Fin 3) :
    Role actualPower 0 (powerX i) := by
  change ∀ k : Fin 2, oldPart ((powerX i).coord k) = 0
  intro k
  exact (powerX i).belongs k

theorem powerY_hasRole (j : Fin 3) :
    Role actualPower 1 (powerY j) := by
  change ∀ k : Fin 2, oldPart ((powerY j).coord k) = 1
  intro k
  exact (powerY j).belongs k

/-- The genuine tagged second power has no full homomorphism to any
strict functional tree of copies of the 3-vertex binary-function
template. This is an unconditional obstruction for that power,
not yet the bounded closed-test version. -/
theorem actualPower_no_fullStrictTreeHom
    {W : Type} {T : Structure toyLanguage W}
    (hTree : TreeAmalgam toyBase W T)
    (f : FunctionalPartite.Induced.Vertex oldSystem 2 → W)
    (hf : actualPower.IsHomomorphism T f) : False := by
  let XRole := {x : W // Role T 0 x}
  let YRole := {y : W // Role T 1 y}
  let R : XRole → YRole → Prop :=
    fun x y => Domain T x.1 y.1
  have hNoSquare : NoSquare R := by
    intro x₁ x₂ y₁ y₂ hxx hyy h₁₁ h₁₂ h₂₁ h₂₂
    have hxx' : x₁.1 ≠ x₂.1 := by
      intro h
      exact hxx (Subtype.ext h)
    have hyy' : y₁.1 ≠ y₂.1 := by
      intro h
      exact hyy (Subtype.ext h)
    exact (strictTree_squareFree hTree)
      x₁.1 x₂.1 y₁.1 y₂.1
      x₁.2 x₂.2 y₁.2 y₂.2 hxx' hyy'
      h₁₁ h₁₂ h₂₁ h₂₂
      trivial trivial trivial trivial
  let fx : Fin 3 → XRole :=
    fun i => ⟨f (powerX i), by
      exact hf.1 (0 : Fin 3) (fun _ => powerX i) (powerX_hasRole i)⟩
  let fy : Fin 3 → YRole :=
    fun j => ⟨f (powerY j), by
      exact hf.1 (1 : Fin 3) (fun _ => powerY j) (powerY_hasRole j)⟩
  apply actualPower_noSquareTarget R hNoSquare fx fy
  intro i j
  exact domain_fullHom_iff hf (powerX i) (powerY j)


/-- The entire concrete native second power already has no strict full B-tree
completion. It is a genuine finite function structure, so the full carrier
is automatically a function-closed test. -/
theorem actualPower_no_fullTreeCompletion :
    ¬ Structure.HasTreeCompletion toyBase actualPower := by
  rintro ⟨W, T, hTree, f, hf⟩
  exact actualPower_no_fullStrictTreeHom hTree f hf.1

/-- A finite-rank obstruction to a generic strict functional sparsening
invariant. The rank is the cardinal of the concrete tagged second power;
the separately exhibited twelve-vertex closed test sharpens this bound. -/
theorem actualPower_not_locallyStrictTreeCompletable :
    ¬ Structure.LocallyClosedTreeCompletable toyBase actualPower
        (Nat.card (FunctionalPartite.Induced.Vertex oldSystem 2)) := by
  intro hLocal
  letI : Fintype (FunctionalPartite.Induced.Vertex oldSystem 2) :=
    Fintype.ofFinite _
  have hcard :
      Fintype.card (FunctionalPartite.Induced.Vertex oldSystem 2) ≤
        Nat.card (FunctionalPartite.Induced.Vertex oldSystem 2) := by
    simp only [Nat.card_eq_fintype_card]
    exact Nat.le_refl _
  exact actualPower_no_fullTreeCompletion (hLocal.fullWitness hcard)

end StructuralRamsey.Structure.NativePowerObstruction
