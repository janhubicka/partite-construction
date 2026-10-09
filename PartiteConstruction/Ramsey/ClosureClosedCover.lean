import PartiteConstruction.Ramsey.ClosureClosedMapGlue

/-! # Closed covers and reflection through a positive factor

These two elementary tools are used on the actual simultaneous Picture
attachment. The cover theorem works on the test's own carrier: it does
not require a transport theorem for irreducibility of its image.

The factor theorem recovers a protected map from a protected composite
and positivity of both factors. Neither factor is required to be globally
injective, and no relation-reflection hypothesis is imposed on the second.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {U V W : Type v}

/-- A closed U-irreducible structure cannot be freely covered by two
proper relative U-substructures. The tuple condition is the exact free
cover condition, including zero-arity relation tuples. -/
theorem IsUIrreducible.closed_cover
    {rules : ClosureDescription L} {A : RelStructure L U}
    (hIrred : IsUIrreducible rules A) (hA : IsUClosed rules A)
    (S T : Set U)
    (hS : IsUSubstructure rules A S) (hT : IsUSubstructure rules A T)
    (hCover : ∀ x, x ∈ S ∨ x ∈ T)
    (hTuples : ∀ R (z : Fin (L.arity R) → U), A.rel R z →
      (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T)) :
    (∀ x, x ∈ S) ∨ (∀ x, x ∈ T) := by
  let mL : Embedding (A.induce (S ∩ T)) (A.induce S) := {
    toFun := fun x => ⟨x.1, x.2.1⟩
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : S => z.1) h
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let mR : Embedding (A.induce (S ∩ T)) (A.induce T) := {
    toFun := fun x => ⟨x.1, x.2.2⟩
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : T => z.1) h
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let l : Embedding (A.induce S) A := inclusion A S
  let r : Embedding (A.induce T) A := inclusion A T
  have hFree : IsFreeAmalgam mL mR l r := by
    constructor
    · intro x
      rcases hCover x with hx | hx
      · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
      · exact Or.inr ⟨⟨x, hx⟩, rfl⟩
    · intro a b
      constructor
      · intro hab
        have he : a.1 = b.1 := hab
        have haT : a.1 ∈ T := by rw [he]; exact b.2
        exact ⟨⟨a.1, a.2, haT⟩, Subtype.ext rfl, Subtype.ext he.symm⟩
      · rintro ⟨d, rfl, rfl⟩
        rfl
    · intro R z
      constructor
      · intro hz
        rcases hTuples R z hz with hL | hR
        · exact Or.inl ⟨fun k => ⟨z k, hL k⟩, hz, rfl⟩
        · exact Or.inr ⟨fun k => ⟨z k, hR k⟩, hz, rfl⟩
      · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
        · exact hz
        · exact hz
  rcases hIrred (hA.induce_of_USubstructure S hS)
      (hA.induce_of_USubstructure T hT) hFree with hL | hR
  · left
    intro x
    obtain ⟨y, hy⟩ := hL x
    change y.1 = x at hy
    rw [← hy]
    exact y.2
  · right
    intro x
    obtain ⟨y, hy⟩ := hR x
    change y.1 = x at hy
    rw [← hy]
    exact y.2

/-- If q composed with p protects the tests, and both factors are
positive, then p already protects the same tests. This is useful for
coordinate evaluation maps that commute with a known part projection. -/
theorem IsClosedUHomomorphismEmbedding.of_comp_homomorphisms
    {rules : ClosureDescription L}
    {A : RelStructure L U} {B : RelStructure L V} {C : RelStructure L W}
    {p : U → V} {q : V → W}
    (hp : A.IsHomomorphism B p) (hq : B.IsHomomorphism C q)
    (hComp : IsClosedUHomomorphismEmbedding rules A C (q ∘ p)) :
    IsClosedUHomomorphismEmbedding rules A B p := by
  constructor
  · exact hp
  · intro X Test hClosed hIrred e
    obtain ⟨g, hg⟩ := hComp.on_test Test hClosed hIrred e
    let d : Embedding Test B := {
      toFun := fun x => p (e x)
      injective := by
        intro x y h
        apply g.injective
        exact (hg x).trans ((congrArg q h).trans (hg y).symm)
      map_rel_iff := by
        intro R z
        constructor
        · intro hz
          have hC : C.rel R (q ∘ (fun k => p (e (z k)))) :=
            hq R _ hz
          have hEq : g ∘ z = q ∘ (fun k => p (e (z k))) := by
            funext k
            exact hg (z k)
          apply (g.map_rel_iff R z).mp
          rw [hEq]
          exact hC
        · intro hz
          exact hp R (e ∘ z) ((e.map_rel_iff R z).mpr hz)
    }
    exact ⟨d, fun _ => rfl⟩

end StructuralRamsey.RelStructure
