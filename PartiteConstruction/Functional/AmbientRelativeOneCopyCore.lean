import PartiteConstruction.Functional.AmbientRelativeWeakPullback

/-!
# One-copy completion of weak tests in native functional Hales-Jewett cores

The native EHN Hales-Jewett power core has a weak/part projection
to the selected FULL functional A. If there is a full embedding
A ↪ B, this projection followed by the embedding of A into B
provides an ambient-relative weak functional map on EVERY exact
weak vertex set, with target the ONE-COPY strict B-tree.

The mechanism is completely functional and works with arbitrary
set-valued output fibres:
1. any full embedding induces an ambient-relative weak HE on
   EVERY weak restriction of its domain, without closure;
2. the verified relative-weak EHN pullback composes such a map with
   any EHN source projection;
3. the target remains a genuine full functional B-copy, not a
   relational graph tree or a semi-closed auxiliary structure.

This settles the pure Hales-Jewett core target side for weak tests.
It does not settle tests mixing the core and attached old pictures:
the strict common-root compatibility remains separate.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V W : Type v}

/-- A full embedding of function structures remains an ambient-relative
weak HE on EVERY exact vertex subset of its source, even if the weak
substructure has forgotten some outputs. The FULL fibre equality is
required only for inputs whose entire original fibre is retained. -/
theorem Embedding.ambientRelativeWeakRestriction
    {A : Structure L U} {T : Structure L V}
    (e : Embedding A T) (S : Set U) :
    IsAmbientRelativeWeakHE A S T
      (fun x : S => e x.1) := by
  let f : S → V := fun x => e x.1
  change IsAmbientRelativeWeakHE A S T f
  constructor
  · constructor
    · constructor
      · intro R x hx
        change T.rel R (e ∘ (Subtype.val ∘ x))
        exact (e.map_rel_iff R (Subtype.val ∘ x)).mpr hx
      · intro F x y hy
        change e y.1 ∈ T.func F (e ∘ (Subtype.val ∘ x))
        rw [← e.map_func F (Subtype.val ∘ x)]
        exact ⟨y.1, hy, rfl⟩
    · intro F x _hNonempty hAll
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        change e y.1 ∈ T.func F (e ∘ (Subtype.val ∘ x))
        rw [← e.map_func F (Subtype.val ∘ x)]
        exact ⟨y.1, hy, rfl⟩
      · intro hz
        have hzT : z ∈ T.func F (e ∘ (Subtype.val ∘ x)) := hz
        rw [← e.map_func F (Subtype.val ∘ x)] at hzT
        obtain ⟨a, ha, hea⟩ := hzT
        exact ⟨(⟨a, hAll a ha⟩ : S), ha, hea⟩
  · intro X E _hE j _hj
    exact ⟨e.comp j, fun _ => rfl⟩

/-- General native FUNCTIONAL one-copy reduction: an EHN projection
C → A followed by a full embedding A ↪ B gives an
ambient-relative weak HE from EVERY C|ᵂS into the genuine B.

There is NO singleton hypothesis and no generated closure hull.
The target B itself has a one-copy strict B-tree certificate. -/
theorem IsEHNHomomorphismEmbedding.ambientRelativeWeak_to_embedding
    {C : Structure L U} {A : Structure L V}
    {B : Structure L W} {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding A p)
    (eAB : Embedding A B)
    (S : Set U) :
    IsAmbientRelativeWeakHE C S B
      (fun x : S => eAB (p x.1)) := by
  let g : p '' S → W := fun x => eAB x.1
  have hB : IsAmbientRelativeWeakHE A (p '' S) B g :=
    eAB.ambientRelativeWeakRestriction (p '' S)
  have hComp := hB.pullback_ehn_exact hp S g
  have hEq :
      (g ∘ (fun x : S =>
        (⟨p x.1, ⟨x.1, x.2, rfl⟩⟩ : p '' S))) =
      (fun x : S => eAB (p x.1)) := by
    funext x
    rfl
  rw [hEq] at hComp
  exact hComp

/-- Explicit one-copy strict functional tree target for every weak
test of a native source admitting EHN projection to A ↪ Base.
This does not assert the maximal mixed attachment invariant. -/
theorem IsEHNHomomorphismEmbedding.ambientRelativeWeak_oneCopyTree
    {C : Structure L U} {A : Structure L V}
    {Base : Structure L W} {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding A p)
    (eAB : Embedding A Base)
    (S : Set U) :
    ∃ f : S → W,
      IsAmbientRelativeWeakHE C S Base f ∧
      TreeAmalgam Base W Base := by
  let f : S → W := fun x => eAB (p x.1)
  refine ⟨f, ?_, ?_⟩
  · exact hp.ambientRelativeWeak_to_embedding eAB S
  · exact TreeAmalgam.copy (Embedding.id Base) (fun x => ⟨x, rfl⟩)

end StructuralRamsey.Structure
