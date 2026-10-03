import PartiteConstruction.Iterated.ControlCompletion

/-! # Completing control from explicit boundary embeddings

For a reducible intersection H = A|{a : α a in S}, a homomorphism-embedding
of the tested structure need not be induced on H.  The hereditary version of
control completion obtains the needed boundary embedding from irreducibility
of H.

This file isolates the exact replacement datum: for every ambient A-copy,
supply an embedding of its tested boundary into the current target, agreeing
with the witness map, whose image is contained in an irreducible target
substructure.  Then a fresh B-copy can be attached over that boundary without
any hereditary irreducibility assumption on A.

This is the relative/boundary interface needed for a general irreducible-A
mixed-step proof.
-/
namespace StructuralRamsey.RelStructure.LocallyTreeLike

universe u v
variable {L : RelLanguage.{u}}
variable {U V W Y : Type v}
variable {A : RelStructure L U} {B : RelStructure L V}
variable {C : RelStructure L W} {T : RelStructure L Y}

/-- Explicit induced boundary data for one ambient A-copy. -/
structure BoundaryEmbedding
    (S : Finset W) (f : ↥(↑S : Set W) → Y)
    (α : Embedding A C) where
  boundary : Embedding (A.induce {a : U | α a ∈ S}) T
  agrees : ∀ x, boundary x = f ⟨α x.1, x.2⟩
  contained : boundary.ContainedInIrreducible

/-- Add one controlled A-copy when an induced boundary embedding is supplied
explicitly.  No hereditary irreducibility assumption on A is used. -/
theorem addControl_of_boundary
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    (S : Finset W)
    (hTree : TreeAmalgam B Y T)
    (f : ↥(↑S : Set W) → Y)
    (hf : (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f)
    (xs : List (Embedding A C))
    (hctrl : Controls (A := A) (C := C) (T := T) S f xs)
    (α : Embedding A C)
    (hbd : BoundaryEmbedding (A := A) (C := C) (T := T) S f α) :
    ∃ (Z : Type v) (T' : RelStructure L Z),
      TreeAmalgam B Z T' ∧
      ∃ f' : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding T' f' ∧
        Controls (A := A) (C := C) (T := T') S f' (α :: xs) := by
  classical
  let Hset : Set U := {a | α a ∈ S}
  let H := A.induce Hset
  let eHT : Embedding H T := hbd.boundary
  let eHB : Embedding H B :=
    eAB.comp (RelStructure.inclusion A Hset)
  have hcT : eHT.ContainedInIrreducible := hbd.contained
  have hcB : eHB.ContainedInIrreducible := by
    apply Embedding.containedInIrreducible_of_range_subset
      hA eAB eHB
    intro x
    exact ⟨x.1, rfl⟩
  let T' := FreeAmalgam.amalgam H T B eHT eHB
  let l : Embedding T T' :=
    FreeAmalgam.leftEmbedding H T B eHT eHB
  let r : Embedding B T' :=
    FreeAmalgam.rightEmbedding H T B eHT eHB
  have hTree' : TreeAmalgam B _ T' :=
    FreeAmalgam.treeAmalgam H T B eHT eHB B
      hTree (TreeAmalgam.copy (Iso.refl B)) hcT hcB
  let f' : ↥(↑S : Set W) → _ := l ∘ f
  have hf' :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding T' f' :=
    l.isHomomorphismEmbedding.comp hf
  refine ⟨_, T', hTree', f', hf', ?_⟩
  intro β hβ
  rcases List.mem_cons.mp hβ with hβα | hβ
  · subst β
    let α' : Embedding A T' := r.comp eAB
    refine ⟨α', ?_⟩
    intro a ha
    refine ⟨a, ?_⟩
    let ah : Hset := ⟨a, ha⟩
    change l (f ⟨α a, ha⟩) = r (eAB a)
    calc
      l (f ⟨α a, ha⟩) = l (eHT ah) :=
        congrArg l (hbd.agrees ah).symm
      _ = r (eHB ah) :=
        FreeAmalgam.left_right_overlap H T B eHT eHB ah
      _ = r (eAB a) := rfl
  · obtain ⟨β', hβ'⟩ := hctrl β hβ
    let β'' : Embedding A T' := l.comp β'
    refine ⟨β'', ?_⟩
    intro a ha
    obtain ⟨a', ha'⟩ := hβ' a ha
    exact ⟨a', congrArg l ha'⟩

end StructuralRamsey.RelStructure.LocallyTreeLike
