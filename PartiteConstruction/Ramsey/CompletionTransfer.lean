import PartiteConstruction.Iterated.SparseningStrictBaseIrreducible
import PartiteConstruction.Relational.FreeAmalgamationClass

/-! # Ramsey transfer through completion on copies

This is the final, genuinely general colouring step of Theorem 2.18 of
Hubička--Nešetřil, *All those Ramsey classes* (2019).

A completion relative to copies of B need not be a homomorphism, nor
injective globally. It only needs to restrict to a genuine embedding on
**each** B-copy. This is exactly the published Definition 2.16.

For a sparsening witness in which every irreducible substructure is
contained in a B-copy, every A-copy is also preserved whenever A is
irreducible. Consequently the Ramsey arrow transfers to the completion.

The multiamalgamation theorem requires a further construction: the local
completion property and strong amalgamation must produce such a
copywise completion. It is not proved by this last transfer lemma alone.
No free-amalgamation axiom for the final class is assumed here.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W X P : Type v}

/-- A vertex map from C to D that restricts to an induced embedding on
every copy of Q. No homomorphism, injectivity, or relation reflection is
assumed outside those copies. -/
def CopywiseCompletion
    (Q : RelStructure L U) (C : RelStructure L W)
    (D : RelStructure L X) (f : W → X) : Prop :=
  ∀ e : Embedding Q C,
    ∃ g : Embedding Q D, ∀ q, g q = f (e q)

/-- Every copy of an irreducible A in a sparse witness is covered by
some B-copy. Hence a map that preserves B-copies preserves A-copies. -/
theorem CopywiseCompletion.of_irreducible_extension
    {A : RelStructure L U} {B : RelStructure L V}
    {C : RelStructure L W} {D : RelStructure L X}
    {f : W → X}
    (hA : A.Irreducible)
    (hExt : IrreduciblesExtendTo B C)
    (hB : CopywiseCompletion B C D f) :
    CopywiseCompletion A C D f := by
  classical
  intro e
  have hS : (C.induce (Set.range e)).Irreducible :=
    hA.range_embedding e
  obtain ⟨β, hβ⟩ := hExt (Set.range e) hS
  have hRange : ∀ a : U, ∃ b : V, e a = β b := by
    intro a
    exact hβ ⟨e a, ⟨a, rfl⟩⟩
  let eAB : Embedding A B := e.factorThroughRange β hRange
  obtain ⟨β', hβ'⟩ := hB β
  refine ⟨β'.comp eAB, ?_⟩
  intro a
  calc
    (β'.comp eAB) a = β' (eAB a) := rfl
    _ = f (β (eAB a)) := hβ' (eAB a)
    _ = f (e a) := by
      apply congrArg f
      exact (Classical.choose_spec (hRange a)).symm

/-- Copywise completions preserve finite Ramsey arrows provided they
respect both the A-copies coloured and the B-copies sought. -/
theorem arrow_of_copywiseCompletion
    {A : RelStructure L U} {B : RelStructure L V}
    {C : RelStructure L W} {D : RelStructure L X}
    {f : W → X} {κ : Type*}
    (hRamsey : StructuralRamsey.Arrow A B C κ)
    (hA : CopywiseCompletion A C D f)
    (hB : CopywiseCompletion B C D f) :
    StructuralRamsey.Arrow A B D κ := by
  classical
  let mapA (a : Embedding A C) : Embedding A D :=
    Classical.choose (hA a)
  have mapA_spec (a : Embedding A C) (x : U) :
      mapA a x = f (a x) :=
    Classical.choose_spec (hA a) x
  intro χ
  obtain ⟨b, hMono⟩ := hRamsey (fun a => χ (mapA a))
  obtain ⟨b', hb'⟩ := hB b
  have hcompose (e : Embedding A B) :
      mapA (b.comp e) = b'.comp e := by
    apply Embedding.ext
    intro a
    calc
      mapA (b.comp e) a = f ((b.comp e) a) :=
        mapA_spec (b.comp e) a
      _ = f (b (e a)) := rfl
      _ = b' (e a) := (hb' (e a)).symm
      _ = (b'.comp e) a := rfl
  refine ⟨b', ?_⟩
  intro e₁ e₂
  calc
    χ (b'.comp e₁) = χ (mapA (b.comp e₁)) := by
      rw [hcompose]
    _ = χ (mapA (b.comp e₂)) := hMono e₁ e₂
    _ = χ (b'.comp e₂) := by
      rw [hcompose]

/-- The precise copy-completion conclusion needed in the last step of
Theorem 2.18: a member of K together with a single vertex map
respecting every B-copy. The maps need not be global embeddings. -/
def HasCopywiseCompletion
    (K : RelStructure.StructureClass.{u,v} (L := L))
    (B : RelStructure L V) (C : RelStructure L W) : Prop :=
  ∃ (X : Type v) (_ : Finite X) (D : RelStructure L X),
    K D ∧ ∃ f : W → X, CopywiseCompletion B C D f

/-- The final step in the multiamalgamation proof needs no amalgamation
assumptions: if a sparse Ramsey witness has its irreducibles covered by
B-copies and admits a K-completion on those copies, the completion is
already a Ramsey witness in K. -/
theorem arrow_of_copywiseCompletion_inClass
    {K : RelStructure.StructureClass.{u,v} (L := L)}
    {A : RelStructure L U} {B : RelStructure L V}
    {C : RelStructure L W} {κ : Type*}
    (hA : A.Irreducible)
    (hRamsey : StructuralRamsey.Arrow A B C κ)
    (hExt : IrreduciblesExtendTo B C)
    (hCompletion : HasCopywiseCompletion K B C) :
    ∃ (X : Type v) (_ : Finite X) (D : RelStructure L X),
      K D ∧ StructuralRamsey.Arrow A B D κ := by
  obtain ⟨X,hX,D,hKD,f,hB⟩ := hCompletion
  have hCopiesA : CopywiseCompletion A C D f :=
    hB.of_irreducible_extension hA hExt
  exact ⟨X,hX,D,hKD,arrow_of_copywiseCompletion hRamsey hCopiesA hB⟩

/-- Relational sparsening + copywise local completion criterion. The
unproved hypothesis in the full multiamalgamation theorem is not a Ramsey
arrow: it is construction of a K-completion on B-copies from Definition
2.17's strong amalgamation and bounded U-completions.

This criterion requires less than K being freely amalgamating, but is
strictly stronger than assuming the published local-completion axiom
without yet proving that it applies to this sparse witness. -/
theorem ramsey_of_sparse_copywise_completion
    (K : RelStructure.StructureClass.{u,v} (L := L))
    (A : RelStructure L U) (B : RelStructure L V)
    (D : RelStructure L P)
    [Finite U] [Finite V] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B D κ)
    (hA : A.Irreducible) (hB : B.Irreducible)
    (n : ℕ)
    (hComplete :
      ∀ {W : Type v} [Finite W] (C : RelStructure L W),
        (∃ p : W → P, C.IsHomomorphismEmbedding D p) →
        LocallyTreeCompletable B C n →
        IrreduciblesExtendTo B C →
        HasCopywiseCompletion K B C) :
    ∃ (X : Type v) (_ : Finite X) (C : RelStructure L X),
      K C ∧ StructuralRamsey.Arrow A B C κ := by
  obtain ⟨W,hW,C,hArrowC,p,hp,hLocal,hExt⟩ :=
    StructuralRamsey.Partite.IteratedSparsening.sparseningRamsey_strict_baseIrreducible_all
      A B D κ hRamsey hB n
  letI : Finite W := hW
  have hCopy : HasCopywiseCompletion K B C :=
    hComplete C ⟨p,hp⟩ hLocal hExt
  exact arrow_of_copywiseCompletion_inClass hA hArrowC hExt hCopy

end StructuralRamsey.RelStructure
