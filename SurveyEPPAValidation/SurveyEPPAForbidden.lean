import SurveyEPPAClassNullaryDirect
import AllThoseEPPA.TreeLikeFaithfulEmbeddingBridge
import AllThoseEPPA.TreeLikeIrreducibleEmbeddingImage

/-!
# Irreducible forbidden structures and coherent EPPA

The survey observes immediately after Theorem `thm:nreppa` that
irreducible-structure faithfulness preserves forbidden irreducible
substructures. This is a *different* statement from the generalized
Herwig–Lascar theorem:

* the forbidden patterns here are **irreducible**;
* forbidden means **no induced/strong embedding**, as in the survey's
  definition of an F-free structure;
* the conclusion is unconditional for finite A with finite
  Γ-relabelling orbit, because we use unrestricted faithful coherent EPPA;
* no ambient structure extending all partial automorphisms is needed.

For an irreducible forbidden source, a homomorphism-embedding is already
a genuine embedding, so the corresponding EPPA-paper Forb(F) convention
also agrees. This does *not* equate arbitrary homomorphisms and embeddings.
-/

namespace SurveyEPPA
namespace IrreducibleForb

open AllThoseEPPA

universe u v w x

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]

/-- The survey's F-free predicate: there is no **embedding** of any
forbidden structure, not merely no ordinary homomorphism. -/
def AvoidsEmbeddings
    (F : HerwigLascar.FiniteForbiddenFamily.{u,v,(max u v)} L)
    (act : L.Action Γ)
    {β : Type (max u v)} (B : Structure L β) : Prop :=
  ∀ i : F.Code,
    ¬ Nonempty (Structure.Embedding act (F.model i) B)

/-- Irreducible-structure faithfulness preserves avoidance of every
irreducible member of a finite forbidden family. The proof uses the
EPPA library's full faithfulness-to-cuts bridge; the image of an exact
embedding is closed and irreducible, and thus embeds back into A. -/
theorem faithful_preserves_irreducible_forbidden_embeddings
    (F : HerwigLascar.FiniteForbiddenFamily.{u,v,(max u v)} L)
    (act : L.Action Γ)
    (hIrreducible : ∀ i : F.Code, (F.model i).IsIrreducible)
    {α β : Type (max u v)}
    (A : Structure L α) (B : Structure L β)
    (ι : Structure.Embedding act A B)
    (hFaith : Structure.IsIrreducibleStructureFaithful act ι)
    (hAvoid : AvoidsEmbeddings F act A) :
    AvoidsEmbeddings F act B := by
  intro i hBad
  obtain ⟨e⟩ := hBad
  let S : Set β := Set.range e.toFun
  have hS : B.IsClosed S := e.range_isClosed act
  have hIrr : (B.induce S hS).IsIrreducible := by
    exact e.range_isIrreducible act (hIrreducible i)
  have hEvery : TreeLike.EveryIrreducibleEmbedsIn act A B :=
    TreeLike.everyIrreducibleEmbedsIn_of_faithful
      act A B ι hFaith
  obtain ⟨j⟩ := hEvery S hS hIrr
  exact hAvoid i ⟨j.comp (e.toClosedRange act)⟩

/-- For an irreducible forbidden source, forbidding a
homomorphism-embedding is equivalent to forbidding an embedding.
This is NOT true for arbitrary forbidden structures. -/
theorem avoidsEmbeddings_iff_avoidsHomomorphismEmbeddings
    (F : HerwigLascar.FiniteForbiddenFamily.{u,v,(max u v)} L)
    (act : L.Action Γ)
    (hIrreducible : ∀ i : F.Code, (F.model i).IsIrreducible)
    {β : Type (max u v)} (B : Structure L β) :
    AvoidsEmbeddings F act B ↔ F.Avoids act B := by
  constructor
  · intro hAvoid i hBad
    obtain ⟨f, hf⟩ := hBad
    let e : Structure.Embedding act (F.model i) B :=
      Structure.Homomorphism.compEmbedding_of_irreducible
        act f hf (Structure.Embedding.id (act := act) (F.model i))
        (hIrreducible i)
    exact hAvoid i ⟨e⟩
  · intro hAvoid i hBad
    obtain ⟨e⟩ := hBad
    exact hAvoid i ⟨e.toHomomorphism,
      Structure.Homomorphism.Embedding.toHomomorphism_isHomomorphismEmbedding
        act e⟩

/-- The corollary stated immediately after `thm:nreppa`: a finite
structure avoiding a family of irreducible patterns has a finite,
coherent, irreducible-structure faithful EPPA witness still avoiding
that family. -/
theorem faithfulCoherentEPPA_preserves_irreducible_forbidden
    (F : HerwigLascar.FiniteForbiddenFamily.{u,v,(max u v)} L)
    (act : L.Action Γ)
    (hIrreducible : ∀ i : F.Code, (F.model i).IsIrreducible)
    {α : Type (max u v)} [Finite α]
    (A : Structure L α)
    (hOrbit : A.HasFiniteRelabelOrbit act)
    (hAvoid : AvoidsEmbeddings F act A) :
    ∃ (β : Type (max u v)) (_ : Finite β)
      (B : Structure L β) (ι : Structure.Embedding act A B),
      AvoidsEmbeddings F act B ∧
      Structure.IsCoherentEPPAWitness act ι ∧
      Structure.IsIrreducibleStructureFaithful act ι := by
  obtain ⟨β, hβ, B, ι, hCoherent, hFaith⟩ :=
    MainTheorems.unrestrictedFaithfulCoherentEPPA act A hOrbit
  exact ⟨β, hβ, B, ι,
    faithful_preserves_irreducible_forbidden_embeddings
      F act hIrreducible A B ι hFaith hAvoid,
    hCoherent, hFaith⟩

/-- Uniform coherent EPPA of an irreducible-forbidden class under
the only necessary relabelling-orbit hypothesis. -/
theorem irreducibleForbiddenClass_hasCoherentEPPA
    (F : HerwigLascar.FiniteForbiddenFamily.{u,v,(max u v)} L)
    (act : L.Action Γ)
    (hIrreducible : ∀ i : F.Code, (F.model i).IsIrreducible)
    (hOrbit :
      ∀ {α : Type (max u v)} [Finite α] (A : Structure L α),
        AvoidsEmbeddings F act A → A.HasFiniteRelabelOrbit act) :
    TreeLike.FiniteClassHasCoherentEPPA act
      (fun {α : Type (max u v)} (A : Structure L α) =>
        AvoidsEmbeddings F act A) := by
  intro α hα A hAvoid
  obtain ⟨β, hβ, B, ι, hAvoidB, hCoherent, _⟩ :=
    faithfulCoherentEPPA_preserves_irreducible_forbidden
      F act hIrreducible A (hOrbit A hAvoid) hAvoid
  exact ⟨β, hβ, B, ι, hAvoidB, hCoherent⟩

/-- In particular every class forbidding finitely many irreducible
substructures has coherent EPPA for ordinary fixed languages. The
finite trivial-action group includes the one-element group used to
model the survey's unchanged relation and function symbols. -/
theorem irreducibleForbiddenClass_hasCoherentEPPA_trivialAction
    [Finite Γ]
    (F : HerwigLascar.FiniteForbiddenFamily.{u,v,(max u v)} L)
    (hIrreducible : ∀ i : F.Code, (F.model i).IsIrreducible) :
    TreeLike.FiniteClassHasCoherentEPPA
      (Language.Action.trivial L Γ)
      (fun {α : Type (max u v)} (A : Structure L α) =>
        AvoidsEmbeddings F (Language.Action.trivial L Γ) A) := by
  apply irreducibleForbiddenClass_hasCoherentEPPA
    F (Language.Action.trivial L Γ) hIrreducible
  intro α hα A hAvoid
  unfold Structure.HasFiniteRelabelOrbit
  exact Set.finite_range _

end IrreducibleForb
end SurveyEPPA
