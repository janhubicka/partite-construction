import PartiteConstruction.Functional.AmbientWeakPartialProjection
import PartiteConstruction.Functional.OriginalPartialSemantics

/-!
# Ambient-relative weak homomorphism-embeddings for SET-VALUED functions

An exact weak vertex test C|ᵂS can forget SOME outputs of a
genuinely set-valued function without forgetting the others.
Consequently an EHN part projection is not in general a source-defined
partial homomorphism on the truncated weak fibres, even though it is
one on genuinely function-closed sources.

The correct direct-function-language invariant is RELATIVE to
ambient C: require full equality of function-value images whenever
the original nonempty function value is ENTIRELY within the tested
vertex set S. No equality is required when ANY output of that input
has been forgotten; the weak test must not invent information about
outputs outside S.

This condition:
* makes sense for arbitrary set-valued functions, not only partial
  singleton-valued functions;
* is preserved by EVERY EHN projection to the EXACT weak image p[S],
  without reflecting undefined source inputs or enlarging either set;
* becomes precisely the original-2019 partial homomorphism convention
  on a genuinely function-closed S;
* supports protection of full ambient irreducible substructures,
  analogous to the corrected U-closed tests.

It does NOT assert a strict functional tree witness or the hard
mixed Hales-Jewett attachment step.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V : Type v}

/-- A weak functional map preserves relations and preserves the
ENTIRE ambient set-valued function fibre on input tuples whose
nonempty value set is contained in S. A weak subset with missing
function outputs imposes no completeness requirement on that input.
Undefined source fibres are deliberately not reflected. -/
def IsAmbientRelativeWeakHomomorphism
    (C : Structure L U) (S : Set U)
    (T : Structure L V) (f : S → V) : Prop :=
  (∀ R (x : Fin (L.relArity R) → S),
    (C.weakInduce S).rel R x → T.rel R (f ∘ x)) ∧
  (∀ F (x : Fin (L.funcArity F) → S),
    (C.func F (Subtype.val ∘ x)).Nonempty →
    (∀ y, y ∈ C.func F (Subtype.val ∘ x) → y ∈ S) →
    imageSet f ((C.weakInduce S).func F x) =
      T.func F (f ∘ x))

/-- The ambient-relative weak analogue of a homomorphism-embedding:
in addition to complete fibres on inputs closed within S, protect
every FULL ambient irreducible piece whose image lies in S.
Do not require full embeddings of spurious irreducibles formed by
forgetting outputs in the weak restriction itself. -/
def IsAmbientRelativeWeakHE
    (C : Structure L U) (S : Set U)
    (T : Structure L V) (f : S → V) : Prop :=
  IsAmbientRelativeWeakHomomorphism C S T f ∧
  ∀ {X : Type v} (E : Structure L X), E.Irreducible →
    ∀ (e : Embedding E C) (he : ∀ x, e x ∈ S),
      ∃ g : Embedding E T, ∀ x, g x = f ⟨e x, he x⟩

/-- On a CLOSED vertex set the ambient-relative function condition
is exactly a partial-function homomorphism: all ambient outputs over
inputs in S remain within S, so every defined source fibre is
preserved completely. -/
theorem IsAmbientRelativeWeakHomomorphism.toOriginalPartial_of_closed
    {C : Structure L U} {S : Set U} {T : Structure L V}
    {f : S → V}
    (h : IsAmbientRelativeWeakHomomorphism C S T f)
    (hS : C.IsClosed S) :
    IsOriginalPartialHomomorphism (C.induce S hS) T f := by
  constructor
  · intro R x hx
    exact h.1 R x hx
  · intro F x hNonempty
    have hDefined : (C.func F (Subtype.val ∘ x)).Nonempty := by
      obtain ⟨y, hy⟩ := hNonempty
      exact ⟨y.1, hy⟩
    have hAll : ∀ y, y ∈ C.func F (Subtype.val ∘ x) → y ∈ S :=
      fun y hy => hS F (Subtype.val ∘ x)
        (fun i => (x i).2) hy
    exact h.2 F x hDefined hAll

/-- A closed test upgrades the ambient-relative weak HE to the
standard original-2019 partial homomorphism-embedding, protecting
all its intrinsic full irreducibles. No generated hull is added. -/
theorem IsAmbientRelativeWeakHE.toOriginalPartialHE_of_closed
    {C : Structure L U} {S : Set U} {T : Structure L V}
    {f : S → V}
    (h : IsAmbientRelativeWeakHE C S T f)
    (hS : C.IsClosed S) :
    IsOriginalPartialHomomorphismEmbedding
      (C.induce S hS) T f := by
  refine ⟨h.1.toOriginalPartial_of_closed hS, ?_⟩
  intro X E hE e
  let inc : Embedding (C.induce S hS) C := inclusion C S hS
  let eC : Embedding E C := inc.comp e
  have heC : ∀ x, eC x ∈ S := fun x => (e x).2
  obtain ⟨g, hg⟩ := h.2 E hE eC heC
  refine ⟨g, ?_⟩
  intro x
  calc
    g x = f ⟨eC x, heC x⟩ := hg x
    _ = f (e x) := by
      congr 1

/-- EHN projections have the ambient-relative weak property for
ALL set-valued function languages. For a nonempty ambient fibre
entirely contained in S, its EHN image is the entire target fibre,
and this target fibre lies in p[S]. On a truncated input with
forgotten outputs there is no false equality requirement.

The target is the exact weak vertex image; no closure hull, no
singleton-valuedness, and no domain reflection are assumed. -/
theorem IsEHNHomomorphismEmbedding.ambientRelativeWeakImage
    {C : Structure L U} {D : Structure L V}
    {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (S : Set U) :
    IsAmbientRelativeWeakHE C S (D.weakInduce (p '' S))
      (fun x : S =>
        (⟨p x.1, ⟨x.1, x.2, rfl⟩⟩ : p '' S)) := by
  let pS : S → p '' S :=
    fun x => ⟨p x.1, ⟨x.1, x.2, rfl⟩⟩
  change IsAmbientRelativeWeakHE C S (D.weakInduce (p '' S)) pS
  constructor
  · constructor
    · intro R x hx
      change D.rel R (p ∘ (Subtype.val ∘ x))
      exact hp.1.1 R (Subtype.val ∘ x) hx
    · intro F x hNonempty hAll
      have hFull :
          imageSet p (C.func F (Subtype.val ∘ x)) =
            D.func F (p ∘ (Subtype.val ∘ x)) :=
        hp.toOriginalPartial.1.2 F (Subtype.val ∘ x) hNonempty
      ext z
      constructor
      · rintro ⟨y, hy, hEq⟩
        change z.1 ∈ D.func F (p ∘ (Subtype.val ∘ x))
        have hIn : p y.1 ∈ D.func F (p ∘ (Subtype.val ∘ x)) := by
          rw [← hFull]
          exact ⟨y.1, hy, rfl⟩
        have heq : z.1 = p y.1 :=
          (congrArg Subtype.val hEq).symm
        rw [heq]
        exact hIn
      · intro hz
        have hzD : z.1 ∈ D.func F (p ∘ (Subtype.val ∘ x)) := hz
        rw [← hFull] at hzD
        obtain ⟨y, hy, hEq⟩ := hzD
        have hyS : y ∈ S := hAll y hy
        refine ⟨(⟨y, hyS⟩ : S), hy, ?_⟩
        apply Subtype.ext
        exact hEq
  · intro X E hE e he
    obtain ⟨g, hg⟩ := hp.2 E hE e
    have hRange : ∀ x, g x ∈ p '' S := by
      intro x
      rw [hg x]
      exact ⟨e x, he x, rfl⟩
    exact ⟨g.codRestrictWeak (p '' S) hRange,
      fun x => Subtype.ext (hg x)⟩

/-- The older stronger singleton-valued weak HE also satisfies the
ambient-relative condition. On an ambient-defined fibre wholly
contained in S, the weak source fibre is nonempty and the stronger
original-partial equality applies. -/
theorem IsAmbientWeakOriginalPartialHE.toAmbientRelative
    {C : Structure L U} {S : Set U} {T : Structure L V}
    {f : S → V}
    (h : IsAmbientWeakOriginalPartialHE C S T f) :
    IsAmbientRelativeWeakHE C S T f := by
  refine ⟨⟨h.1.1, ?_⟩, h.2⟩
  intro F x hNonempty hAll
  obtain ⟨y, hy⟩ := hNonempty
  have hyWeak :
      ((C.weakInduce S).func F x).Nonempty :=
    ⟨⟨y, hAll y hy⟩, hy⟩
  exact h.1.2 F x hyWeak

end StructuralRamsey.Structure
