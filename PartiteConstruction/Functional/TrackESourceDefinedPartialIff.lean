import PartiteConstruction.Functional.TrackBRealEHNExactImageUSize2019
import PartiteConstruction.Functional.TrackENativePartialFullFaithfulness

/-!
# Appendix A Track E: exact same-map source-defined homomorphism correspondence

The existing native `Structure.IsOriginalPartialHomomorphism.toNonemptyPartial`
proves one direction. Here we prove the converse for precisely the two
canonical `Option (Set)` encodings `A.toNonemptyPartial` and
`B.toNonemptyPartial`, on the IDENTICAL vertex map.

This does not replace the source-defined notion by a full/domain-reflecting
homomorphism. Defined source tuples are preserved with equality of COMPLETE
output fibres; undefined source tuples may map to defined target tuples.

The witness below shows this distinction even for a unary language with
one-element source and target. In particular, the corrected 2019 EHN
projection may be faithfully transported into `Option (Set)` without
acquiring the false global total-fibre equation.
-/

namespace StructuralRamsey.Structure.TrackESourceDefinedPartialIff

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- A source-defined genuine-partial homomorphism between the canonical
native images descends to the original 2019 source-defined functional
homomorphism on the EXACT SAME map. No domain reflection is used. -/
theorem originalPartialHom_of_nonemptyPartial
    {A : Structure L V} {B : Structure L W} {f : V → W}
    (h : PartialSetStructure.IsOriginalPartialHomomorphism
      A.toNonemptyPartial B.toNonemptyPartial f) :
    IsOriginalPartialHomomorphism A B f := by
  classical
  refine ⟨h.1, ?_⟩
  intro F xs hDefined
  have hSource :
      A.toNonemptyPartial.func F xs = some (A.func F xs) := by
    change (if (A.func F xs).Nonempty then
      some (A.func F xs) else none) = some (A.func F xs)
    simp [hDefined]
  have hTarget := h.2 F xs (A.func F xs) hSource
  change (if (B.func F (f ∘ xs)).Nonempty then
      some (B.func F (f ∘ xs)) else none) =
      some (imageSet f (A.func F xs)) at hTarget
  by_cases hB : (B.func F (f ∘ xs)).Nonempty
  · have hEq : B.func F (f ∘ xs) =
        imageSet f (A.func F xs) := by
      simpa [hB] using hTarget
    exact hEq.symm
  · have hImpossible : False := by
      simpa [hB] using hTarget
    exact hImpossible.elim

/-- Exact equivalence for genuine 2019 source-defined maps. The relation
and source-defined whole-fibre clauses coincide on a fixed A, B, f;
neither direction changes the vertex map, function arities, carrier,
or the meaning of an undefined source tuple. -/
theorem originalPartialHom_iff_nonemptyPartial
    {A : Structure L V} {B : Structure L W} {f : V → W} :
    IsOriginalPartialHomomorphism A B f ↔
      PartialSetStructure.IsOriginalPartialHomomorphism
        A.toNonemptyPartial B.toNonemptyPartial f := by
  constructor
  · exact IsOriginalPartialHomomorphism.toNonemptyPartial
  · exact originalPartialHom_of_nonemptyPartial

/-- Faithful source-defined 2019 homomorphism-embedding predicate in
genuine Option(Set) syntax, testing exactly all irreducible *native*
substructures under their canonical encoding. The native test E is
unchanged; no claim is made about irreducibility of arbitrary rich
partial structures having independent defined-empty operations. -/
def CanonicalEncodedOriginalPartialHE
    (A : Structure L V) (B : Structure L W) (f : V → W) : Prop :=
  PartialSetStructure.IsOriginalPartialHomomorphism
    A.toNonemptyPartial B.toNonemptyPartial f ∧
    ∀ {X : Type v} (E : Structure L X), E.Irreducible →
      ∀ e : PartialSetStructure.Embedding
        E.toNonemptyPartial A.toNonemptyPartial,
        ∃ g : PartialSetStructure.Embedding
          E.toNonemptyPartial B.toNonemptyPartial,
          ∀ x, g.toFun x = f (e.toFun x)

/-- Exact homomorphism-EMBEDDING correspondence, extending the prior
same-map homomorphism iff using the checked full-embedding equivalence.
Every quantifier still uses the identical native irreducible E and
original vertex map f. -/
theorem originalPartialHE_iff_canonicalEncodedHE
    {A : Structure L V} {B : Structure L W} {f : V → W} :
    IsOriginalPartialHomomorphismEmbedding A B f ↔
      CanonicalEncodedOriginalPartialHE A B f := by
  constructor
  · intro h
    refine ⟨originalPartialHom_iff_nonemptyPartial.mp h.1, ?_⟩
    intro X E hIrred e
    obtain ⟨g, hg⟩ :=
      h.2 E hIrred
        (TrackENativePartialFullFaithfulness.partialFullEmbedding_toNative e)
    exact ⟨g.toNonemptyPartial, fun x => hg x⟩
  · intro h
    refine ⟨originalPartialHom_iff_nonemptyPartial.mpr h.1, ?_⟩
    intro X E hIrred e
    obtain ⟨g, hg⟩ := h.2 E hIrred e.toNonemptyPartial
    exact ⟨TrackENativePartialFullFaithfulness.partialFullEmbedding_toNative g,
      fun x => hg x⟩

/-- Native EHN projections are EXACTLY these source-defined genuine
partial homomorphism-embeddings on canonically encoded irreducible
tests, by the previously verified 2019 EHN/original equivalence.
No total-fibre domain reflection is added. -/
theorem EHN_iff_canonicalEncodedOriginalPartialHE
    {A : Structure L V} {B : Structure L W} {f : V → W} :
    A.IsEHNHomomorphismEmbedding B f ↔
      CanonicalEncodedOriginalPartialHE A B f := by
  exact (originalPartialHE_iff_EHN).symm.trans
    originalPartialHE_iff_canonicalEncodedHE

/-- A one-point unary native function structure with ALL inputs undefined. -/
def nowhereDefined : Structure PartialSetStructure.exampleLanguage Unit where
  rel := fun R => Empty.elim R
  func := fun _ _ => ∅

/-- A one-point unary native function structure with ALL inputs defined. -/
def everywhereDefined : Structure PartialSetStructure.exampleLanguage Unit where
  rel := fun R => Empty.elim R
  func := fun _ _ => Set.univ

/-- A nonvacuous source-defined original partial map which is *not* a
survey full-fibre homomorphism, although it remains a genuine
source-defined homomorphism after faithful Option(Set) encoding.
The empty source domain imposes no false demand to reflect definedness. -/
theorem sourceDefined_and_nonreflecting_example :
    IsOriginalPartialHomomorphism nowhereDefined everywhereDefined id ∧
    PartialSetStructure.IsOriginalPartialHomomorphism
      nowhereDefined.toNonemptyPartial
      everywhereDefined.toNonemptyPartial id ∧
    ¬ nowhereDefined.IsHomomorphism everywhereDefined id := by
  have hPartial : IsOriginalPartialHomomorphism
      nowhereDefined everywhereDefined id := by
    constructor
    · intro R xs hx
      exact Empty.elim R
    · intro F xs hDefined
      change (∅ : Set Unit).Nonempty at hDefined
      rcases hDefined with ⟨x, hx⟩
      exact hx.elim
  refine ⟨hPartial, hPartial.toNonemptyPartial, ?_⟩
  intro hFull
  have hEq := hFull.2 () (fun _ : Fin 1 => ())
  have hUnit : () ∈ everywhereDefined.func () (fun _ : Fin 1 => ()) := by
    change () ∈ (Set.univ : Set Unit)
    trivial
  rw [← hEq] at hUnit
  rcases hUnit with ⟨x, hx, _⟩
  exact hx

end StructuralRamsey.Structure.TrackESourceDefinedPartialIff
