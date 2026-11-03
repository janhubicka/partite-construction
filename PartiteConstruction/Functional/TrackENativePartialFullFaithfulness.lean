import PartiteConstruction.Functional.NativePartialClosure
import PartiteConstruction.Structure.PartialSetFunctionsMaps

/-!
# Appendix A Track E: full native / partial embedding equivalence

Do not introduce a second conversion: the existing
`Structure.toNonemptyPartial` and `Structure.Embedding.toNonemptyPartial`
already give the forward direction. We prove their converse on the SAME
vertex maps. This translation is fully faithful exactly on the full
subcategory whose DEFINED partial function values are nonempty.

In particular, the richer genuine partial syntax may have
`some ∅` distinct from `none`; such objects cannot be native ones.
This matters for correcting the 2019 endpoint without silently assuming
domain reflection for a globally source-defined EHN projection.

All tests use the exact original carrier, including nullary symbols,
multivalued outputs, and repeated input vertices.
-/

namespace StructuralRamsey.Structure.TrackENativePartialFullFaithfulness

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- Dropping an independent domain bit after applying an Option map
commutes with taking the set-theoretic image. This is a generic
pointwise fact, no assumption of injectivity or positive arity. -/
theorem option_getD_image
    (f : V → W) (m : Option (Set V)) :
    (m.map (Structure.imageSet f)).getD ∅ =
      Structure.imageSet f (m.getD ∅) := by
  cases m with
  | none =>
      change (∅ : Set W) = Structure.imageSet f ∅
      simp [Structure.imageSet]
  | some T => rfl

/-- FULL partial embeddings between faithful native images descend to
FULL native functional embeddings, retaining the IDENTICAL vertex map.
There is no weakening to positive homomorphisms or changing the image. -/
noncomputable def partialFullEmbedding_toNative
    {A : Structure L V} {B : Structure L W}
    (e : PartialSetStructure.Embedding
      A.toNonemptyPartial B.toNonemptyPartial) :
    Structure.Embedding A B where
  toFun := e.toFun
  injective := e.injective
  map_rel_iff := e.map_rel_iff
  map_func := by
    intro F xs
    have h := congrArg
      (fun t : Option (Set W) => t.getD ∅)
      (e.map_func F xs)
    have h' :
        Structure.imageSet e.toFun
          ((A.toNonemptyPartial.func F xs).getD ∅) =
        (B.toNonemptyPartial.func F (e.toFun ∘ xs)).getD ∅ := by
      simpa only [option_getD_image] using h
    change Structure.imageSet e.toFun
        ((A.toNonemptyPartial.collapseDomain).func F xs) =
      (B.toNonemptyPartial.collapseDomain).func F (e.toFun ∘ xs) at h'
    simpa only [Structure.toNonemptyPartial_collapseDomain] using h'

/-- Full faithfulness, not merely preservation: the EXACT sets of full
embeddings coincide under the native-to-Option translation, without
changing any underlying function on vertices. -/
noncomputable def nativePartialFullEmbeddingEquiv
    (A : Structure L V) (B : Structure L W) :
    Structure.Embedding A B ≃
      PartialSetStructure.Embedding
        A.toNonemptyPartial B.toNonemptyPartial where
  toFun := Structure.Embedding.toNonemptyPartial
  invFun := partialFullEmbedding_toNative
  left_inv := by
    intro e
    apply Structure.Embedding.ext
    intro x
    rfl
  right_inv := by
    intro e
    apply PartialSetStructure.Embedding.ext
    intro x
    rfl

/-- The necessary and sufficient OBJECT-level condition for a genuine
partial structure to be in the image of the native encoding: it does
not contain defined-empty values. Merely having no output incidence
does NOT imply undefinedness outside this full subcategory. -/
def NoDefinedEmptyValues (P : PartialSetStructure L V) : Prop :=
  ∀ F xs S, P.func F xs = some S → S.Nonempty

/-- The existing native encoding always avoids independent
defined-empty function values, even for nullary operations. -/
theorem toNonemptyPartial_noDefinedEmpty (A : Structure L V) :
    NoDefinedEmptyValues A.toNonemptyPartial := by
  classical
  intro F xs S h
  by_cases hA : (A.func F xs).Nonempty
  · have hs : A.func F xs = S := by
      simpa [Structure.toNonemptyPartial, hA] using h
    simpa [← hs] using hA
  · have hf : False := by
      simpa [Structure.toNonemptyPartial, hA] using h
    exact hf.elim

/-- Characterize the EXACT essential-image objects on their current
carrier. No arbitrary partial object with `some ∅` is identified
with the same native graph after domain collapse. -/
theorem noDefinedEmpty_iff_nativeRoundtrip
    (P : PartialSetStructure L V) :
    NoDefinedEmptyValues P ↔
      (P.collapseDomain).toNonemptyPartial = P := by
  classical
  constructor
  · intro h
    cases P with
    | mk rel fn =>
      change PartialSetStructure.mk rel _ = PartialSetStructure.mk rel fn
      congr 1
      funext F xs
      cases hv : fn F xs with
      | none =>
          simp [Structure.toNonemptyPartial,
            PartialSetStructure.collapseDomain, hv]
      | some S =>
          have hS : S.Nonempty := h F xs S hv
          simp [Structure.toNonemptyPartial,
            PartialSetStructure.collapseDomain, hv, hS]
  · intro heq F xs S hFx
    have hval := congrArg
      (fun Q : PartialSetStructure L V => Q.func F xs) heq
    have hc : P.collapseDomain.func F xs = S := by
      change (P.func F xs).getD ∅ = S
      simp [hFx]
    have hval' :
        (if h : S.Nonempty then some S else none) = some S := by
      simpa [Structure.toNonemptyPartial, hc, hFx] using hval
    by_contra hEmpty
    simp [hEmpty] at hval'

/-- Strictly distinguish the rich independent-domain syntax from its
faithful native image: defined-empty inputs are genuinely additional
structures, not an alternative spelling for undefined inputs. -/
theorem definedEmptyExample_not_nativeImage :
    ¬ ∃ (A : Structure PartialSetStructure.exampleLanguage Unit),
      A.toNonemptyPartial = PartialSetStructure.definedEmptyExample := by
  rintro ⟨A, hA⟩
  have hNo : NoDefinedEmptyValues PartialSetStructure.definedEmptyExample := by
    rw [← hA]
    exact toNonemptyPartial_noDefinedEmpty A
  exact (hNo () (fun _ : Fin 1 => ()) ∅ rfl).ne_empty rfl

end StructuralRamsey.Structure.TrackENativePartialFullFaithfulness
