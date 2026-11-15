import PartiteConstruction.Functional.TrackCRichOptionEHN
import PartiteConstruction.Functional.TrackCDomainEmptyLegalLooseTree
import PartiteConstruction.Functional.PublishedSparseningLoose

/-!
# Appendix A Track C: legal rich partial loose B-cover, on actual vertices

The class-free native loose-full-tree theorem produces a native EHN map
and INTERNAL copies of the native B. For arbitrary genuine Option(Set)
operations, collapseDomain is not faithful: a mixed source-defined empty
input disappears. The Dom/Empty/value expansion is faithful and its
legal structures survive free native amalgamation.

We assemble those already proved interfaces on the SAME output carrier
and SAME EHN vertex map. This proves internal B copies and a genuine
original partial homomorphism-embedding. Exact small H-completions
and the final class-local Ramsey transfer remain separate.
-/

namespace StructuralRamsey.Structure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V W P X : Type v}

/-- The actual selected EHN map of a LEGAL Dom/Empty structure is
an original source-defined rich Option(Set) homomorphism-embedding
of its exact decoder. The vertex map is unchanged. -/
theorem IsLegalDomainEmpty.ehn_to_richOptionHE
    {Native : Structure L.withDomainEmptyFlags W}
    {Control : PartialSetStructure L P}
    {q : W → P}
    (hLegal : IsLegalDomainEmpty Native)
    (hq : Native.IsEHNHomomorphismEmbedding
      Control.domainEmptyEncode q) :
    (Native.domainEmptyDecode).IsOptionClosedFreeHomomorphismEmbedding
      Control q := by
  have hCanon :
      Native.domainEmptyDecode.domainEmptyEncode = Native :=
    hLegal.decodeEncode_eq
  apply PartialSetStructure.IsOptionClosedFreeHomomorphismEmbedding.ofDomainEmptyEHN
  simpa only [hCanon] using hq

/-- Every genuine domain-aware irreducible in a CANONICAL native
loose B-tree lies inside a full genuine B-copy on the original map.
Defined-empty tuples are seen by their Dom/Empty relations. -/
theorem LooseTreeAmalgam.richOptionIrreducible_contained_in_BCopy
    {Base : PartialSetStructure L V}
    {Decoded : PartialSetStructure L W}
    (hTree : LooseTreeAmalgam Base.domainEmptyEncode W
      Decoded.domainEmptyEncode)
    (E : PartialSetStructure L X)
    (hE : E.IsOptionClosedFreeIrreducible)
    (e : PartialSetStructure.Embedding E Decoded) :
    ∃ j : PartialSetStructure.Embedding Base Decoded,
      ∀ x : X, ∃ b : V, e.toFun x = j.toFun b := by
  let eNative : Embedding E.domainEmptyEncode
      Decoded.domainEmptyEncode := e.domainEmptyEncode
  have hNativeIrred : E.domainEmptyEncode.Irreducible :=
    PartialSetStructure.IsOptionClosedFreeIrreducible.domainEmptyEncode_irreducible
      E hE
  obtain ⟨jNative, hjNative⟩ :=
    hTree.irreducible_contained_in_copy hNativeIrred eNative
  refine ⟨PartialSetStructure.Embedding.ofDomainEmptyEncode jNative, ?_⟩
  intro x
  obtain ⟨b, hb⟩ := hjNative x
  exact ⟨b, hb⟩

/-- An ACTUAL native loose tree of legal B decodes to a genuinely
partial B-covered witness, on precisely its original vertex set. -/
theorem LooseTreeAmalgam.richOptionDecoded_internalBCover
    {Base : PartialSetStructure L V}
    {Native : Structure L.withDomainEmptyFlags W}
    (hTree : LooseTreeAmalgam Base.domainEmptyEncode W Native)
    (E : PartialSetStructure L X)
    (hE : E.IsOptionClosedFreeIrreducible)
    (e : PartialSetStructure.Embedding E Native.domainEmptyDecode) :
    ∃ j : PartialSetStructure.Embedding Base Native.domainEmptyDecode,
      ∀ x : X, ∃ b : V, e.toFun x = j.toFun b := by
  have hLegal : IsLegalDomainEmpty Native :=
    hTree.isLegalDomainEmpty (domainEmptyEncode_isLegal Base)
  have hCanon :
      Native.domainEmptyDecode.domainEmptyEncode = Native :=
    hLegal.decodeEncode_eq
  have hTreeCanon :
      LooseTreeAmalgam Base.domainEmptyEncode W
        Native.domainEmptyDecode.domainEmptyEncode := by
    simpa only [hCanon] using hTree
  exact hTreeCanon.richOptionIrreducible_contained_in_BCopy E hE e

/-- BOTH intrinsic endpoints on the SAME decoded loose B-tree and
SAME selected EHN projection. No local H-completion is inferred. -/
theorem LooseTreeAmalgam.richOptionDecoded_HE_and_internalBCover
    {Base : PartialSetStructure L V}
    {Control : PartialSetStructure L P}
    {Native : Structure L.withDomainEmptyFlags W}
    {q : W → P}
    (hTree : LooseTreeAmalgam Base.domainEmptyEncode W Native)
    (hq : Native.IsEHNHomomorphismEmbedding
      Control.domainEmptyEncode q) :
    (Native.domainEmptyDecode).IsOptionClosedFreeHomomorphismEmbedding
      Control q ∧
    (∀ {X : Type v} (E : PartialSetStructure L X),
      E.IsOptionClosedFreeIrreducible →
      ∀ e : PartialSetStructure.Embedding E Native.domainEmptyDecode,
        ∃ j : PartialSetStructure.Embedding
          Base Native.domainEmptyDecode,
          ∀ x : X, ∃ b : V, e.toFun x = j.toFun b) := by
  have hLegal : IsLegalDomainEmpty Native :=
    hTree.isLegalDomainEmpty (domainEmptyEncode_isLegal Base)
  constructor
  · exact hLegal.ehn_to_richOptionHE hq
  · intro X E hE e
    exact hTree.richOptionDecoded_internalBCover E hE e

end StructuralRamsey.Structure
