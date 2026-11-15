import PartiteConstruction.Functional.TrackCDomainEmptyLegalLooseTree
import PartiteConstruction.Functional.TrackCOptionIrredNative
import PartiteConstruction.Functional.LooseTreeAmalgam

/-!
# Track C: internal genuine rich B-copies in a legal native loose B-tree

The English second native B-cover pass must satisfy the ORIGINAL
intrinsic locally finite subclass axiom: every irreducible genuine
partial substructure of the completed witness extends to an
ACTUAL full copy of B INSIDE that same witness.

The native LooseTreeAmalgam theorem already proves that every
native irreducible full E-copy lies in a constituent native B-copy.
For rich Option(Set) this must not be applied after collapsing
defined-empty values, which can destroy irreducibility.

Instead, let T be any LEGAL native Dom/Empty tree of the canonical
faithful encoding B.domainEmptyEncode. Every full rich partial
E-copy in its EXACT genuine decoder T.domainEmptyDecode expands
to a FULL native E.domainEmptyEncode copy in T (F1).
The verified F4 lemma makes this native copy irreducible.
The verified loose-tree localization gives a NATIVE B-copy in T
containing that exact E image. Because T is LEGAL, F1 decodes
this B-copy to a FULL genuine Option(Set) B-copy in the same
partial target, including undefined/defined-empty distinction.

The resulting inclusion uses the same original vertex maps.
No generated closure hull, no abstract external Test -> B coverage,
no filler B-copies outside the actual second witness.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V W : Type v}

/-- Every irreducible genuine partial full substructure of a
LEGAL native loose tree over the faithful encoding of B extends
INTERNALLY to one actual FULL genuine B-copy, on the exact same
decoded target and with the original E vertex map.

The irreducibility premise is the definedness-sensitive
closed-free-cover predicate (including source-defined empty inputs).
The parent F4 theorem has verified its implication to native
universal irreducibility of the faithful encoding. -/
theorem LooseTreeAmalgam.richOptionIrred_extendsToInternalB
    (B : PartialSetStructure L V)
    (T : Structure L.withDomainEmptyFlags W)
    (hT : Structure.IsLegalDomainEmpty T)
    (hTree : Structure.LooseTreeAmalgam B.domainEmptyEncode W T)
    (E : PartialSetStructure L U)
    (hE : E.IsOptionClosedFreeIrreducible)
    (e : Embedding E T.domainEmptyDecode) :
    ∃ j : Embedding B T.domainEmptyDecode,
      ∀ a : U, ∃ b : V, e.toFun a = j.toFun b := by
  classical
  let eTag : Structure.Embedding E.domainEmptyEncode
      T.domainEmptyDecode.domainEmptyEncode :=
    e.domainEmptyEncode
  have hTCanonical :
      T.domainEmptyDecode.domainEmptyEncode = T :=
    hT.decodeEncode_eq
  let eNative : Structure.Embedding E.domainEmptyEncode T := by
    simpa only [hTCanonical] using eTag
  have hNativeIrred : E.domainEmptyEncode.Irreducible :=
    IsOptionClosedFreeIrreducible.domainEmptyEncode_irreducible E hE
  obtain ⟨jNative, hjNative⟩ :=
    hTree.irreducible_contained_in_copy hNativeIrred eNative
  let jTag : Structure.Embedding B.domainEmptyEncode
      T.domainEmptyDecode.domainEmptyEncode := by
    simpa only [hTCanonical] using jNative
  let j : Embedding B T.domainEmptyDecode :=
    Embedding.ofDomainEmptyEncode jTag
  refine ⟨j, ?_⟩
  intro a
  obtain ⟨b, hb⟩ := hjNative a
  refine ⟨b, ?_⟩
  change e.toFun a = jTag.toFun b
  calc
    e.toFun a = eNative.toFun a := rfl
    _ = jNative.toFun b := hb
    _ = jTag.toFun b := rfl

end StructuralRamsey.PartialSetStructure
