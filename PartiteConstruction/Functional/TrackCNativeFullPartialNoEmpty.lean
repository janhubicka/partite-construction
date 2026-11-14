import PartiteConstruction.Functional.TrackENativePartialFullFaithfulness
import PartiteConstruction.Functional.PartialDomainGraphClosedRange2019
import PartiteConstruction.Functional.TrackBRealEHNExactImageUSize2019

/-!
# Track C: a full native copy into a NoDefinedEmpty Option(Set) control
#       is a FULL genuine-partial copy on precisely the same vertices.

The selected 2019 two-pass final covered partial decoder P has
NoDefinedEmptyValues when its native Base B does. Track E gives FULL
native embeddings of every actual irreducible test into P.collapseDomain.

We show that such native full embeddings automatically lift to FULL
genuine partial Option(Set) embeddings into P itself and have a
function-closed exact image. There is no collapse on the SOURCE
partial structure and no replacement of the source by its
closure-hull. This is an essential auxiliary lemma for the
nonempty-valued original 2019 cover-and-pullback proof.

The rich defined-empty case instead needs the faithful Dom/Empty
encoding in Track C #665. It must NOT use this native/partial
roundtrip without the explicit NoDefinedEmptyValues premise.
-/

namespace StructuralRamsey.Structure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure.TrackENativePartialFullFaithfulness

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- A native FULL embedding E → P.collapseDomain into a genuinely
partial target with NO defined-empty inputs is a FULL original
Option(Set) embedding E.toNonemptyPartial → P with the SAME map.
All primitive domain bits and values are reflected. -/
theorem Embedding.toPartialOfNoDefinedEmpty
    {E : Structure L V} {P : PartialSetStructure L W}
    (hP : NoDefinedEmptyValues P)
    (g : Embedding E P.collapseDomain) :
    PartialSetStructure.Embedding E.toNonemptyPartial P := by
  have hEq : P.collapseDomain.toNonemptyPartial = P :=
    (noDefinedEmpty_iff_nativeRoundtrip P).mp hP
  simpa only [hEq] using g.toNonemptyPartial

/-- The exact image of a native FULL copy in a genuine
NoDefinedEmpty partial target is function-closed there, including
all nullary and multivalued values. No image-hull inflation. -/
theorem Embedding.toPartialOfNoDefinedEmpty_rangeClosed
    {E : Structure L V} {P : PartialSetStructure L W}
    (hP : NoDefinedEmptyValues P)
    (g : Embedding E P.collapseDomain) :
    P.IsClosed (Set.range g.toFun) := by
  exact (g.toPartialOfNoDefinedEmpty hP).range_isClosed


variable {U : Type v}

/-- Any genuine native EHN/original-2019 homomorphism-embedding into
the NATIVE COLLAPSE of a no-defined-empty partial target is an
ORIGINAL source-defined Option(Set) homomorphism into that SAME
partial target. The underlying vertex map is unchanged, and no
undefined-domain reflection is introduced.

This is the positive source-map bridge needed to use the
already verified n-vertex weak completion pullback with the
actual native second-cover projection q. -/
theorem IsEHNHomomorphismEmbedding.toPartialTargetOfNoDefinedEmpty
    {E : Structure L V} {P : PartialSetStructure L U}
    {q : V → U}
    (hP : NoDefinedEmptyValues P)
    (hq : E.IsEHNHomomorphismEmbedding P.collapseDomain q) :
    PartialSetStructure.IsOriginalPartialHomomorphism
      E.toNonemptyPartial P q := by
  have hOriginal :
      IsOriginalPartialHomomorphism E P.collapseDomain q :=
    hq.toOriginalPartial.1
  have hPartial :
      PartialSetStructure.IsOriginalPartialHomomorphism
        E.toNonemptyPartial P.collapseDomain.toNonemptyPartial q :=
    hOriginal.toNonemptyPartial
  have hEq : P.collapseDomain.toNonemptyPartial = P :=
    (noDefinedEmpty_iff_nativeRoundtrip P).mp hP
  simpa only [hEq] using hPartial

end StructuralRamsey.Structure
