import PartiteConstruction.Functional.WeakInvariant
import PartiteConstruction.Functional.WeakOperations

/-!
# Each Hales-Jewett coordinate projection is EHN, not merely weak

The genuine functional Hales-Jewett power carries a weak coordinate
map to the original selected-support partite system. The existing
`power_weaklyPartiteOver` proof also shows that every irreducible
full substructure of the power has a FULL part embedding into A.

Fix an irreducible full E-copy in the power. Its chosen coordinate
image need not initially be function closed. However its FUNCTION-
CLOSED HULL is irreducible, by the already checked generated weak
image lemma, and the original partite projection gives a FULL
embedding of that hull into A. The full E-copy itself also embeds
into A via the already verified power EHN theorem. Both maps
agree with the part projection on the coordinate image.

CANCEL the full embedding of the hull into A. This makes the
coordinate map on E a FULL embedding into the hull, and hence into
the original selected-support functional structure.

Consequently **each individual coordinate evaluation is an EHN
homomorphism-embedding**, even when the original B→A part map is
only EHN and genuinely set-valued function images are present.
No singleton reduction or artificial domain-reflection assumption
is used. The closure hull occurs solely inside the local proof
of irreducibility, NEVER in the weak-vertex test/rank.

This is the direct functional shadow needed by the actual native
Hales-Jewett line-attachment induction. It does not imply that all
different line attachments have one COMMON chosen coordinate.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V : Type v}
variable {A : Structure L P} {B : System L P V}
variable {N : ℕ}

/-- Coordinate evaluation of a genuine FUNCTIONAL Hales-Jewett power
is an EHN homomorphism-embedding into the selected partite system
at every coordinate, provided B is EHN-partite over A and N>0.

On an arbitrary irreducible full source E its restriction is a
FULL functional embedding, with all operation-value fibres mapped
exactly, not only positive incidence. -/
theorem coordinateEHN
    (hB : B.WeaklyPartiteOver A) (hN : 0 < N)
    (i : Fin N) :
    (power B N).toStructure.IsEHNHomomorphismEmbedding
      B.toStructure (fun z => z.coord i) := by
  classical
  let C := power B N
  have hPower : C.WeaklyPartiteOver A :=
    power_weaklyPartiteOver hB hN
  constructor
  · exact coordinateWeak i
  · intro X E hE e
    let q : X → V := fun x => (e x).coord i
    have hq : E.IsWeakHomomorphism B.toStructure q :=
      (coordinateWeak i).comp e.isWeakHomomorphism
    let S : Set V := B.toStructure.functionClosure (Set.range q)
    have hS : B.toStructure.IsClosed S :=
      B.toStructure.functionClosure_isClosed (Set.range q)
    let H := B.toStructure.induce S hS
    have hH : H.Irreducible :=
      hE.functionClosure_weakImage hq
    let inc : Embedding H B.toStructure :=
      inclusion B.toStructure S hS
    obtain ⟨gH, hgH⟩ := hB.2 H hH inc
    obtain ⟨gE, hgE⟩ := hPower.2 E hE e
    have hqs : ∀ x : X, q x ∈ S := by
      intro x
      exact B.toStructure.subset_functionClosure
        (Set.range q) ⟨x, rfl⟩
    let qs : X → S := fun x => ⟨q x, hqs x⟩
    have hEq : ∀ x, gE x = gH (qs x) := by
      intro x
      calc
        gE x = C.part (e x) := hgE x
        _ = B.part (q x) := ((e x).belongs i).symm
        _ = gH (qs x) := (hgH (qs x)).symm
    let eH : Embedding E H :=
      gE.factorWithMap gH qs hEq
    let eB : Embedding E B.toStructure := inc.comp eH
    refine ⟨eB, ?_⟩
    intro x
    rfl

end StructuralRamsey.FunctionalPartite.Induced
