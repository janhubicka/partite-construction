import PartiteConstruction.Functional.EHNFiniteAttachmentShadow
import PartiteConstruction.Functional.EHNLineAttachmentRetraction
import PartiteConstruction.Functional.WeakHistoryShadowCardinality

/-!
# Simultaneous retraction of a whole family of native HJ line attachments

The Hales--Jewett Picture normally attaches old copies along many distinct
lines; their parameter-coordinate sets need not intersect. Nevertheless,
if a FINITE family of true HJ lines has ONE COMMON parameter coordinate i,
the SAME coordinate evaluation on the genuine functional power fixes
every attaching full support, and the identity on EACH copied old Picture
agrees with it. The verified finite full-functional attachment shadow
induction therefore yields one common EHN map back to Old.

This is stronger than the verified one-line retraction and a genuine
positive many-attachment statement. It is compatible with genuinely
multivalued set-valued functions and transversal output images.

The theorem does not assert retraction of all HJ lines: the C7
counterexample has no common parameter coordinate. Nor does it
manufacture strict completion witnesses for arbitrary maximal mixed
multi-line root systems.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P V U : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- A finite family of TRUE functional HJ lines sharing parameter
coordinate i admits a simultaneous EHN shadow to the old functional
Picture. Every prescribed full Old-copy remains embedded, and its
entire selected support coincides with the corresponding line image.

The source and all intermediate targets are genuine functional
partite systems with transversal set-valued function fibres. -/
theorem commonParameterLines_partCompatibleEHNShadow
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (A : Structure L U) [Finite U] [Finite P] (hKA : K A)
    (alpha : Structure.Embedding A D)
    (N : ℕ) (hN : 0 < N) (i : Fin N)
    (xs : List {W : Line
      (Induced.Letter A (B.weakRestrict D hB.1 A alpha)) N //
        W.symbol i = .parameter}) :
    let S := B.support alpha.toFunctionEmbedding
    let hS : B.toStructure.IsClosed S :=
      B.weak_support_closed D hB.1 A alpha
    let R := B.weakRestrict D hB.1 A alpha
    let E := Induced.power R N
    let Core := E.relabel alpha.toFunctionEmbedding
    ∃ T : Stage K D,
      ∃ core : FunctionalPartite.Embedding Core T.system,
        ∃ q : T.Carrier → V,
          T.system.toStructure.IsEHNHomomorphismEmbedding
            B.toStructure q ∧
          (∀ z : Induced.Vertex R N, q (core z) = (z.coord i).1) ∧
          (∀ z : T.Carrier, B.part (q z) = T.system.part z) ∧
          (∀ W ∈ xs,
            ∃ copy : FunctionalPartite.Embedding B T.system,
              ∀ x : S, copy x.1 =
                core (Induced.lineMap W.1 x)) := by
  classical
  dsimp only
  let S := B.support alpha.toFunctionEmbedding
  let hS : B.toStructure.IsClosed S :=
    B.weak_support_closed D hB.1 A alpha
  let R := B.weakRestrict D hB.1 A alpha
  have hR : R.WeaklyPartiteOver A :=
    B.weakRestrict_invariant D hB.1 A alpha hB
  let E := Induced.power R N
  have hE : E.WeaklyPartiteOver A :=
    Induced.power_weaklyPartiteOver hR hN
  let Core := E.relabel alpha.toFunctionEmbedding
  have hCore : Core.WeaklyPartiteOver D :=
    alpha.isEHNHomomorphismEmbedding.comp hE
  let T0 : Stage K D := {
    Carrier := Induced.Vertex R N
    finiteCarrier := inferInstance
    system := Core
    isPartite := hCore
    mem := mem_of_weaklyPartiteOver hK E hE hKA
  }
  let qE : T0.Carrier → V := fun z => (z.coord i).1
  let inc : Structure.Embedding R.toStructure B.toStructure :=
    B.weakRestrictInclusion D hB.1 A alpha
  have hCoordinate :
      E.toStructure.IsEHNHomomorphismEmbedding
        R.toStructure (fun z => z.coord i) :=
    Induced.coordinateEHN hR hN i
  have hqE : T0.system.toStructure.IsEHNHomomorphismEmbedding
      B.toStructure qE :=
    inc.isEHNHomomorphismEmbedding.comp hCoordinate
  have hpart : ∀ z : T0.Carrier, B.part (qE z) = T0.system.part z := by
    intro z
    calc
      B.part (qE z) = alpha (R.part (z.coord i)) :=
        (B.restrictedPart_spec alpha.toFunctionEmbedding (z.coord i)).symm
      _ = alpha z.part := congrArg alpha (z.belongs i)
      _ = T0.system.part z := rfl
  let Maps : {W : Line (Induced.Letter A R) N //
      W.symbol i = .parameter} →
        FunctionalPartite.Embedding (B.induce S hS) T0.system :=
    fun W => {
      toEmbedding := (Induced.weak_lineEmbedding hR.1 W.1).toEmbedding
      map_part := by
        intro x
        exact
          (congrArg alpha
            ((Induced.weak_lineEmbedding hR.1 W.1).map_part x)).trans
            (B.restrictedPart_spec alpha.toFunctionEmbedding x)
    }
  have hAgree :
      ∀ W : {W : Line (Induced.Letter A R) N //
          W.symbol i = .parameter}, ∀ x : S,
        qE (Maps W x) = x.1 := by
    intro W x
    change ((Induced.lineMap W.1 x).coord i).1 = x.1
    simp [Induced.lineMap, W.2]
  obtain ⟨T, core, q, hq, hcore, hp, hCopies⟩ :=
    attachList_partCompatibleEHNShadow
      hK B hB hmB S hS T0 qE hqE hpart
      Maps (fun _ v => v)
      (fun _ => (Structure.Embedding.id B.toStructure).isEHNHomomorphismEmbedding)
      (fun _ _ => rfl) hAgree xs
  refine ⟨T, core, q, hq, hcore, hp, ?_⟩
  intro W hW
  obtain ⟨copy, hcopy⟩ := hCopies W hW
  exact ⟨copy, hcopy⟩

end StructuralRamsey.FunctionalPartite.EHN
