import PartiteConstruction.Functional.EHNPartPreservingRetractFamily
import PartiteConstruction.Functional.EHNLineAttachmentRetraction
import PartiteConstruction.Functional.EHNLineOnlyPicture

/-!
# Track D: positive strict functional locality for genuine HJ common-parameter line families

This is a concrete (though geometrically restricted) POSITIVE
history theorem for the ACTUAL native functional Hales--Jewett Picture.

Choose one parameter coordinate i shared by every full line W in a
finite list. The exact tagged coordinatewise power admits an EHN
shadow to the selected old support by evaluating coordinate i. Its
composition with EVERY specified full line embedding is the identity
on the original function-closed A-support. Therefore the genuine
successive native full functional attachments admit one EHN shadow
onto the copied old Picture, preserving the original part projection.

Every exact n-vertex weak test of the resulting stage has a strict
full-functional B-tree completion with actual A-intersection and
arbitrary projected-history protection, provided the OLD stage has
the corresponding n-vertex witness. This is a mathematical theorem,
not an unproved hAttach hypothesis or a purely relational proxy.

The theorem is intentionally restricted to lines sharing i. The
documented genuine three-line C7 uses parameter sets {1}, {0},
and {0,1}, with no COMMON coordinate, and is not covered. The
full arbitrary HJ Picture and maximal multi-generated mixed roots
remain open.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}}
variable {P V U UA VB : Type v}

/-- For an ACTUAL Hales--Jewett power and any finite list of its full
support line embeddings sharing a parameter coordinate, attach genuine
entire OLD copies along those lines. The resulting native functional
system retains the strict full-functional exact weak-history n-bound.

The proof uses an explicit original-stage retraction, not the false
arbitrary-stage maximal mixed-root schema, and counts only literal
tested vertices rather than any function-generated closure hull. -/
theorem lineFamily_commonParameter_strictWeakHistory
    [DecidableEq V]
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (A : Structure L U) (alpha : Structure.Embedding A D)
    (N : ℕ) (hN : 0 < N) (i : Fin N)
    (lines : List (Line (Induced.Letter A
      (B.weakRestrict D hB.1 A alpha)) N))
    (hCommon : ∀ W ∈ lines, W.symbol i = .parameter)
    (TestA : Structure L UA) (Base : Structure L VB)
    (hTestA : TestA.Irreducible)
    (n : ℕ)
    (hOld : SetAmbientRelativeWeakTreeWitness.AtMost
      TestA Base B.toStructure B.part n) :
    let S : Set V := B.support alpha.toFunctionEmbedding
    let hS : B.toStructure.IsClosed S :=
      B.weak_support_closed D hB.1 A alpha
    let R := B.weakRestrict D hB.1 A alpha
    let E := Induced.power R N
    let Core := E.relabel alpha.toFunctionEmbedding
    ∃ (X : Type v) (T : System L P X)
      (j : FunctionalPartite.Embedding Core T),
      SetAmbientRelativeWeakTreeWitness.AtMost
        TestA Base T.toStructure T.part n := by
  classical
  dsimp only
  let S : Set V := B.support alpha.toFunctionEmbedding
  let hS : B.toStructure.IsClosed S :=
    B.weak_support_closed D hB.1 A alpha
  let R := B.weakRestrict D hB.1 A alpha
  let E := Induced.power R N
  let Core := E.relabel alpha.toFunctionEmbedding
  have hR : R.WeaklyPartiteOver A :=
    B.weakRestrict_invariant D hB.1 A alpha hB
  let q0 : Induced.Vertex R N → V :=
    fun z => (z.coord i).1
  let inc : Structure.Embedding R.toStructure B.toStructure :=
    B.weakRestrictInclusion D hB.1 A alpha
  have hCoord : E.toStructure.IsEHNHomomorphismEmbedding
      R.toStructure (fun z => z.coord i) :=
    Induced.coordinateEHN hR hN i
  have hq0 : Core.toStructure.IsEHNHomomorphismEmbedding
      B.toStructure q0 :=
    inc.isEHNHomomorphismEmbedding.comp hCoord
  have hPart0 : ∀ z : Induced.Vertex R N,
      B.part (q0 z) = Core.part z := by
    intro z
    calc
      B.part (q0 z) =
          alpha (R.part (z.coord i)) :=
        (B.restrictedPart_spec alpha.toFunctionEmbedding (z.coord i)).symm
      _ = alpha z.part := congrArg alpha (z.belongs i)
      _ = Core.part z := rfl
  let maps : Line (Induced.Letter A R) N →
      FunctionalPartite.Embedding (B.induce S hS) Core :=
    fun W => {
      toEmbedding := (Induced.weak_lineEmbedding hR.1 W).toEmbedding
      map_part := fun x =>
        (congrArg alpha
          ((Induced.weak_lineEmbedding hR.1 W).map_part x)).trans
          (B.restrictedPart_spec alpha.toFunctionEmbedding x)
    }
  have hSplit : ∀ W ∈ lines, ∀ x : S,
      q0 (maps W x) = x.1 := by
    intro W hW x
    have hEval :=
      (Induced.line_parameter_coordinate_EHN_retraction
        hR W i (hCommon W hW)).2 x
    change ((Induced.weak_lineEmbedding hR.1 W x).coord i).1 = x.1
    exact congrArg Subtype.val hEval
  exact attachFamily_splitRoot_strictWeakHistory
    B S hS Core q0 hq0 hPart0 maps lines hSplit
    TestA Base hTestA n hOld

end StructuralRamsey.FunctionalPartite.EHN
