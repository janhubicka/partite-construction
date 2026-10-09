import PartiteConstruction.Ramsey.CopywiseFreeFold

/-! # Compatible target diagrams without full hereditariness

Theorem 2.18 assumes hereditary closure only for U-closed substructures.
The existing `FiniteStrongAmalgamationClass` packages full hereditariness
and is therefore not the right input for the general nonempty-U case.

This module isolates finite strong amalgamation over a root KNOWN to be
in K. A compatible completion diagram then yields a K-target preserving
B-copies of a free source amalgam. The source separator may be reducible
and its map into the shared K-root need not be injective.

The common target diagram is an explicit premise. Producing it from the
Picture history is a separate unproved induction step; it is not inferred
from independent completions of the two sides.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Finite strong amalgamation over members of K, without any hereditary
or free-amalgamation axiom. In particular the common root is explicitly
required to belong to K, as in Definition 2.17(3). -/
def HasFiniteStrongAmalgamation
    (K : StructureClass.{u,v} (L := L)) : Prop :=
  ∀ {H E F : Type v} [Finite H] [Finite E] [Finite F]
    (Root : RelStructure L H) (Left : RelStructure L E)
    (Right : RelStructure L F),
    K Root → K Left → K Right →
    ∀ (sL : Embedding Root Left) (sR : Embedding Root Right),
      ∃ (Z : Type v) (_ : Finite Z) (Target : RelStructure L Z),
        K Target ∧
        ∃ (jL : Embedding Left Target) (jR : Embedding Right Target),
          (∀ d, jL (sL d) = jR (sR d)) ∧
          (∀ a b, jL a = jR b →
            ∃ d, a = sL d ∧ b = sR d)

/-- Glue B-copywise completions whose restrictions to the source root
factor through the SAME member Q of K. The target amalgam may add mixed
relations. The conclusion does not assert a global homomorphism or
completion of all U-irreducible tests. -/
theorem HasCopywiseCompletion.of_compatible_class_diagram
    {K : StructureClass.{u,v} (L := L)}
    (hK : HasFiniteStrongAmalgamation K)
    {VB H E F C P X Y : Type v}
    {Base : RelStructure L VB}
    {Root : RelStructure L H}
    {Left : RelStructure L E} {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hBase : Base.Irreducible)
    (hSrc : IsFreeAmalgam sL sR iL iR)
    [Finite P] [Finite X] [Finite Y]
    (Q : RelStructure L P) (TL : RelStructure L X)
    (TR : RelStructure L Y)
    (hQ : K Q) (hTL : K TL) (hTR : K TR)
    (q : H → P) (fL : E → X) (fR : F → Y)
    (hL : CopywiseCompletion Base Left TL fL)
    (hR : CopywiseCompletion Base Right TR fR)
    (eL : Embedding Q TL) (eR : Embedding Q TR)
    (hCompatL : ∀ r, fL (sL r) = eL (q r))
    (hCompatR : ∀ r, fR (sR r) = eR (q r)) :
    HasCopywiseCompletion K Base Whole := by
  obtain ⟨Z, hZ, Target, hTarget, jL, jR, hGlue, _⟩ :=
    hK Q TL TR hQ hTL hTR eL eR
  have hCompat : ∀ r, jL (fL (sL r)) = jR (fR (sR r)) := by
    intro r
    calc
      jL (fL (sL r)) = jL (eL (q r)) := congrArg jL (hCompatL r)
      _ = jR (eR (q r)) := hGlue (q r)
      _ = jR (fR (sR r)) := congrArg jR (hCompatR r).symm
  refine ⟨Z, hZ, Target, hTarget,
    hSrc.compatibleFold (jL ∘ fL) (jR ∘ fR) hCompat, ?_⟩
  exact CopywiseCompletion.fold_free hBase hSrc
    fL fR hL hR jL jR hCompat

end StructuralRamsey.RelStructure
