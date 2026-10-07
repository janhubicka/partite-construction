import PartiteConstruction.Functional.EHNStrongInduction
import PartiteConstruction.Functional.EHNRootDichotomy

/-! # Induction over a closed EHN attachment root

The weak projection on the support of a functional EHN Picture step is an
EHN homomorphism-embedding, not necessarily a full embedding.  A closed
finite overlap can therefore have a reducible root.  Its separator needs
a common tree completion before the two side witnesses can be extended.

The induction below is on the *closed root itself*, not on arbitrary weak
substructures.  In the free-amalgam branch the caller receives the
induction hypothesis for the common part as well as both proper sides.
Consequently the remaining geometric obligation can be expressed as one
common-root extension step, without pretending that every overlap embeds
into a single A-copy.
-/

namespace StructuralRamsey.Structure.IsEHNHomomorphismEmbedding

universe u v

variable {L : Language.{u}}
variable {P W : Type v}
variable {D : Structure L P} {C : Structure L W}
variable {p : W → P}

/-- Induct on a finite function-closed test of an EHN source.  In the
reducible branch the common part is explicitly available recursively.
The hypothesis [Finite W] is used only to invoke finite strong induction
on the (closed) subtype carried by the test. -/
theorem closedTest_induction_with_common
    [Finite W]
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    (Q : ∀ {X : Type v}, Structure L X → (X → P) → Prop)
    (hembed :
      ∀ {X : Type v} [Finite X]
        (E : Structure L X) (q : X → P),
        E.IsEHNHomomorphismEmbedding D q →
        (∃ g : Embedding E D, ∀ x, g x = q x) →
        Q E q)
    (hfree :
      ∀ {X : Type v} [Finite X]
        (E : Structure L X) (q : X → P),
        E.IsEHNHomomorphismEmbedding D q →
        ∀ d : ProperFreeDecomposition E,
          Q d.common (q ∘ d.leftIn ∘ d.toLeft) →
          Q d.left (q ∘ d.leftIn) →
          Q d.right (q ∘ d.rightIn) →
          Q E q) :
    let Small := C.induce (↑S : Set W) hS
    let inc : Embedding Small C :=
      inclusion C (↑S : Set W) hS
    Q Small (p ∘ inc) := by
  classical
  let Small := C.induce (↑S : Set W) hS
  let inc : Embedding Small C :=
    inclusion C (↑S : Set W) hS
  have hSmall :
      Small.IsEHNHomomorphismEmbedding D (p ∘ inc) :=
    hp.comp inc.isEHNHomomorphismEmbedding
  exact finite_free_induction_with_common hSmall Q hembed hfree

end StructuralRamsey.Structure.IsEHNHomomorphismEmbedding


namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {P U V : Type v}
variable {D : Structure L P}
variable {A : Structure L U}
variable {B : System L P V}

/-- Specialized common-aware induction for the actual closed overlap inside
an EHN Picture attachment.  The labels take values in A, because the
canonical support is weakly A-partite.  The embedded branch is genuinely
a full A-embedding, while a reducible overlap is handled through its strict
free-amalgam decomposition and its recursively completed separator. -/
theorem closedRoot_induction_with_common
    [Finite V]
    (hB : B.WeaklyPartiteOver D)
    (alpha : Structure.Embedding A D)
    (RootTest : Finset (B.support alpha.toFunctionEmbedding))
    (hRoot :
      (B.weakRestrict D hB.1 A alpha).toStructure.IsClosed
        (↑RootTest : Set _))
    (Q : ∀ {X : Type v}, Structure L X → (X → U) → Prop)
    (hembed :
      ∀ {X : Type v} [Finite X]
        (E : Structure L X) (q : X → U),
        E.IsEHNHomomorphismEmbedding A q →
        (∃ g : Structure.Embedding E A, ∀ x, g x = q x) →
        Q E q)
    (hfree :
      ∀ {X : Type v} [Finite X]
        (E : Structure L X) (q : X → U),
        E.IsEHNHomomorphismEmbedding A q →
        ∀ d : Structure.ProperFreeDecomposition E,
          Q d.common (q ∘ d.leftIn ∘ d.toLeft) →
          Q d.left (q ∘ d.leftIn) →
          Q d.right (q ∘ d.rightIn) →
          Q E q) :
    let WR := B.weakRestrict D hB.1 A alpha
    let Small := WR.toStructure.induce (↑RootTest : Set _) hRoot
    let inc : Structure.Embedding Small WR.toStructure :=
      Structure.inclusion WR.toStructure (↑RootTest : Set _) hRoot
    Q Small (WR.part ∘ inc) := by
  exact
    IsEHNHomomorphismEmbedding.closedTest_induction_with_common
      (B.weakRestrict_invariant D hB.1 A alpha hB)
      RootTest hRoot Q hembed hfree

end StructuralRamsey.FunctionalPartite
