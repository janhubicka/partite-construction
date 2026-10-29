import PartiteConstruction.Functional.WholeMaskCanonicalEmbeddingInverse2019
import PartiteConstruction.Functional.WholeMaskTagInduce2019
import PartiteConstruction.Functional.WholeMaskWeakDomainObstruction2019
import PartiteConstruction.Structure.PartialSetFunctionsWholePartWeakDictionary

/-!
# Exact criterion for canonical 2019 whole-mask weak restrictions

The canonical OLD complete-mask graph of a whole-fibre weak restriction
on the literal vertex set S agrees with the induced AMBIENT OLD
complete-mask graph on the SAME S precisely when S is CLOSED under
all defined partial function values of the original source.

The forward implication constructs a full genuine functional
inclusion and hence a full OLD induced embedding.  For the reverse
implication, equality of the two OLD graphs would produce a FULL
genuine partial-function inclusion from the weak source into A,
using the verified canonical inverse.  If S were nonclosed,
the proven domain-loss obstruction excludes this full embedding.

The statement includes some-empty, repeated arguments, arbitrary
set-valued transversal fibres and nullaries.  It characterizes
the exact borderline between canonical full functional copies
and semi-closed ambient relational weak tests; it neither enlarges
S nor imposes any false full embedding on a nonclosed weak test.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V : Type w}

/-- A CLOSED whole-fibre weak restriction has exactly the inherited
canonical complete-mask OLD domain, output and ordinary relations.
No full-closure hull of an unclosed source is taken. -/
theorem wholeWeakInduce_wholeMaskPatternGraph_eq_induce_of_closed
    (A : PartialSetStructure L V)
    (part : V → P) (S : Set V) (hS : A.IsClosed S) :
    (wholeWeakInduce A S).wholeMaskPatternGraph
      (part ∘ Subtype.val) =
      (A.wholeMaskPatternGraph part).induce S := by
  classical
  let e : Embedding (wholeWeakInduce A S) A := {
    toFun := Subtype.val
    injective := Subtype.val_injective
    map_rel_iff := fun _ _ => Iff.rfl
    map_func := by
      intro F xs
      change
        (wholeWeakValue S
          (A.func F (Subtype.val ∘ xs))).map
            (Structure.imageSet Subtype.val) =
          A.func F (Subtype.val ∘ xs)
      cases hv : A.func F (Subtype.val ∘ xs) with
      | none =>
          simp [hv, wholeWeakValue]
      | some T =>
          have hT : T ⊆ S :=
            hS F (Subtype.val ∘ xs) T (fun i => (xs i).2) hv
          rw [hv, wholeWeakValue_of_subset S T hT]
          simp only [Option.map_some]
          congr 1
          ext y
          constructor
          · rintro ⟨z, hz, rfl⟩
            exact hz
          · intro hy
            exact ⟨⟨y, hT hy⟩, hy, rfl⟩
  let eOld : RelStructure.Embedding
      ((wholeWeakInduce A S).wholeMaskPatternGraph
        (part ∘ Subtype.val))
      (A.wholeMaskPatternGraph part) :=
    e.wholeMaskPatternGraph (part ∘ Subtype.val) part
      (fun _ => rfl)
  apply RelStructure.rel_injective
  funext R xs
  exact propext (eOld.map_rel_iff R xs).symm

/-- Conversely a canonical full OLD induced weak graph is possible
ONLY on a genuine function-closed carrier.  The failure on an
unclosed test is already witnessed by ambient active-domain bits
for a defined function value leaving S. -/
theorem wholeWeakInduce_isClosed_of_wholeMaskPatternGraph_eq_induce
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (S : Set V)
    (hEq :
      (wholeWeakInduce A S).wholeMaskPatternGraph
        (part ∘ Subtype.val) =
        (A.wholeMaskPatternGraph part).induce S) :
    A.IsClosed S := by
  classical
  let Weak := wholeWeakInduce A S
  have hTransWeak : FibreTransversal Weak (part ∘ Subtype.val) :=
    FibreTransversal.wholeWeakInduce A part hTrans S
  let eOld : RelStructure.Embedding
      (Weak.wholeMaskPatternGraph (part ∘ Subtype.val))
      (A.wholeMaskPatternGraph part) := by
    rw [hEq]
    exact RelStructure.inclusion (A.wholeMaskPatternGraph part) S
  let e : Embedding Weak A :=
    Embedding.ofCanonicalWholeMaskPatternGraph
      Weak A (part ∘ Subtype.val) part
      hTransWeak hTrans eOld
  intro F xs T hxs hVal y hy
  by_contra hyOutside
  let xsS : Fin (L.funcArity F) → S :=
    fun i => ⟨xs i, hxs i⟩
  have hValue : A.func F (Subtype.val ∘ xsS) = some T := by
    simpa only [xsS] using hVal
  have hLost : ¬ T ⊆ S := by
    intro hT
    exact hyOutside (hT hy)
  have hNot := canonicalOldInclusion_not_fullWeakEmbedding_of_lost_output
    A part hTrans S F xsS T hValue hLost
  exact hNot ⟨e, fun _ => rfl⟩

/-- The exact OLD whole-mask presentation commutes with whole-fibre
weak induction if and only if no defined output leaves S.
The weaker complete-OUTPUT fragment does commute on EVERY S. -/
theorem wholeWeakInduce_wholeMaskPatternGraph_eq_induce_iff_closed
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (S : Set V) :
    (wholeWeakInduce A S).wholeMaskPatternGraph
        (part ∘ Subtype.val) =
      (A.wholeMaskPatternGraph part).induce S ↔
    A.IsClosed S := by
  constructor
  · exact wholeWeakInduce_isClosed_of_wholeMaskPatternGraph_eq_induce
      A part hTrans S
  · exact wholeWeakInduce_wholeMaskPatternGraph_eq_induce_of_closed
      A part S

/-- The same iff holds after adding the canonical 2019 full-root
closure tags, because the tagged language retains the complete
OLD mask language as a literal reduct. -/
theorem wholeWeakInduce_wholeMaskTagExpansion_eq_induce_iff_closed
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (S : Set V) :
    wholeMaskTagExpansion
        ((wholeWeakInduce A S).wholeMaskPatternGraph
          (part ∘ Subtype.val)) =
      (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)).induce S ↔
    A.IsClosed S := by
  constructor
  · intro hTag
    apply (wholeWeakInduce_wholeMaskPatternGraph_eq_induce_iff_closed
      A part hTrans S).mp
    apply RelStructure.rel_injective
    funext R xs
    exact congrArg
      (fun E : RelStructure (L.wholeMaskTagLanguage P) S =>
        E.rel (.inl R) xs) hTag
  · intro hClosed
    calc
      wholeMaskTagExpansion
          ((wholeWeakInduce A S).wholeMaskPatternGraph
            (part ∘ Subtype.val)) =
        wholeMaskTagExpansion
          ((A.wholeMaskPatternGraph part).induce S) := by
            rw [wholeWeakInduce_wholeMaskPatternGraph_eq_induce_of_closed
              A part S hClosed]
      _ = (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)).induce S :=
        wholeMaskTagExpansion_induce_eq (A.wholeMaskPatternGraph part) S

end StructuralRamsey.PartialSetStructure
