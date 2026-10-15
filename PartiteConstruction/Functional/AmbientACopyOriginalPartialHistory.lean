import PartiteConstruction.Functional.OriginalPartialProjectedHistoryInvariant
import PartiteConstruction.Functional.InitialTreeCompletion
import PartiteConstruction.Functional.LooseTreeAmalgam

/-!
# Actual ambient A-copy intersections in original-partial strict tree witnesses

The published sparsening invariant speaks of intersections of the test
with ACTUAL ambient copies of A. It does not require every arbitrary
embedded closed partial A-piece to be placed inside a B-constituent.

Consequently an irreducible A and irreducible B suffice to certify the
initial EHN Picture: a full A-copy inside a strict B-tree is contained
in one B constituent. No hypothesis that EVERY closed substructure
of A is irreducible is needed for this narrower published-style
property.

The global test completion uses original-2019 partial homomorphism-
embeddings, so source-undefined function inputs may map to defined
target inputs. Source test sets are genuinely function-closed, counted
by generating rank, and never enlarged to their ambient closure.

This is the genuine initial case. Preservation of the invariant
through a mixed Hales-Jewett Picture attachment is not proved here.
-/


namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U P W VB : Type v}
variable {A : Structure L U} {D : Structure L P}
variable {C : Structure L W} {Base : Structure L VB}

/-- The image of every actual ambient A-copy, restricted to the exact
tested set, is controlled by a full A-copy in the completion target.
The chosen target copy is contained in an irreducible full piece;
it need not be the image of an arbitrary partial A-embedding. -/
def FunctionalAmbientACopyIntersections
    {Y : Type v} {Target : Structure L Y}
    (S : Finset W) (f : ↥(↑S : Set W) → Y) : Prop :=
  ∀ e : Embedding A C,
    ∃ eT : Embedding A Target,
      eT.ContainedInIrreducible ∧
      ∀ (a : U) (ha : e a ∈ (↑S : Set W)),
        eT a = f ⟨e a, ha⟩

/-- Published-style local strict B-tree completions with exact actual
ambient A-copy intersections and finite projected history diaries.

Unlike FunctionalOriginalPartialProjectedHistoryTreeLike, this
does NOT demand protected extensions of arbitrary closed PARTIAL
A-copies that do not extend to a genuine full ambient A-copy.
The global test map remains source-defined original-partial. -/
def FunctionalAmbientACopyHistoryTreeLike
    (p : W → P) (n : ℕ) : Prop :=
  ∀ (S : Finset W) (hS : C.IsClosed (↑S : Set W)),
    (C.induce (↑S : Set W) hS).GeneratedByAtMost n →
    ∀ history : List (Set P),
      ∃ (Z : Type v) (Target : Structure L Z),
        TreeAmalgam Base Z Target ∧
        ∃ f : ↥(↑S : Set W) → Z,
          IsOriginalPartialHomomorphismEmbedding
            (C.induce (↑S : Set W) hS) Target f ∧
          FunctionalAmbientACopyIntersections
            (A := A) (C := C) (Target := Target) S f ∧
          FunctionalRespectsProjectedHistory p S f history

namespace FunctionalAmbientACopyHistoryTreeLike

/-- The actual ambient A-copy history invariant is monotone in the
number of generators. -/
theorem mono
    {p : W → P} {m n : ℕ}
    (h : FunctionalAmbientACopyHistoryTreeLike
      (A := A) (C := C) (Base := Base) p n)
    (hmn : m ≤ n) :
    FunctionalAmbientACopyHistoryTreeLike
      (A := A) (C := C) (Base := Base) p m := by
  intro S hS hGen history
  exact h S hS (hGen.mono hmn) history

/-- A genuine strict B-tree has the published-style ambient A-copy
history invariant at EVERY generator rank. A and B need only be
irreducible; hereditary irreducibility of closed A-pieces is not assumed.

The strict target is the original source B-tree. We choose each
closed-test inclusion as its completion map, which also preserves all
projected history predicates by injectivity. -/
theorem of_tree
    (hA : A.Irreducible)
    (hBase : Base.Irreducible)
    (hTree : TreeAmalgam Base W C)
    (p : W → P) (n : ℕ) :
    FunctionalAmbientACopyHistoryTreeLike
      (A := A) (C := C) (Base := Base) p n := by
  intro S hS _hGen history
  let inc : Embedding (C.induce (↑S : Set W) hS) C :=
    inclusion C (↑S : Set W) hS
  have hPartial : IsOriginalPartialHomomorphismEmbedding
      (C.induce (↑S : Set W) hS) C inc :=
    inc.isEHNHomomorphismEmbedding.toOriginalPartial
  refine ⟨W, C, hTree, inc, hPartial, ?_, ?_⟩
  · intro e
    obtain ⟨baseCopy, hContains⟩ :=
      (LooseTreeAmalgam.ofTree hTree).irreducible_contained_in_copy
        hA e
    refine ⟨e, ?_, ?_⟩
    · exact ⟨VB, Base, hBase, baseCopy, hContains⟩
    · intro a ha
      rfl
  · intro K _hK x y hxy
    have hEq : x = y := inc.injective hxy
    subst y
    exact Iff.rfl

end FunctionalAmbientACopyHistoryTreeLike

end StructuralRamsey.Structure


namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}}
variable {P U V : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The ACTUAL initial EHN Picture satisfies the genuine ambient
A-copy version of the strict original-partial projected-history
invariant at every rank, and retains all prescribed B placements.

The hypotheses are exactly irreducibility of A and B; no
hereditary irreducibility of A's closed substructures is needed.
The mixed Hales-Jewett step is a separate obligation. -/
theorem initial_ambientACopy_originalPartial_history
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (hA : A.Irreducible)
    (Base : Structure L V) [Finite V] [Finite P]
    (hBaseMem : K Base) (hBaseIrred : Base.Irreducible)
    (hpos : L.PositiveFuncArity)
    (beta0 : Structure.Embedding Base D)
    (n : ℕ) :
    ∃ T : Stage K D,
      Structure.FunctionalAmbientACopyHistoryTreeLike
        (A := A) (C := T.system.toStructure) (Base := Base)
        T.system.part n ∧
      ∀ beta : Structure.Embedding Base D,
        ∃ e : Structure.Embedding Base T.system.toStructure,
          ∀ x, T.system.part (e x) = beta x := by
  obtain ⟨T, hTree, hCopies⟩ :=
    initial_tree hK Base hBaseMem hBaseIrred hpos beta0
  have hHistory :
      Structure.FunctionalAmbientACopyHistoryTreeLike
        (A := A) (C := T.system.toStructure) (Base := Base)
        T.system.part n :=
    Structure.FunctionalAmbientACopyHistoryTreeLike.of_tree
      hA hBaseIrred hTree T.system.part n
  exact ⟨T, hHistory, hCopies⟩

end StructuralRamsey.FunctionalPartite.EHN
