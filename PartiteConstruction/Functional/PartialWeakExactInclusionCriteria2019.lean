import PartiteConstruction.Functional.PartialDomainGraphClosedRange2019
import PartiteConstruction.Functional.PartialWeakCompleteDomainGraphIff2019

/-!
# Track A: exact graph and full-functional inclusion criteria for weak cuts

Work on the LITERAL vertex subset S of a genuine Option(Set)-valued
structure A.  The partial weak restriction is the CLIPPED operation:
it keeps an originally defined-empty input defined, but deletes a
defined nonempty input when every output is lost.

The ordinary relational inclusion from the independent Dom_F/Graph_F
encoding of the clipped weak restriction into the ambient encoding
is induced exactly if no defined application loses all its outputs.
This criterion is strictly weaker than actual function-closedness:
a multivalued fibre can retain one output and lose another.

The SAME vertex inclusion is a FULL genuine partial-function embedding
exactly when S is function-closed.  In this case both the domain bit
and the entire function value sets are preserved, not merely positive
incidences.

These are exact carrier/map correspondences; no generators are added,
no weak test is replaced by an ambient closure hull, and no strict
functional mixed-root B-tree theorem is asserted. The results cover
nullary functions, repeated inputs and defined-empty applications.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- On an exact weak cut, no-lost-application is precisely sufficient
for the ordinary induced relational inclusion of BOTH domain and
output-incidence data. -/
def weakDomainGraphInclusion
    (A : PartialSetStructure L V) (S : Set V)
    (hNo : NoLostDefinedApplications A S) :
    RelStructure.Embedding
      (domainGraph (A.weakInduce S)) (domainGraph A) where
  toFun := Subtype.val
  injective := Subtype.val_injective
  map_rel_iff := by
    intro R xs
    change ((domainGraph A).induce S).rel R xs ↔
      (domainGraph (A.weakInduce S)).rel R xs
    exact ((clippedDomainGraph_agrees_iff_noLost A S).mpr hNo R xs).symm

/-- Exact iff for existence of the induced domain/output graph embedding
with the LITERAL weak inclusion map. Any unrelated injection is excluded
by the map equality. -/
theorem weakDomainGraphInclusion_iff_noLost
    (A : PartialSetStructure L V) (S : Set V) :
    (∃ g : RelStructure.Embedding
        (domainGraph (A.weakInduce S)) (domainGraph A),
      g.toFun = (Subtype.val : S → V)) ↔
      NoLostDefinedApplications A S := by
  constructor
  · rintro ⟨g, hg⟩
    apply (clippedDomainGraph_agrees_iff_noLost A S).mp
    intro R xs
    have h := g.map_rel_iff R xs
    rw [hg] at h
    exact h.symm
  · intro hNo
    exact ⟨weakDomainGraphInclusion A S hNo, rfl⟩

/-- Closedness permits the canonical weak-substructure inclusion to be a
FULL embedding of genuine partial set-valued structures: the weak and
ordinary closed-induced value sets literally coincide on every input. -/
def weakFullInclusion
    (A : PartialSetStructure L V) (S : Set V)
    (hClosed : A.IsClosed S) :
    Embedding (A.weakInduce S) A where
  toFun := Subtype.val
  injective := Subtype.val_injective
  map_rel_iff := by
    intro R xs
    rfl
  map_func := by
    intro F xs
    rw [weakInduce_closed_func A S hClosed F xs]
    exact (closedInclusion A S hClosed).map_func F xs

/-- Exact iff: the LITERAL weak inclusion is a full functional
embedding precisely when S contains EVERY target function output of
each application with inputs in S. No condition on the external
unrelated function applications is imposed. -/
theorem weakFullInclusion_iff_closed
    (A : PartialSetStructure L V) (S : Set V) :
    (∃ e : Embedding (A.weakInduce S) A,
      e.toFun = (Subtype.val : S → V)) ↔
      A.IsClosed S := by
  constructor
  · rintro ⟨e, he⟩
    have hClosed := e.range_isClosed
    have hRange : Set.range (Subtype.val : S → V) = S := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact x.2
      · intro hy
        exact ⟨⟨y, hy⟩, rfl⟩
    rw [he, hRange] at hClosed
    exact hClosed
  · intro hClosed
    exact ⟨weakFullInclusion A S hClosed, rfl⟩

/-- If no entire clipped application is lost but some multivalued
output escapes, the relational graph inclusion is induced, whereas
the identical vertex map cannot be a full functional embedding.
This is the general principle behind Track A's transversal example. -/
theorem weakGraphIncluded_notFull_of_noLost_notClosed
    (A : PartialSetStructure L V) (S : Set V)
    (hNo : NoLostDefinedApplications A S)
    (hNotClosed : ¬ A.IsClosed S) :
    (∃ g : RelStructure.Embedding
        (domainGraph (A.weakInduce S)) (domainGraph A),
      g.toFun = (Subtype.val : S → V)) ∧
      ¬ (∃ e : Embedding (A.weakInduce S) A,
          e.toFun = (Subtype.val : S → V)) := by
  constructor
  · exact (weakDomainGraphInclusion_iff_noLost A S).mpr hNo
  · intro he
    exact hNotClosed ((weakFullInclusion_iff_closed A S).mp he)

end StructuralRamsey.PartialSetStructure
