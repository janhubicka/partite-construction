import PartiteConstruction.Functional.FreeAmalgamPullback

/-!
# A copied support remains inside the original core in every closed test

Suppose a full functional free amalgam attaches one old copy along a
full-functional support whose image in the current core factors through
a distinguished, function-closed original Hales--Jewett power core.

The closed-test pullback has a genuine full-function-language common
separator. Its map into the tested left side factors, canonically, through
the intersection of that tested left side with the original core.

Importantly, this intersection is itself CLOSED (the inverse image of
the range of a full embedding), so all maps here are genuine full
functional embeddings. No weak-test closure enlargement, relational
surrogate, U-closed structure or root isolation is used.

This establishes the actual closed-test geometric anchor factorization
needed to apply the fixed-root star-attachment theorem. The completion
of this anchored tested left side and the old-copy relative witness
remain logically separate obligations.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v

variable {L : Language.{u}}
variable {H E F C U J : Type v}
variable {Dsrc : Structure L H}
variable {Esrc : Structure L E}
variable {Fsrc : Structure L F}
variable {Csrc : Structure L C}
variable {TestSrc : Structure L U}
variable {sE : Embedding Dsrc Esrc}
variable {sF : Embedding Dsrc Fsrc}
variable {iE : Embedding Esrc Csrc}
variable {iF : Embedding Fsrc Csrc}

/-- Pull back a distinguished closed anchor of the LEFT side to the
actual closed test, whenever the source support of the new copied side
factors fully through that anchor.

The resulting `TestAnchor` is exactly the intersection of the tested
left side and the old distinguished core. It is a genuine functional
closed substructure. The common separator embeds into it and the
composite to the tested left side is the actual `pb.toLeft` map.

Neither the root nor its canonical original-partial projection must be
irreducible or injective under that projection. -/
theorem EmbeddingPullback.common_factors_through_closed_anchor
    (hfree : IsFreeAmalgam sE sF iE iF)
    (e : Embedding TestSrc Csrc)
    (pb : EmbeddingPullback hfree e)
    (Anchor : Structure L J)
    (j : Embedding Anchor Esrc)
    (a : Embedding Dsrc Anchor)
    (hSupport : ∀ d : H, sE d = j (a d)) :
    ∃ (S : Set pb.Left) (hS : pb.left.IsClosed S)
      (rootInAnchor : Embedding pb.common (pb.left.induce S hS)),
      ∀ x : pb.Common,
        (inclusion pb.left S hS) (rootInAnchor x) = pb.toLeft x := by
  classical
  let S : Set pb.Left := {x | pb.leftMap x ∈ Set.range j}
  have hS : pb.left.IsClosed S :=
    pb.leftMap.preimage_isClosed (Set.range j) j.range_isClosed
  let inc : Embedding (pb.left.induce S hS) pb.left :=
    inclusion pb.left S hS
  have hRange : ∀ x : pb.Common,
      ∃ z : S, pb.toLeft x = inc z := by
    intro x
    refine ⟨⟨pb.toLeft x, ?_⟩, rfl⟩
    change pb.leftMap (pb.toLeft x) ∈ Set.range j
    rw [pb.common_left x, hSupport (pb.commonMap x)]
    exact ⟨a (pb.commonMap x), rfl⟩
  let r : Embedding pb.common (pb.left.induce S hS) :=
    pb.toLeft.factorThroughRange inc hRange
  refine ⟨S, hS, r, ?_⟩
  intro x
  exact (Classical.choose_spec (hRange x)).symm

end StructuralRamsey.Structure.IsFreeAmalgam
