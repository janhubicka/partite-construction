import PartiteConstruction.Ramsey.ClosureEmbeddingRange

/-! # Closure-root correctness in relational free amalgams

The 2019 closure description has relational closure tuples with a
prescribed irreducible root (their initial coordinates). A free
amalgam of two U-closed structures can only contain relation tuples
inherited from one side; hence each closure tuple in the amalgam
automatically has a correctly embedded root.

The remaining, harder part of Lemma 2.23(2) is to show that there is
**exactly one** closure tuple above every embedded root, including
roots sitting on the common overlap. The previously checked
`Embedding.range_isUSubstructure` is precisely the extra ingredient
for that uniqueness proof.

All images in this module are vertex-exact, and weak EHN projection
images are not asserted to be U-closed.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {H E F C : Type v}
variable {Root : RelStructure L H}
variable {Left : RelStructure L E}
variable {Right : RelStructure L F}
variable {Whole : RelStructure L C}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- The first half of the U-closed free-amalgam lemma:
every closure relation tuple in a relational free amalgam has the
correct embedded irreducible root, assuming this holds in each side. -/
theorem IsFreeAmalgam.closureTuple_hasRoot
    (hFree : IsFreeAmalgam sL sR iL iR)
    (rule : ClosureRule L)
    (hLeft : rule.IsClosed Left)
    (hRight : rule.IsClosed Right)
    (t : Fin (L.arity rule.symbol) → C)
    (ht : Whole.rel rule.symbol t) :
    rule.RootMatches Whole t := by
  rcases (hFree.rel_iff rule.symbol t).mp ht with
      ⟨a,ha,hEq⟩ | ⟨b,hb,hEq⟩
  · obtain ⟨e,he⟩ := hLeft.1 a ha
    let eC : Embedding rule.root Whole := iL.comp e
    refine ⟨eC, ?_⟩
    intro j
    rw [hEq]
    exact congrArg iL (he j)
  · obtain ⟨e,he⟩ := hRight.1 b hb
    let eC : Embedding rule.root Whole := iR.comp e
    refine ⟨eC, ?_⟩
    intro j
    rw [hEq]
    exact congrArg iR (he j)

/-- Therefore a free amalgam of U-closed sides never contains a
closure relation on a non-root input tuple. The uniqueness/existence
half remains a distinct obligation for Lemma 2.23(2). -/
theorem IsFreeAmalgam.closureTuple_hasRoot_all
    {rules : ClosureDescription L}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hLeft : IsUClosed rules Left)
    (hRight : IsUClosed rules Right) :
    ∀ rule : ClosureRule L, rule ∈ rules →
      ∀ t : Fin (L.arity rule.symbol) → C,
        Whole.rel rule.symbol t → rule.RootMatches Whole t := by
  intro rule hrule t ht
  exact hFree.closureTuple_hasRoot rule
    (hLeft rule hrule) (hRight rule hrule) t ht

end StructuralRamsey.RelStructure
