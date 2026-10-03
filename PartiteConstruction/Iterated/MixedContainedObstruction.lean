import PartiteConstruction.Iterated.LocalTreeLike

/-! # Straddling boundaries cannot lie in one irreducible target piece

A genuinely straddling embedded substructure of a free amalgam cannot have its
whole image contained in an irreducible substructure of the amalgam: every
irreducible substructure localizes to one side.

This is the precise obstruction behind the remaining mixed projected-history
step.  A reducible partial A-boundary that hits exclusive vertices on both
sides must be folded/completed into a single irreducible target piece; merely
embedding it into the target free amalgam can never provide the
`ContainedInIrreducible` certificate required by future compatible gluing.
-/
namespace StructuralRamsey.RelStructure.IsFreeAmalgam

universe u v
variable {L : RelLanguage.{u}}
variable {H E F C Q : Type v}
variable {D : RelStructure L H}
variable {A : RelStructure L E}
variable {B : RelStructure L F}
variable {Whole : RelStructure L C}
variable {R : RelStructure L Q}
variable {sA : Embedding D A} {sB : Embedding D B}
variable {iA : Embedding A Whole} {iB : Embedding B Whole}

/-- A point of the left side is exclusive when it is not in the image of the
right side. -/
def LeftExclusive (a : E) : Prop :=
  ∀ b : F, iA a ≠ iB b

/-- A point of the right side is exclusive when it is not in the image of the
left side. -/
def RightExclusive (b : F) : Prop :=
  ∀ a : E, iB b ≠ iA a

/-- An embedded substructure containing one exclusive point from each side
cannot be contained in any irreducible substructure of the free amalgam. -/
theorem not_containedInIrreducible_of_straddles
    (hfree : IsFreeAmalgam sA sB iA iB)
    (e : Embedding R Whole)
    (x y : Q) (a : E) (b : F)
    (hx : e x = iA a) (hy : e y = iB b)
    (ha : LeftExclusive (iA := iA) (iB := iB) a)
    (hb : RightExclusive (iA := iA) (iB := iB) b) :
    ¬ e.ContainedInIrreducible := by
  rintro ⟨S, hS, hRange⟩
  rcases hfree.irreducible_side S hS with hleft | hright
  · let ys : S := ⟨e y, hRange y⟩
    obtain ⟨a', ha'⟩ := hleft ys
    apply hb a'
    calc
      iB b = e y := hy.symm
      _ = iA a' := ha'
  · let xs : S := ⟨e x, hRange x⟩
    obtain ⟨b', hb'⟩ := hright xs
    apply ha b'
    calc
      iA a = e x := hx.symm
      _ = iB b' := hb'

/-- Equivalent pointwise form, avoiding explicit side witnesses in later
applications. -/
theorem not_containedInIrreducible_of_exclusive_images
    (hfree : IsFreeAmalgam sA sB iA iB)
    (e : Embedding R Whole)
    (x y : Q)
    (hxL : ∃ a : E, e x = iA a ∧ LeftExclusive (iA := iA) (iB := iB) a)
    (hyR : ∃ b : F, e y = iB b ∧ RightExclusive (iA := iA) (iB := iB) b) :
    ¬ e.ContainedInIrreducible := by
  obtain ⟨a, hxa, ha⟩ := hxL
  obtain ⟨b, hyb, hb⟩ := hyR
  exact not_containedInIrreducible_of_straddles
    hfree e x y a b hxa hyb ha hb

end StructuralRamsey.RelStructure.IsFreeAmalgam
