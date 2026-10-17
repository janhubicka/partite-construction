import PartiteConstruction.Functional.ProtectedAMarkWeakPullback

/-!
# Exact restriction of strict functional weak-test witnesses

The source of the repaired Appendix A induction is an EXACT weak
vertex subset. A witness obtained on an auxiliary larger weak set J
may be restricted to an actual tested subset I⊆J, without changing
its target tree or requiring any function-closure hull.

The ambient-relative weak functional HE restricts because any
nonempty source fibre entirely contained in I was already entirely
contained in J. On the restricted fibre the image set is unchanged;
missing outputs are not falsely reflected. Every full ambient
irreducible piece, actual full A-copy intersection, and projected
history remains protected.

If the auxiliary target has a full protected A mark, the same mark
remains protected after restricting to I. This is important for the
budgeted-alpha completion: request a predecessor witness on
J=I∪alpha(A) only WHEN |J| fits the previous vertex bound; then
restrict back to I. Neither exact tested I nor the induction bound
is enlarged.

No singleton-valuedness, free gluing root or total-fibre projection
assumption is needed.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V VA P : Type v}

/-- Exact inclusion of weak carriers. -/
def weakSubsetMap (Small Large : Set U) (hSub : Small ⊆ Large) :
    Small → Large :=
  fun x => ⟨x.1, hSub x.2⟩

/-- An ambient-relative weak HE restricts to ANY exact weaker
vertex set, preserving nonempty complete output fibres and all
ambient full irreducible tests. -/
theorem IsAmbientRelativeWeakHE.restrict_subset
    {C : Structure L U} {Target : Structure L V}
    {Large : Set U} {f : Large → V}
    (h : IsAmbientRelativeWeakHE C Large Target f)
    (Small : Set U) (hSub : Small ⊆ Large) :
    IsAmbientRelativeWeakHE C Small Target
      (f ∘ weakSubsetMap Small Large hSub) := by
  let j : Small → Large := weakSubsetMap Small Large hSub
  let g : Small → V := f ∘ j
  change IsAmbientRelativeWeakHE C Small Target g
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro R xs hx
    have hxBig : (C.weakInduce Large).rel R (j ∘ xs) := hx
    exact h.1.1.1 R (j ∘ xs) hxBig
  · intro F xs y hy
    have hyBig :
        j y ∈ (C.weakInduce Large).func F (j ∘ xs) := hy
    exact h.1.1.2 F (j ∘ xs) (j y) hyBig
  · intro F xs hNonempty hAll
    let xb : Fin (L.funcArity F) → Large := j ∘ xs
    have hNonBig :
        (C.func F (Subtype.val ∘ xb)).Nonempty := hNonempty
    have hAllBig :
        ∀ y, y ∈ C.func F (Subtype.val ∘ xb) → y ∈ Large := by
      intro y hy
      exact hSub (hAll y hy)
    have hBig := h.1.2 F xb hNonBig hAllBig
    change imageSet g ((C.weakInduce Small).func F xs) =
      Target.func F (f ∘ xb)
    calc
      imageSet g ((C.weakInduce Small).func F xs) =
          imageSet f ((C.weakInduce Large).func F xb) := by
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨j y, hy, rfl⟩
        · rintro ⟨y, hy, rfl⟩
          have hSmall : y.1 ∈ Small := hAll y.1 hy
          exact ⟨⟨y.1, hSmall⟩, hy, rfl⟩
      _ = Target.func F (f ∘ xb) := hBig
  · intro X E hE e he
    have heLarge : ∀ x, e x ∈ Large := fun x => hSub (he x)
    obtain ⟨eT, heT⟩ := h.2 E hE e heLarge
    refine ⟨eT, ?_⟩
    intro x
    exact heT x

/-- Every certificate for a full ambient A-copy on a weak test
persists on each exact subset, with the same target A-copy. -/
theorem SetAmbientACopyIntersections.restrict_subset
    {A : Structure L VA} {C : Structure L U}
    {Target : Structure L V} {Large : Set U}
    {f : Large → V}
    (h : SetAmbientACopyIntersections A C Target Large f)
    (Small : Set U) (hSub : Small ⊆ Large) :
    SetAmbientACopyIntersections A C Target Small
      (f ∘ weakSubsetMap Small Large hSub) := by
  intro e
  obtain ⟨eT, hContained, hAgree⟩ := h e
  refine ⟨eT, hContained, ?_⟩
  intro a ha
  exact hAgree a (hSub ha)

/-- Arbitrary projected histories persist under exact weak-test
restriction (the target map itself is unchanged). -/
theorem SetRespectsProjectedHistory.restrict_subset
    {Large : Set U}
    {f : Large → V} {part : U → P}
    {history : List (Set P)}
    (h : SetRespectsProjectedHistory part Large f history)
    (Small : Set U) (hSub : Small ⊆ Large) :
    SetRespectsProjectedHistory part Small
      (f ∘ weakSubsetMap Small Large hSub) history := by
  intro K hK x y hxy
  exact h K hK
    (weakSubsetMap Small Large hSub x)
    (weakSubsetMap Small Large hSub y) hxy

/-- The complete genuine STRICT functional B-tree weak witness
restricts from an auxiliary weak test J to its literal subset I,
without replacing I by a function closure. -/
theorem SetAmbientRelativeWeakTreeWitness.restrict_subset
    {A : Structure L VA} {Base : Structure L V}
    {C : Structure L U} {part : U → P}
    {Large : Set U} {history : List (Set P)}
    (h : SetAmbientRelativeWeakTreeWitness
      A Base C part Large history)
    (Small : Set U) (hSub : Small ⊆ Large) :
    SetAmbientRelativeWeakTreeWitness
      A Base C part Small history := by
  obtain ⟨Z, Target, hTree, f, hWeak, hCopies, hHist⟩ := h
  exact ⟨Z, Target, hTree,
    f ∘ weakSubsetMap Small Large hSub,
    hWeak.restrict_subset Small hSub,
    hCopies.restrict_subset Small hSub,
    hHist.restrict_subset Small hSub⟩

/-- A complete protected mark remains exact after shrinking the
WEAK source carrier, including originally unoccupied control parts. -/
theorem ProtectedAMark.restrict_subset
    {A : Structure L VA} {D : Structure L P}
    {Target : Structure L V}
    {part : U → P} {Large : Set U} {f : Large → V}
    {mark : Embedding A Target} {alpha : Embedding A D}
    (h : ProtectedAMark alpha part Large f mark)
    (Small : Set U) (hSub : Small ⊆ Large) :
    ProtectedAMark alpha part Small
      (f ∘ weakSubsetMap Small Large hSub) mark := by
  intro x a
  exact h (weakSubsetMap Small Large hSub x) a

/-- Exact restriction of a protected-mark witness. The quantification
over arbitrary weak subsets is still false as a uniform rank invariant;
this is a sound relative lemma only. -/
theorem SetAmbientProtectedWeakTreeWitness.restrict_subset
    {A : Structure L VA} {Base : Structure L V}
    {D : Structure L P} {alpha : Embedding A D}
    {C : Structure L U} {part : U → P}
    {Large : Set U} {history : List (Set P)}
    (h : SetAmbientProtectedWeakTreeWitness
      A Base alpha C part Large history)
    (Small : Set U) (hSub : Small ⊆ Large) :
    SetAmbientProtectedWeakTreeWitness
      A Base alpha C part Small history := by
  obtain ⟨Z, Target, hTree, f, hWeak, hCopies,
    hHist, mark, hContained, hTrace⟩ := h
  exact ⟨Z, Target, hTree,
    f ∘ weakSubsetMap Small Large hSub,
    hWeak.restrict_subset Small hSub,
    hCopies.restrict_subset Small hSub,
    hHist.restrict_subset Small hSub,
    mark, hContained, hTrace.restrict_subset Small hSub⟩

end StructuralRamsey.Structure
