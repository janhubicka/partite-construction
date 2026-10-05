import PartiteConstruction.Functional.HistoryTreeCompletion

/-! # Relative-labelled functional history witnesses

The hard mixed step for set-valued functions needs the two side completions to
realize the common closed A-boundary with the same A-labels.  The ordinary
combined history invariant already embeds every projected closed partial
A-copy into an irreducible piece of the target tree.  One fresh copy of the
base, attached over that embedded partial copy, upgrades this to a prescribed
relative labelling without changing any of the diary or projected-partial
data.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {U P W V : Type v}
variable {A : Structure L U} {D : Structure L P}
variable {C : Structure L W} {Base : Structure L V}

/-- Combined functional histories with one prescribed relative labelling of a
closed projected partial A-copy. -/
def FunctionalRelativeHistoryTreeLike
    (p : W → P) (n : ℕ) : Prop :=
  FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n ∧
  ∀ (S : Finset W) (hS : C.IsClosed (↑S : Set W)),
    (C.induce (↑S : Set W) hS).GeneratedByAtMost n →
    ∀ (projectedHistory : List (Set P))
      (sourceHistory : List (Set W))
      (β : Embedding A D) (H : Set U) (hH : A.IsClosed H)
      (e : Embedding (A.induce H hH) C)
      (hproj : ∀ x, p (e x) = β x.1)
      (hRange : ∀ x, e x ∈ S)
      (ell : Embedding (A.induce H hH) A),
      ∃ (Z : Type v) (Target : Structure L Z),
        TreeAmalgam Base Z Target ∧
        ∃ f : ↥(↑S : Set W) → Z,
          (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding Target f ∧
          FunctionalProjectedPartialIntersections
            (A := A) (D := D) (C := C) (T := Target) p S f ∧
          FunctionalRespectsProjectedHistory
            p S f projectedHistory ∧
          FunctionalRespectsSourceHistory
            S f sourceHistory ∧
          ∃ targetCopy : Embedding A Target,
            (∀ x : ↥H,
              f ⟨e x, hRange x⟩ = targetCopy (ell x)) ∧
            ∀ y : ↥(↑S : Set W), ∀ a : U,
              f y = targetCopy a →
                ∃ x : ↥H, y.1 = e x ∧ ell x = a

namespace FunctionalRelativeHistoryTreeLike

variable {p : W → P} {m n : ℕ}

/-- Forget the distinguished relative-labelling request. -/
theorem toHistory
    (h : FunctionalRelativeHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n) :
    FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n :=
  h.1

/-- Monotonicity in generator rank. -/
theorem mono
    (h : FunctionalRelativeHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (hmn : m ≤ n) :
    FunctionalRelativeHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p m := by
  refine ⟨h.1.mono hmn, ?_⟩
  intro S hS hgen projectedHistory sourceHistory β H hH e hproj hRange ell
  exact h.2 S hS (hgen.mono hmn) projectedHistory sourceHistory
    β H hH e hproj hRange ell

/-- Embed a requested closed boundary into the induced tested structure. -/
noncomputable def boundaryEmbedding
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    {H : Set U} (hH : A.IsClosed H)
    (e : Embedding (A.induce H hH) C)
    (hRange : ∀ x, e x ∈ S) :
    Embedding (A.induce H hH) (C.induce (↑S : Set W) hS) := by
  let inc : Embedding (C.induce (↑S : Set W) hS) C :=
    inclusion C (↑S : Set W) hS
  exact e.factorThroughClosedRange inc
    (fun x => ⟨⟨e x, hRange x⟩, rfl⟩)

/-- Pointwise equation for the induced-boundary factorization. -/
theorem boundaryEmbedding_val
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    {H : Set U} (hH : A.IsClosed H)
    (e : Embedding (A.induce H hH) C)
    (hRange : ∀ x, e x ∈ S) (x : ↥H) :
    (boundaryEmbedding (A := A) S hS hH e hRange x).1 = e x := by
  let inc : Embedding (C.induce (↑S : Set W) hS) C :=
    inclusion C (↑S : Set W) hS
  have hfac :=
    Embedding.factorThroughClosedRange_spec e inc
      (fun z => ⟨⟨e z, hRange z⟩, rfl⟩) x
  exact hfac


/-- The isolation clause carried by a relative witness is exactly the
root-isolation property for its boundary embedding and A-label map. -/
theorem rootIsolated_of_relativeWitness
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    {H : Set U} (hH : A.IsClosed H)
    (e : Embedding (A.induce H hH) C)
    (hRange : ∀ x, e x ∈ S)
    (ell : Embedding (A.induce H hH) A)
    {Z : Type v} {Target : Structure L Z}
    (f : ↥(↑S : Set W) → Z)
    (targetCopy : Embedding A Target)
    (hiso :
      ∀ y : ↥(↑S : Set W), ∀ a : U,
        f y = targetCopy a →
          ∃ x : ↥H, y.1 = e x ∧ ell x = a) :
    IsFreeAmalgam.RootIsolated
      (boundaryEmbedding (A := A) S hS hH e hRange)
      targetCopy ell f := by
  intro y a hya
  obtain ⟨x, hyx, hxa⟩ := hiso y a hya
  refine ⟨x, ?_, hxa⟩
  apply Subtype.ext
  calc
    y.1 = e x := hyx
    _ = (boundaryEmbedding (A := A) S hS hH e hRange x).1 :=
      (boundaryEmbedding_val (A := A) S hS hH e hRange x).symm

/-- Inclusion of a closed partial A-substructure gives the identity
relative-labelling request. -/
def identityLabelEmbedding
    (H : Set U) (hH : A.IsClosed H) :
    Embedding (A.induce H hH) A :=
  inclusion A H hH

/-- Specialize the relative request to identity A-labels. -/
theorem witness_identityLabels
    (h : FunctionalRelativeHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    (hgen : (C.induce (↑S : Set W) hS).GeneratedByAtMost n)
    (projectedHistory : List (Set P))
    (sourceHistory : List (Set W))
    (β : Embedding A D) (H : Set U) (hH : A.IsClosed H)
    (e : Embedding (A.induce H hH) C)
    (hproj : ∀ x, p (e x) = β x.1)
    (hRange : ∀ x, e x ∈ S) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding Target f ∧
        FunctionalProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f ∧
        FunctionalRespectsProjectedHistory
          p S f projectedHistory ∧
        FunctionalRespectsSourceHistory
          S f sourceHistory ∧
        ∃ targetCopy : Embedding A Target,
          (∀ x : ↥H,
            f ⟨e x, hRange x⟩ = targetCopy x.1) ∧
          ∀ y : ↥(↑S : Set W), ∀ a : U,
            f y = targetCopy a →
              ∃ x : ↥H, y.1 = e x ∧ x.1 = a := by
  obtain ⟨Z, Target, hTree, f, hf, hPart, hProj, hSrc,
    targetCopy, htarget, hiso⟩ :=
    h.2 S hS hgen projectedHistory sourceHistory
      β H hH e hproj hRange (identityLabelEmbedding (A := A) H hH)
  refine ⟨Z, Target, hTree, f, hf, hPart, hProj, hSrc,
    targetCopy, ?_, ?_⟩
  · intro x
    calc
      f ⟨e x, hRange x⟩ =
          targetCopy ((identityLabelEmbedding (A := A) H hH) x) :=
        htarget x
      _ = targetCopy x.1 := rfl
  · intro y a hya
    obtain ⟨x, hyx, hxa⟩ := hiso y a hya
    exact ⟨x, hyx, hxa⟩

/-- Presentation-free relative witness.  The distinguished boundary may be
any full substructure embedded in A; internally we pass to the closed range of
that embedding and use the literal-subtype relative witness. -/
theorem witness_embeddedLabels
    (h : FunctionalRelativeHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    (hgen : (C.induce (↑S : Set W) hS).GeneratedByAtMost n)
    (projectedHistory : List (Set P))
    (sourceHistory : List (Set W))
    {X : Type v} {R : Structure L X}
    (ell : Embedding R A) (β : Embedding A D)
    (e : Embedding R C)
    (hproj : ∀ x, p (e x) = β (ell x))
    (hRange : ∀ x, e x ∈ S) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding Target f ∧
        FunctionalProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f ∧
        FunctionalRespectsProjectedHistory
          p S f projectedHistory ∧
        FunctionalRespectsSourceHistory
          S f sourceHistory ∧
        ∃ targetCopy : Embedding A Target,
          (∀ x : X,
            f ⟨e x, hRange x⟩ = targetCopy (ell x)) ∧
          ∀ y : ↥(↑S : Set W), ∀ a : U,
            f y = targetCopy a →
              ∃ x : X, y.1 = e x ∧ ell x = a := by
  classical
  let H : Set U := Set.range ell
  have hH : A.IsClosed H := ell.range_isClosed
  let inc : Embedding (A.induce H hH) A :=
    inclusion A H hH
  have hToRange :
      ∀ x : X, ∃ z : H, ell x = inc z := by
    intro x
    exact ⟨⟨ell x, ⟨x, rfl⟩⟩, rfl⟩
  let toRange : Embedding R (A.induce H hH) :=
    ell.factorThroughClosedRange inc hToRange
  have hToRangeSpec (x : X) :
      inc (toRange x) = ell x :=
    Embedding.factorThroughClosedRange_spec ell inc hToRange x
  have hFromRange :
      ∀ z : H, ∃ x : X, inc z = ell x := by
    intro z
    rcases z.2 with ⟨x, hx⟩
    exact ⟨x, hx.symm⟩
  let fromRange : Embedding (A.induce H hH) R :=
    inc.factorThroughClosedRange ell hFromRange
  have hFromRangeSpec (z : H) :
      ell (fromRange z) = inc z :=
    Embedding.factorThroughClosedRange_spec inc ell hFromRange z
  have hInv (x : X) : fromRange (toRange x) = x := by
    apply ell.injective
    calc
      ell (fromRange (toRange x)) = inc (toRange x) :=
        hFromRangeSpec (toRange x)
      _ = ell x := hToRangeSpec x
  let eH : Embedding (A.induce H hH) C :=
    e.comp fromRange
  have hprojH : ∀ z, p (eH z) = β z.1 := by
    intro z
    calc
      p (eH z) = β (ell (fromRange z)) :=
        hproj (fromRange z)
      _ = β z.1 := by
        apply congrArg β
        exact hFromRangeSpec z
  have hRangeH : ∀ z, eH z ∈ S := by
    intro z
    exact hRange (fromRange z)
  obtain ⟨Z, Target, hTree, f, hf, hPart, hProj, hSrc,
    targetCopy, htarget, hiso⟩ :=
    h.witness_identityLabels
      S hS hgen projectedHistory sourceHistory
      β H hH eH hprojH hRangeH
  refine ⟨Z, Target, hTree, f, hf, hPart, hProj, hSrc,
    targetCopy, ?_, ?_⟩
  · intro x
    have hx := htarget (toRange x)
    calc
      f ⟨e x, hRange x⟩ =
          f ⟨eH (toRange x), hRangeH (toRange x)⟩ := by
        apply congrArg f
        apply Subtype.ext
        change e x = e (fromRange (toRange x))
        exact congrArg e (hInv x).symm
      _ = targetCopy (toRange x).1 := hx
      _ = targetCopy (ell x) := by
        apply congrArg targetCopy
        exact hToRangeSpec x
  · intro y a hya
    obtain ⟨z, hyz, hza⟩ := hiso y a hya
    let x : X := fromRange z
    refine ⟨x, ?_, ?_⟩
    · exact hyz
    · calc
        ell x = inc z := hFromRangeSpec z
        _ = z.1 := rfl
        _ = a := hza

/-- Whole-structure specialization of the presentation-free relative witness.
This is the side-witness interface used by mixed free-amalgam gluing. -/
theorem fullWitness_embeddedLabels
    [Fintype W]
    (h : FunctionalRelativeHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (hgen : C.GeneratedByAtMost n)
    (projectedHistory : List (Set P))
    (sourceHistory : List (Set W))
    {X : Type v} {R : Structure L X}
    (ell : Embedding R A) (β : Embedding A D)
    (e : Embedding R C)
    (hproj : ∀ x, p (e x) = β (ell x)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : W → Z,
        C.IsHomomorphismEmbedding Target f ∧
        FunctionalProjectedEmbeddedIntersections
          (A := A) (D := D) C p Target f ∧
        (∀ Hset ∈ projectedHistory, ∀ x y : W,
          f x = f y → (p x ∈ Hset ↔ p y ∈ Hset)) ∧
        (∀ Hset ∈ sourceHistory, ∀ x y : W,
          f x = f y → (x ∈ Hset ↔ y ∈ Hset)) ∧
        ∃ targetCopy : Embedding A Target,
          (∀ x : X, f (e x) = targetCopy (ell x)) ∧
          ∀ y : W, ∀ a : U,
            f y = targetCopy a →
              ∃ x : X, y = e x ∧ ell x = a := by
  classical
  let S : Finset W := Finset.univ
  have hS : C.IsClosed (↑S : Set W) := by
    intro F x _ y _
    simp [S]
  let Small := C.induce (↑S : Set W) hS
  let inc : Embedding Small C :=
    inclusion C (↑S : Set W) hS
  let allEmb : Embedding C Small :=
    (Embedding.id C).factorWithMap inc
      (fun x => ⟨x, Finset.mem_univ x⟩)
      (fun _ => rfl)
  have hsurj : Function.Surjective allEmb := by
    intro y
    refine ⟨y.1, ?_⟩
    apply Subtype.ext
    rfl
  have hgenSmall : Small.GeneratedByAtMost n :=
    hgen.of_surjective_embedding allEmb hsurj
  have hRange : ∀ x : X, e x ∈ S := by
    intro x
    exact Finset.mem_univ _
  obtain ⟨Z, Target, hTree, f0, hf0, hPart0, hProj0, hSrc0,
    targetCopy, htarget0, hiso0⟩ :=
    h.witness_embeddedLabels
      S hS hgenSmall projectedHistory sourceHistory
      ell β e hproj hRange
  let f : W → Z := f0 ∘ allEmb
  have hf : C.IsHomomorphismEmbedding Target f :=
    hf0.comp allEmb.isHomomorphismEmbedding
  have hPart :
      FunctionalProjectedEmbeddedIntersections
        (A := A) (D := D) C p Target f := by
    intro Q R0 ell0 β0 e0 hproj0
    have hRange0 : ∀ x, e0 x ∈ S := by
      intro x
      exact Finset.mem_univ _
    obtain ⟨eRT, heRT, hc⟩ :=
      hPart0.embeddedWitness β0 ell0 e0 hproj0 hRange0
    refine ⟨eRT, ?_, hc⟩
    intro x
    change eRT x = f0 (allEmb (e0 x))
    have hx := heRT x
    exact hx
  have hProj :
      ∀ Hset ∈ projectedHistory, ∀ x y : W,
        f x = f y → (p x ∈ Hset ↔ p y ∈ Hset) := by
    intro Hset hmem x y hxy
    exact hProj0 Hset hmem (allEmb x) (allEmb y) hxy
  have hSrc :
      ∀ Hset ∈ sourceHistory, ∀ x y : W,
        f x = f y → (x ∈ Hset ↔ y ∈ Hset) := by
    intro Hset hmem x y hxy
    have hs := hSrc0 Hset hmem (allEmb x) (allEmb y) hxy
    exact hs
  have htarget : ∀ x : X, f (e x) = targetCopy (ell x) := by
    intro x
    change f0 (allEmb (e x)) = targetCopy (ell x)
    exact htarget0 x
  have hiso :
      ∀ y : W, ∀ a : U,
        f y = targetCopy a →
          ∃ x : X, y = e x ∧ ell x = a := by
    intro y a hya
    obtain ⟨x, hyx, hxa⟩ :=
      hiso0 (allEmb y) a hya
    refine ⟨x, ?_, hxa⟩
    exact hyx
  exact ⟨Z, Target, hTree, f, hf, hPart, hProj, hSrc,
    targetCopy, htarget, hiso⟩

/-- The relative request is automatic from the ordinary combined history
invariant: attach one fresh copy of Base over the already embedded partial
A-boundary. -/
theorem ofHistory
    (hA : A.Irreducible)
    (eAB : Embedding A Base)
    (h : FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n) :
    FunctionalRelativeHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n := by
  classical
  refine ⟨h, ?_⟩
  intro S hS hgen projectedHistory sourceHistory
    β H hH e hproj hRange ell
  let Boundary : Set W := Set.range e
  obtain ⟨Y, T, hTree, f, hf, hPart, hProj, hSrcAll⟩ :=
    h S hS hgen projectedHistory (Boundary :: sourceHistory)
  have hSrc :
      FunctionalRespectsSourceHistory S f sourceHistory := by
    intro Hset hmem x y hxy
    exact hSrcAll Hset (by simp [hmem]) x y hxy
  obtain ⟨eHT, heHT, hcT⟩ :=
    hPart β H hH e hproj hRange
  let Hstr := A.induce H hH
  let eHB : Embedding Hstr Base :=
    eAB.comp ell
  have hcB : eHB.ContainedInIrreducible := by
    refine ⟨U, A, hA, eAB, ?_⟩
    intro x
    exact ⟨ell x, rfl⟩
  let T' := FreeAmalgam.amalgam Hstr T Base eHT eHB
  let l : Embedding T T' :=
    FreeAmalgam.leftEmbedding Hstr T Base eHT eHB
  let r : Embedding Base T' :=
    FreeAmalgam.rightEmbedding Hstr T Base eHT eHB
  have hfree : IsFreeAmalgam eHT eHB l r :=
    FreeAmalgam.isFreeAmalgam Hstr T Base eHT eHB
  have hTree' : TreeAmalgam Base _ T' :=
    FreeAmalgam.treeAmalgam Hstr T Base eHT eHB Base
      hTree
      (TreeAmalgam.copy (Embedding.id Base) (by
        intro b
        exact ⟨b, rfl⟩))
      hcT hcB
  let f' : ↥(↑S : Set W) → _ := l ∘ f
  have hf' :
      (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding T' f' :=
    l.isHomomorphismEmbedding.comp hf
  have hPart' :
      FunctionalProjectedPartialIntersections
        (A := A) (D := D) (C := C) (T := T') p S f' :=
    hPart.postcomp l
  have hProj' :
      FunctionalRespectsProjectedHistory p S f' projectedHistory :=
    hProj.postcomp l
  have hSrc' :
      FunctionalRespectsSourceHistory S f' sourceHistory :=
    hSrc.postcomp l
  let targetCopy : Embedding A T' := r.comp eAB
  refine ⟨_, T', hTree', f', hf', hPart', hProj', hSrc',
    targetCopy, ?_, ?_⟩
  · intro x
    change l (f ⟨e x, hRange x⟩) = r (eAB (ell x))
    calc
      l (f ⟨e x, hRange x⟩) = l (eHT x) :=
        congrArg l (heHT x).symm
      _ = r (eHB x) :=
        (hfree.overlap (eHT x) (eHB x)).mpr ⟨x, rfl, rfl⟩
      _ = r (eAB (ell x)) := rfl
  · intro y a hya
    have hcross : l (f y) = r (eAB a) := by
      exact hya
    obtain ⟨z, hfz, hbase⟩ :=
      (hfree.overlap (f y) (eAB a)).mp hcross
    have ha : ell z = a := by
      apply eAB.injective
      calc
        eAB (ell z) = eHB z := rfl
        _ = eAB a := hbase.symm
    let yz : ↥(↑S : Set W) := ⟨e z, hRange z⟩
    have hEq : f y = f yz := by
      calc
        f y = eHT z := hfz
        _ = f yz := heHT z
    have hzBoundary : yz.1 ∈ Boundary := by
      exact ⟨z, rfl⟩
    have hyBoundary : y.1 ∈ Boundary :=
      (hSrcAll Boundary (by simp) y yz hEq).2 hzBoundary
    rcases hyBoundary with ⟨z', hz'⟩
    have hzz : z' = z := by
      apply eHT.injective
      calc
        eHT z' = f ⟨e z', hRange z'⟩ := heHT z'
        _ = f y := by
          apply congrArg f
          apply Subtype.ext
          exact hz'
        _ = eHT z := hfz
    subst z'
    refine ⟨z, ?_, ha⟩
    exact hz'.symm

end FunctionalRelativeHistoryTreeLike

end StructuralRamsey.Structure
