import PartiteConstruction.Functional.ProjectedHistoryTreeCompletion
import PartiteConstruction.Functional.ControlCompletion

/-! # Combined projected/source histories for functional local tree completion

The relational sparsening proof only needs histories of subsets of the ambient
part structure D.  For set-valued functions this is not sufficient when two
source vertices occupy the same part: fibre-surjectivity in a mixed free
amalgam also needs to know that points outside the actual source overlap are
not identified with points inside it.

Accordingly the functional diary carries two finite histories:
* projected subsets of D, for the existing partite bookkeeping;
* actual subsets of the current source C, for root isolation.

The final local tree-completion statement forgets both histories.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U P W V : Type v}
variable {A : Structure L U} {D : Structure L P}
variable {C : Structure L W} {Base : Structure L V}

/-- Functional projected-history invariant strengthened by arbitrary finite
source-side history. -/
def FunctionalHistoryTreeLike
    (p : W → P) (n : ℕ) : Prop :=
  ∀ (S : Finset W) (hS : C.IsClosed (↑S : Set W)),
    (C.induce (↑S : Set W) hS).GeneratedByAtMost n →
    ∀ (projectedHistory : List (Set P))
      (sourceHistory : List (Set W)),
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding Target f ∧
        FunctionalProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f ∧
        FunctionalRespectsProjectedHistory
          p S f projectedHistory ∧
        FunctionalRespectsSourceHistory
          S f sourceHistory

namespace FunctionalHistoryTreeLike

variable {p : W → P} {m n : ℕ}

/-- Forget source history. -/
theorem toProjectedHistory
    (h : FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n) :
    FunctionalProjectedHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n := by
  intro S hS hgen history
  obtain ⟨Z, T, hTree, f, hf, hPart, hProj, _⟩ :=
    h S hS hgen history []
  exact ⟨Z, T, hTree, f, hf, hPart, hProj⟩

/-- Forget all diary data. -/
theorem toLocallyClosedTreeCompletable
    (h : FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n) :
    LocallyClosedTreeCompletable Base C n :=
  h.toProjectedHistory.toLocallyClosedTreeCompletable

/-- Monotonicity in generator rank. -/
theorem mono
    (h : FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (hmn : m ≤ n) :
    FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p m := by
  intro S hS hgen hp hs
  exact h S hS (hgen.mono hmn) hp hs

/-- The combined history invariant pulls back along a full embedding.
Projected histories stay in the same ambient part structure; source histories
are transported by direct image under the embedding. -/
theorem pullback_embedding
    {X : Type v} {C' : Structure L X}
    (h : FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (e : Embedding C' C) :
    FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C') (Base := Base) (p ∘ e) n := by
  classical
  intro S hS hgen projectedHistory sourceHistory
  let I : Finset W := S.image e
  have hIclosed : C.IsClosed (↑I : Set W) := by
    have hset :
        (↑I : Set W) = imageSet e (↑S : Set X) := by
      ext y
      simp [I, imageSet]
    rw [hset]
    exact e.image_isClosed hS
  let incS : Embedding (C'.induce (↑S : Set X) hS) C' :=
    inclusion C' (↑S : Set X) hS
  let incI : Embedding (C.induce (↑I : Set W) hIclosed) C :=
    inclusion C (↑I : Set W) hIclosed
  let j : Embedding (C'.induce (↑S : Set X) hS) C :=
    e.comp incS
  have hrange :
      ∀ x : ↥(↑S : Set X),
        ∃ y : ↥(↑I : Set W), j x = incI y := by
    intro x
    let y : ↥(↑I : Set W) :=
      ⟨e x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
    exact ⟨y, rfl⟩
  let ee : Embedding
      (C'.induce (↑S : Set X) hS)
      (C.induce (↑I : Set W) hIclosed) :=
    j.factorThroughClosedRange incI hrange
  have hee (x : ↥(↑S : Set X)) :
      (ee x).1 = e x.1 := by
    have hx : j x = incI (ee x) := by
      change j x = incI (Classical.choose (hrange x))
      exact Classical.choose_spec (hrange x)
    exact hx.symm
  have heesurj : Function.Surjective ee := by
    intro y
    have hy : y.1 ∈ I := y.2
    rcases Finset.mem_image.mp hy with ⟨x, hxS, hxy⟩
    let xs : ↥(↑S : Set X) := ⟨x, hxS⟩
    refine ⟨xs, ?_⟩
    apply Subtype.ext
    calc
      (ee xs).1 = e x := hee xs
      _ = y.1 := hxy
  have hIgen :
      (C.induce (↑I : Set W) hIclosed).GeneratedByAtMost n :=
    hgen.of_surjective_embedding ee heesurj
  let sourceHistoryI : List (Set W) :=
    sourceHistory.map (fun H => e '' H)
  obtain ⟨Z, T, hTree, fI, hfI, hPartI, hProjI, hSrcI⟩ :=
    h I hIclosed hIgen projectedHistory sourceHistoryI
  let f : ↥(↑S : Set X) → Z := fI ∘ ee
  have hf :
      (C'.induce (↑S : Set X) hS).IsHomomorphismEmbedding T f := by
    exact hfI.comp ee.isHomomorphismEmbedding
  have hPart :
      FunctionalProjectedPartialIntersections
        (A := A) (D := D) (C := C') (T := T)
        (p ∘ e) S f := by
    intro β H hH a hproj hRange
    let aC : Embedding (A.induce H hH) C := e.comp a
    have hprojC : ∀ x, p (aC x) = β x.1 := by
      intro x
      exact hproj x
    have hRangeC : ∀ x, aC x ∈ I := by
      intro x
      exact Finset.mem_image.mpr ⟨a x, hRange x, rfl⟩
    obtain ⟨eHT, heHT, hcHT⟩ :=
      hPartI β H hH aC hprojC hRangeC
    refine ⟨eHT, ?_, hcHT⟩
    intro x
    change eHT x = fI (ee ⟨a x, hRange x⟩)
    have himage :
        (⟨aC x, hRangeC x⟩ : ↥(↑I : Set W)) =
          ee ⟨a x, hRange x⟩ := by
      apply Subtype.ext
      symm
      exact hee ⟨a x, hRange x⟩
    rw [← himage]
    exact heHT x
  have hProj :
      FunctionalRespectsProjectedHistory
        (p ∘ e) S f projectedHistory := by
    intro H hH x y hxy
    have hxyI : fI (ee x) = fI (ee y) := hxy
    have hmem := hProjI H hH (ee x) (ee y) hxyI
    simpa [Function.comp_apply, hee x, hee y] using hmem
  have hSrc :
      FunctionalRespectsSourceHistory S f sourceHistory := by
    intro H hH x y hxy
    have hHI : e '' H ∈ sourceHistoryI := by
      apply List.mem_map.mpr
      exact ⟨H, hH, rfl⟩
    have hxyI : fI (ee x) = fI (ee y) := hxy
    have hmem := hSrcI (e '' H) hHI (ee x) (ee y) hxyI
    have hx :
        (ee x).1 ∈ e '' H ↔ x.1 ∈ H := by
      rw [hee x]
      constructor
      · rintro ⟨z, hz, hez⟩
        have : z = x.1 := e.injective hez
        simpa [this] using hz
      · intro hxH
        exact ⟨x.1, hxH, rfl⟩
    have hy :
        (ee y).1 ∈ e '' H ↔ y.1 ∈ H := by
      rw [hee y]
      constructor
      · rintro ⟨z, hz, hez⟩
        have : z = y.1 := e.injective hez
        simpa [this] using hz
      · intro hyH
        exact ⟨y.1, hyH, rfl⟩
    exact hx.symm.trans (hmem.trans hy)
  exact ⟨Z, T, hTree, f, hf, hPart, hProj, hSrc⟩

/-- If the witness map is injective then it respects every source history. -/
theorem respectsSourceHistory_of_injective
    {Y : Type v} {S : Finset W}
    {f : ↥(↑S : Set W) → Y}
    (hf : Function.Injective f)
    (history : List (Set W)) :
    FunctionalRespectsSourceHistory S f history := by
  intro H _ x y hxy
  have hxy' : x = y := hf hxy
  subst y
  rfl

/-- If equality in the target already implies equality of source vertices,
both kinds of finite history are automatic. -/
theorem histories_of_injective
    {Y : Type v} {S : Finset W}
    {f : ↥(↑S : Set W) → Y}
    (hf : Function.Injective f)
    (projectedHistory : List (Set P))
    (sourceHistory : List (Set W)) :
    FunctionalRespectsProjectedHistory p S f projectedHistory ∧
      FunctionalRespectsSourceHistory S f sourceHistory := by
  constructor
  · intro H _ x y hxy
    have hxy' : x = y := hf hxy
    subst y
    rfl
  · exact respectsSourceHistory_of_injective hf sourceHistory

/-- Source history on the preimages of projected diary sets already implies
the projected-history condition.  This lets the mixed functional step carry
one source-side diary through the free-amalgam glue and recover the projected
diary afterwards. -/
theorem projectedHistory_of_sourcePreimages
    {Y : Type v} {S : Finset W}
    {f : ↥(↑S : Set W) → Y}
    (history : List (Set P))
    (hSrc :
      FunctionalRespectsSourceHistory S f
        (history.map (fun H => p ⁻¹' H))) :
    FunctionalRespectsProjectedHistory p S f history := by
  intro H hH x y hxy
  have hpre :
      p ⁻¹' H ∈ history.map (fun K => p ⁻¹' K) := by
    apply List.mem_map.mpr
    exact ⟨H, hH, rfl⟩
  simpa using hSrc (p ⁻¹' H) hpre x y hxy

/-- A synchronized functional-history witness can be completed to control
every ambient A-copy, without losing projected intersections or either diary.

The EHN projection supplies the projected full A-copy needed to turn the
projected-partial certificate into ordinary embedded-intersection data.
Control completion then only postcomposes the target, so all synchronized
certificates survive. -/
theorem witness_withControl
    [Finite U] [Finite W]
    (hA : A.Irreducible)
    (eAB : Embedding A Base)
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (h : FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    (hgen : (C.induce (↑S : Set W) hS).GeneratedByAtMost n)
    (projectedHistory : List (Set P))
    (sourceHistory : List (Set W)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding Target f ∧
        FunctionalProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f ∧
        FunctionalRespectsProjectedHistory p S f projectedHistory ∧
        FunctionalRespectsSourceHistory S f sourceHistory ∧
        (∀ α : Embedding A C,
          ∃ α' : Embedding A Target,
            ∀ a : U, ∀ ha : α a ∈ S,
              ∃ a' : U, f ⟨α a, ha⟩ = α' a') := by
  classical
  obtain ⟨Y, T, hTree, f, hf, hPart, hProj, hSrc⟩ :=
    h S hS hgen projectedHistory sourceHistory
  have hInt :
      FunctionalEmbeddedIntersections
        (A := A) (C := C) (T := T) S hS f :=
    hPart.toEmbeddedIntersections hA hp
  obtain ⟨Z, Target, hTree', j, hf', hctrl⟩ :=
    LocallyClosedTreeCompletable.completeControl_of_embeddedIntersections_with_embedding
      (A := A) (B := Base) (C := C)
      hA eAB S hS hTree f hf hInt
  let f' : ↥(↑S : Set W) → Z := j ∘ f
  have hPart' :
      FunctionalProjectedPartialIntersections
        (A := A) (D := D) (C := C) (T := Target) p S f' := by
    exact hPart.postcomp j
  have hProj' :
      FunctionalRespectsProjectedHistory p S f' projectedHistory := by
    exact hProj.postcomp j
  have hSrc' :
      FunctionalRespectsSourceHistory S f' sourceHistory := by
    exact hSrc.postcomp j
  exact ⟨Z, Target, hTree', f', hf', hPart', hProj', hSrc', hctrl⟩

end FunctionalHistoryTreeLike

namespace IsFreeAmalgam

variable {H E F C₀ G ZL ZR Z : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C₀}
variable {Gov : Structure L G}
variable {TL : Structure L ZL} {TR : Structure L ZR}
variable {Target : Structure L Z}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}
variable {tL : Embedding Gov TL} {tR : Embedding Gov TR}
variable {jL : Embedding TL Target} {jR : Embedding TR Target}

/-- Source-side diary predicates survive the compatible functional lift.

The only nontrivial case is equality between a point from the left side and a
point from the right side.  Root isolation places both points over source-root
vertices with the same target-root label; injectivity of the root labelling
then identifies those source-root vertices, so the two source points were
already equal in the free amalgam. -/
theorem functionalLiftMap_respectsSourceSets
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hTgt : IsFreeAmalgam tL tR jL jR)
    (q : H → G) (hq : Function.Injective q)
    (fL : E → ZL) (fR : F → ZR)
    (hcompatL : ∀ d, fL (sL d) = tL (q d))
    (hcompatR : ∀ d, fR (sR d) = tR (q d))
    (hrootL : RootIsolated sL tL q fL)
    (hrootR : RootIsolated sR tR q fR)
    (history : List (Set C₀))
    (hHistL :
      ∀ Hset ∈ history, ∀ x y : E,
        fL x = fL y → (iL x ∈ Hset ↔ iL y ∈ Hset))
    (hHistR :
      ∀ Hset ∈ history, ∀ x y : F,
        fR x = fR y → (iR x ∈ Hset ↔ iR y ∈ Hset)) :
    ∀ Hset ∈ history, ∀ x y : C₀,
      functionalLiftMap hSrc hTgt q fL fR hcompatL hcompatR x =
          functionalLiftMap hSrc hTgt q fL fR hcompatL hcompatR y →
        (x ∈ Hset ↔ y ∈ Hset) := by
  classical
  let lift :=
    functionalLiftMap hSrc hTgt q fL fR hcompatL hcompatR
  intro Hset hH x y hxy
  rcases hSrc.covers x with ⟨a, hxa⟩ | ⟨b, hxb⟩
  · rcases hSrc.covers y with ⟨a', hya⟩ | ⟨b, hyb⟩
    · have haa : fL a = fL a' := by
        apply jL.injective
        calc
          jL (fL a) = lift (iL a) :=
            (functionalLiftMap_left hSrc hTgt q fL fR
              hcompatL hcompatR a).symm
          _ = lift x := congrArg lift hxa.symm
          _ = lift y := hxy
          _ = lift (iL a') := congrArg lift hya
          _ = jL (fL a') :=
            functionalLiftMap_left hSrc hTgt q fL fR
              hcompatL hcompatR a'
      rw [hxa, hya]
      exact hHistL Hset hH a a' haa
    · have hcross : jL (fL a) = jR (fR b) := by
        calc
          jL (fL a) = lift (iL a) :=
            (functionalLiftMap_left hSrc hTgt q fL fR
              hcompatL hcompatR a).symm
          _ = lift x := congrArg lift hxa.symm
          _ = lift y := hxy
          _ = lift (iR b) := congrArg lift hyb
          _ = jR (fR b) :=
            functionalLiftMap_right hSrc hTgt q fL fR
              hcompatL hcompatR b
      obtain ⟨g, hLg, hRg⟩ := (hTgt.overlap (fL a) (fR b)).mp hcross
      obtain ⟨dL, ha, hqdL⟩ := hrootL a g hLg
      obtain ⟨dR, hb, hqdR⟩ := hrootR b g hRg
      have hd : dL = dR := by
        apply hq
        exact hqdL.trans hqdR.symm
      have hab : iL a = iR b := by
        calc
          iL a = iL (sL dL) := congrArg iL ha
          _ = iL (sL dR) := congrArg (fun d => iL (sL d)) hd
          _ = iR (sR dR) :=
            (hSrc.overlap (sL dR) (sR dR)).mpr ⟨dR, rfl, rfl⟩
          _ = iR b := congrArg iR hb.symm
      rw [hxa, hyb, hab]
  · rcases hSrc.covers y with ⟨a, hya⟩ | ⟨b', hyb⟩
    · have hcross : jL (fL a) = jR (fR b) := by
        calc
          jL (fL a) = lift (iL a) :=
            (functionalLiftMap_left hSrc hTgt q fL fR
              hcompatL hcompatR a).symm
          _ = lift y := congrArg lift hya.symm
          _ = lift x := hxy.symm
          _ = lift (iR b) := congrArg lift hxb
          _ = jR (fR b) :=
            functionalLiftMap_right hSrc hTgt q fL fR
              hcompatL hcompatR b
      obtain ⟨g, hLg, hRg⟩ := (hTgt.overlap (fL a) (fR b)).mp hcross
      obtain ⟨dL, ha, hqdL⟩ := hrootL a g hLg
      obtain ⟨dR, hb, hqdR⟩ := hrootR b g hRg
      have hd : dL = dR := by
        apply hq
        exact hqdL.trans hqdR.symm
      have hab : iL a = iR b := by
        calc
          iL a = iL (sL dL) := congrArg iL ha
          _ = iL (sL dR) := congrArg (fun d => iL (sL d)) hd
          _ = iR (sR dR) :=
            (hSrc.overlap (sL dR) (sR dR)).mpr ⟨dR, rfl, rfl⟩
          _ = iR b := congrArg iR hb.symm
      rw [hxb, hya, ← hab]
    · have hbb : fR b = fR b' := by
        apply jR.injective
        calc
          jR (fR b) = lift (iR b) :=
            (functionalLiftMap_right hSrc hTgt q fL fR
              hcompatL hcompatR b).symm
          _ = lift x := congrArg lift hxb.symm
          _ = lift y := hxy
          _ = lift (iR b') := congrArg lift hyb
          _ = jR (fR b') :=
            functionalLiftMap_right hSrc hTgt q fL fR
              hcompatL hcompatR b'
      rw [hxb, hyb]
      exact hHistR Hset hH b b' hbb

end IsFreeAmalgam

namespace LocallyClosedTreeCompletable

variable {H E F C₀ G ZL ZR : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C₀}
variable {Gov : Structure L G}
variable {TL : Structure L ZL} {TR : Structure L ZR}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}
variable {tL : Embedding Gov TL} {tR : Embedding Gov TR}

/-- Glue two functional tree witnesses while preserving arbitrary finite
source-side diary predicates on the whole source free amalgam. -/
theorem glueIsolatedRoot_withSourceHistory
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hTreeL : TreeAmalgam Base ZL TL)
    (hTreeR : TreeAmalgam Base ZR TR)
    (hcL : tL.ContainedInIrreducible)
    (hcR : tR.ContainedInIrreducible)
    (q : H → G) (hq : Function.Injective q)
    (fL : E → ZL) (fR : F → ZR)
    (hcompatL : ∀ d, fL (sL d) = tL (q d))
    (hcompatR : ∀ d, fR (sR d) = tR (q d))
    (hfL : Left.IsHomomorphismEmbedding TL fL)
    (hfR : Right.IsHomomorphismEmbedding TR fR)
    (hrootL : IsFreeAmalgam.RootIsolated sL tL q fL)
    (hrootR : IsFreeAmalgam.RootIsolated sR tR q fR)
    (history : List (Set C₀))
    (hHistL :
      ∀ Hset ∈ history, ∀ x y : E,
        fL x = fL y → (iL x ∈ Hset ↔ iL y ∈ Hset))
    (hHistR :
      ∀ Hset ∈ history, ∀ x y : F,
        fR x = fR y → (iR x ∈ Hset ↔ iR y ∈ Hset)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : C₀ → Z,
        Whole.IsHomomorphismEmbedding Target f ∧
        ∀ Hset ∈ history, ∀ x y : C₀,
          f x = f y → (x ∈ Hset ↔ y ∈ Hset) := by
  classical
  let Target := FreeAmalgam.amalgam Gov TL TR tL tR
  let jL := FreeAmalgam.leftEmbedding Gov TL TR tL tR
  let jR := FreeAmalgam.rightEmbedding Gov TL TR tL tR
  have hTgt : IsFreeAmalgam tL tR jL jR :=
    FreeAmalgam.isFreeAmalgam Gov TL TR tL tR
  have hTree :
      TreeAmalgam Base
        (FreeAmalgam.Vertex Gov TL TR tL tR) Target :=
    FreeAmalgam.treeAmalgam Gov TL TR tL tR Base
      hTreeL hTreeR hcL hcR
  let f : C₀ → FreeAmalgam.Vertex Gov TL TR tL tR :=
    IsFreeAmalgam.functionalLiftMap hSrc hTgt q fL fR
      hcompatL hcompatR
  have hf : Whole.IsHomomorphismEmbedding Target f :=
    IsFreeAmalgam.functionalLiftMap_isHomomorphismEmbedding
      hSrc hTgt q fL fR hcompatL hcompatR
      hfL hfR hrootL hrootR
  have hHist :
      ∀ Hset ∈ history, ∀ x y : C₀,
        f x = f y → (x ∈ Hset ↔ y ∈ Hset) :=
    IsFreeAmalgam.functionalLiftMap_respectsSourceSets
      hSrc hTgt q hq fL fR hcompatL hcompatR
      hrootL hrootR history hHistL hHistR
  exact ⟨_, Target, hTree, f, hf, hHist⟩

end LocallyClosedTreeCompletable

end StructuralRamsey.Structure
