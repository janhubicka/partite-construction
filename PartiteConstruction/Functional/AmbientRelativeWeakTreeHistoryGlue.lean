import PartiteConstruction.Functional.AmbientRelativeWeakTreeGlue
import PartiteConstruction.Functional.AmbientACopyIntersectionsGlue
import PartiteConstruction.Functional.WeakProjectedHistoryCrossKernelGlue

/-!
# The complete conditional strict functional weak-history mixed gluing step

This is the functional target-construction step of the published iterated
partite proof, on the EXACT weak source vertex set S. The source is a genuine
full FUNCTIONAL free amalgam, with potentially set-valued operations. Its
restricted source functions keep exactly the outputs in S and do not create
temporary multivalued/nonfunctional states.

From two relative side witnesses into genuine strict B-tree EXTENSIONS of the
SAME strict B-tree Start, where:
* both maps agree with the SAME (possibly noninjective) exact common-root q,
* both carry full ambient A-copy intersection certificates and projected
  history certificates, and
* a shared root-labelling pG factors each side's projected labels for ALL
  side points whose images land inside the target Start,

we merge the two target tree extensions, glue the ambient-relative weak HEs,
carry the genuine ambient A-copy certificates, and preserve projected
histories through a provably controlled cross-side target kernel.

This proves the ENTIRE conditional mixed-step constructor producing the
exact strict functional weak-tree/history witness used in the induction.

Crucially, it does NOT claim existence of such compatible side witnesses
in every maximal mixed Picture attachment. The remaining mathematical gap is
their construction, not the full-functional source gluing, transversality,
history transfer, cardinality, or strict target-tree merging.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {VA VC VL VR VZ P : Type v}

/-- Full target embeddings preserve the certificates for intersections
with every genuine full ambient A-copy of the tested source. -/
theorem SetAmbientACopyIntersections.postcomp_full
    {A : Structure L VA}
    {C : Structure L VC} {T : Structure L VL} {T' : Structure L VR}
    {S : Set VC} {f : S → VL}
    (h : SetAmbientACopyIntersections A C T S f)
    (j : Embedding T T') :
    SetAmbientACopyIntersections A C T' S (j ∘ f) := by
  intro e
  obtain ⟨eT, hContained, hAgree⟩ := h e
  refine ⟨j.comp eT, hContained.postcomp j, ?_⟩
  intro a ha
  change j (eT a) = j (f ⟨e a, ha⟩)
  exact congrArg j (hAgree a ha)

/-- Injective target maps also preserve arbitrary projected history diaries
without needing to reflect undefined function inputs. -/
theorem SetRespectsProjectedHistory.postcomp_full
    {C : Structure L VC} {T : Structure L VL} {T' : Structure L VR}
    {S : Set VC} {f : S → VL} {p : VC → P}
    {history : List (Set P)}
    (h : SetRespectsProjectedHistory p S f history)
    (j : Embedding T T') :
    SetRespectsProjectedHistory p S (j ∘ f) history := by
  intro K hK x y hEq
  exact h K hK x y (j.injective hEq)

end StructuralRamsey.Structure

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {VA H E F C VB G WL WR P : Type v}

/-- Full mixed witness transfer on EXACT weak functional vertex tests.

The two side completions must be relative to ONE shared strict functional
Base-tree Start. Their root comparison uses the same weak root map q, which
may identify root vertices. The root-labelling pG additionally ensures that
a *cross-side* target collision inside Start never identifies differing
projected parts. The side target maps may be noninjective globally.

Under these explicit compatibility assumptions the result contains ALL
parts of the genuine strict functional locally tree-like invariant:
  (i) strict full-functional Base-tree target,
  (ii) ambient-relative weak HE on the exact vertex set,
  (iii) full copies of A witnessing every actual ambient A-intersection,
  (iv) the requested arbitrary finite projected history diary.

This is conditional and cannot be substituted for the missing maximal-rank
mixed root EXTENSION EXISTENCE lemma. -/
theorem ambientRelativeWeakTreeHistory_glue_sharedRoot
    {A : Structure L VA}
    (hA : A.Irreducible)
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (S : Set C)
    (pWhole : C → P) (pL : E → P) (pR : F → P)
    (hpL : ∀ a, pWhole (iL a) = pL a)
    (hpR : ∀ b, pWhole (iR b) = pR b)
    (Base : Structure L VB)
    (Start : Structure L G)
    (hStart : TreeAmalgam Base G Start)
    (q : ((iL.comp sL) ⁻¹' S) → G)
    (TL : Structure L WL) (TR : Structure L WR)
    (hExtL : TreeExtension Base Start WL TL)
    (hExtR : TreeExtension Base Start WR TR)
    (fL : (iL ⁻¹' S) → WL)
    (fR : (iR ⁻¹' S) → WR)
    (hL : IsAmbientRelativeWeakHE Left (iL ⁻¹' S) TL fL)
    (hR : IsAmbientRelativeWeakHE Right (iR ⁻¹' S) TR fR)
    (hRootL : ∀ (d : H) (hdL : iL (sL d) ∈ S),
      fL ⟨sL d, hdL⟩ =
        hExtL.startEmbedding (q ⟨d, hdL⟩))
    (hRootR : ∀ (d : H)
      (hdL : iL (sL d) ∈ S) (hdR : iR (sR d) ∈ S),
      fR ⟨sR d, hdR⟩ =
        hExtR.startEmbedding (q ⟨d, hdL⟩))
    (hCopiesL : SetAmbientACopyIntersections A Left TL
      (iL ⁻¹' S) fL)
    (hCopiesR : SetAmbientACopyIntersections A Right TR
      (iR ⁻¹' S) fR)
    (history : List (Set P))
    (hHistL : SetRespectsProjectedHistory pL
      (iL ⁻¹' S) fL history)
    (hHistR : SetRespectsProjectedHistory pR
      (iR ⁻¹' S) fR history)
    (pG : G → P)
    (hFactorL : ∀ (a : iL ⁻¹' S) g,
      fL a = hExtL.startEmbedding g → pL a.1 = pG g)
    (hFactorR : ∀ (b : iR ⁻¹' S) g,
      fR b = hExtR.startEmbedding g → pR b.1 = pG g) :
    SetAmbientRelativeWeakTreeWitness A Base Whole pWhole S history := by
  classical
  obtain ⟨Z, Target, hAll, eL, eR, hTargetFree, hStartL, hStartR⟩ :=
    hExtL.mergeFree hExtR
  have hTree : TreeAmalgam Base Z Target :=
    hAll.toTree hStart
  have hWholeL : IsAmbientRelativeWeakHE
      Left (iL ⁻¹' S) Target (eL ∘ fL) :=
    hL.postcomp_full eL
  have hWholeR : IsAmbientRelativeWeakHE
      Right (iR ⁻¹' S) Target (eR ∘ fR) :=
    hR.postcomp_full eR
  have hAgree : ∀ (d : H)
      (hdL : iL (sL d) ∈ S) (hdR : iR (sR d) ∈ S),
      (eL ∘ fL) ⟨sL d, hdL⟩ =
        (eR ∘ fR) ⟨sR d, hdR⟩ := by
    intro d hdL hdR
    change eL (fL ⟨sL d, hdL⟩) =
      eR (fR ⟨sR d, hdR⟩)
    rw [hRootL d hdL, hRootR d hdL hdR]
    exact (hStartL (q ⟨d, hdL⟩)).trans
      (hStartR (q ⟨d, hdL⟩)).symm
  obtain ⟨f, hWeak, hfL, hfR⟩ :=
    hSrc.ambientRelativeWeakHE_glue S Target
      (eL ∘ fL) (eR ∘ fR) hWholeL hWholeR hAgree
  have hCopiesL' : SetAmbientACopyIntersections
      A Left Target (iL ⁻¹' S) (eL ∘ fL) :=
    hCopiesL.postcomp_full eL
  have hCopiesR' : SetAmbientACopyIntersections
      A Right Target (iR ⁻¹' S) (eR ∘ fR) :=
    hCopiesR.postcomp_full eR
  have hCopies : SetAmbientACopyIntersections
      A Whole Target S f :=
    hSrc.ambientACopyIntersections_glue
      hA S Target f (eL ∘ fL) (eR ∘ fR)
      hfL hfR hCopiesL' hCopiesR'
  have hHist : SetRespectsProjectedHistory pWhole S f history :=
    hSrc.setRespectsProjectedHistory_glue_targetRoot
      S pWhole pL pR hpL hpR hTargetFree
      f fL fR hfL hfR history hHistL hHistR
      pG hFactorL hFactorR
  exact ⟨Z, Target, hTree, f, hWeak, hCopies, hHist⟩

end StructuralRamsey.Structure.IsFreeAmalgam
