import PartiteConstruction.Functional.AmbientRelativeWeakTreeHistoryGlue
import PartiteConstruction.Functional.ExactWeakRootSingletonFactor

/-!
# Strict functional mixed weak-tree gluing from root-hit-safe histories

The complete conditional functional mixed-gluing theorem previously had an
apparently independent choice of a projection pG:Start→P, together with
label factorization assumptions on both relative side witnesses.

These can instead be DEDUCED from:
  1. finite histories containing every projected singleton;
  2. both side maps factoring through one possibly NONINJECTIVE map q
     on the exact common weak source root;
  3. ROOT-HIT SAFETY: any side vertex whose image happens to land in
     the distinguished target Start is an actual weak-root vertex, with
     the corresponding q-coordinate.

Singleton histories alone guarantee projected labels on q[root] but
cannot constrain other side vertices hitting the target root. Thus the
third hypothesis is not silently omitted. This isolates the exact
additional relative extension property which the genuine maximal
mixed Hales-Jewett Picture construction must establish.

The result retains full set-valued function languages, a genuine
strict functional B-tree target, all ambient A-copy intersections,
arbitrary projected histories, and exact weak source vertex sets.
There are NO generated closure hulls, and the function-output
transversality axiom remains available in every actual partite stage.

This theorem is a CONDITIONAL refinement, not an assertion that
root-hit-safe side extensions exist for all native HJ stages.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {VA H E F C VB G WL WR P : Type v}

/-- If both strict relative weak side witnesses have root-hit safety,
then the standard finite singleton projected diary automatically
constructs the shared root-labelling pG. Consequently the complete
strict functional weak-tree/history gluing theorem needs no
separately supplied pG or factorization assumptions.

The only nontrivial remaining hypothesis is the EXISTENCE of these
coherent, root-hit-safe strict side extensions for each actual
maximal-rank mixed Hales-Jewett Picture test. -/
theorem ambientRelativeWeakTreeHistory_glue_isolatedRootHits
    [Fintype P] [Nonempty P]
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
      (iL ⁻¹' S) fL (history ++ singletonProjectedHistory P))
    (hHistR : SetRespectsProjectedHistory pR
      (iR ⁻¹' S) fR (history ++ singletonProjectedHistory P))
    (hHitL : ∀ (a : iL ⁻¹' S) (g : G),
      fL a = hExtL.startEmbedding g →
      ∃ d : ((iL.comp sL) ⁻¹' S),
        a.1 = sL d.1 ∧ q d = g)
    (hHitR : ∀ (b : iR ⁻¹' S) (g : G),
      fR b = hExtR.startEmbedding g →
      ∃ d : ((iL.comp sL) ⁻¹' S),
        b.1 = sR d.1 ∧ q d = g) :
    SetAmbientRelativeWeakTreeWitness
      A Base Whole pWhole S history := by
  classical
  let RootSet : Set H := (iL.comp sL) ⁻¹' S
  let rootL : RootSet → (iL ⁻¹' S) :=
    fun d => ⟨sL d.1, d.2⟩
  have hRootEq : ∀ d : RootSet,
      fL (rootL d) = hExtL.startEmbedding (q d) := by
    intro d
    exact hRootL d.1 d.2
  obtain ⟨pG, hFactorRoot⟩ :=
    hHistL.factors_through_weakRoot_of_singletons
      rootL q hExtL.startEmbedding hRootEq
  have hFactorL : ∀ (a : iL ⁻¹' S) (g : G),
      fL a = hExtL.startEmbedding g → pL a.1 = pG g := by
    intro a g ha
    obtain ⟨d, hda, hdg⟩ := hHitL a g ha
    calc
      pL a.1 = pL (sL d.1) := congrArg pL hda
      _ = pG (q d) := hFactorRoot d
      _ = pG g := congrArg pG hdg
  have hFactorR : ∀ (b : iR ⁻¹' S) (g : G),
      fR b = hExtR.startEmbedding g → pR b.1 = pG g := by
    intro b g hb
    obtain ⟨d, hdb, hdg⟩ := hHitR b g hb
    have hOverlap : iL (sL d.1) = iR (sR d.1) :=
      (hSrc.overlap (sL d.1) (sR d.1)).mpr
        ⟨d.1, rfl, rfl⟩
    have hProj : pR (sR d.1) = pL (sL d.1) := by
      calc
        pR (sR d.1) = pWhole (iR (sR d.1)) :=
          (hpR (sR d.1)).symm
        _ = pWhole (iL (sL d.1)) :=
          congrArg pWhole hOverlap.symm
        _ = pL (sL d.1) := hpL (sL d.1)
    calc
      pR b.1 = pR (sR d.1) := congrArg pR hdb
      _ = pL (sL d.1) := hProj
      _ = pG (q d) := hFactorRoot d
      _ = pG g := congrArg pG hdg
  have hHistL' : SetRespectsProjectedHistory pL
      (iL ⁻¹' S) fL history := by
    intro K hK a b hab
    exact hHistL K (List.mem_append.mpr (Or.inl hK)) a b hab
  have hHistR' : SetRespectsProjectedHistory pR
      (iR ⁻¹' S) fR history := by
    intro K hK a b hab
    exact hHistR K (List.mem_append.mpr (Or.inl hK)) a b hab
  exact hSrc.ambientRelativeWeakTreeHistory_glue_sharedRoot
    hA S pWhole pL pR hpL hpR Base Start hStart q
    TL TR hExtL hExtR fL fR hL hR
    hRootL hRootR hCopiesL hCopiesR
    history hHistL' hHistR' pG hFactorL hFactorR

end StructuralRamsey.Structure.IsFreeAmalgam
