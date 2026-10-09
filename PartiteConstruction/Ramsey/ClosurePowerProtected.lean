import PartiteConstruction.Ramsey.ClosureHomomorphicImageHull
import PartiteConstruction.Ramsey.ClosureProtectedPictureStep

/-! # Protection of every positive native coordinate power

At each coordinate, close the image of the ENTIRE closed U-irreducible
test. ClosureHomomorphicImageHull proves this hull is U-irreducible by
pulling back target free decompositions. The old protected part map
embeds the hull. This gives coordinatewise injectivity and reflection,
which together give the required embedding into the part structure.

There is no ordinary irreducible generating-seed hypothesis and no
finiteness assumption. This concerns the explicit closed-test convention;
it does not identify that convention with published Definition 2.15.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure
universe u v
variable {L : RelLanguage.{u}} {P V E : Type v} {N : ℕ}

/-- The part map of a positive native induced power embeds every
closed U-irreducible test, including those without an irreducible seed. -/
theorem part_embedding_on_closed_uIrreducible_test
    {rules : ClosureDescription L} {A : RelStructure L P}
    (B : System L P V)
    (hBClosed : IsUClosed rules B.toRelStructure)
    (hBPart : IsClosedUHomomorphismEmbedding rules
      B.toRelStructure A B.part)
    (hN : 0 < N)
    (Test : RelStructure L E)
    (hTestClosed : IsUClosed rules Test)
    (hTestIrred : IsUIrreducible rules Test)
    (e : RelStructure.Embedding Test (power B N).toRelStructure) :
    ∃ d : RelStructure.Embedding Test A,
      ∀ x, d x = (power B N).part (e x) := by
  classical
  let Pwr := power B N
  have hPartOrdinary : B.IsPartiteOver A :=
    StructuralRamsey.RelStructure.IsClosedUHomomorphismEmbedding.toHomomorphismEmbedding_of_closed
      hBPart hBClosed
  have hPerCoord (k : Fin N) :
      (∀ x y : E, Pwr.part (e x) = Pwr.part (e y) →
        (e x).coord k = (e y).coord k) ∧
      (∀ (R : L.Symbol) (z : Fin (L.arity R) → E),
        A.rel R (fun j => Pwr.part (e (z j))) →
        B.rel R (fun j => (e (z j)).coord k)) := by
    let f : E → V := fun x => (e x).coord k
    have hf : Test.IsHomomorphism B.toRelStructure f := by
      intro R z hz
      exact ((e.map_rel_iff R z).mpr hz) k
    let H : Set V := UClosureHull rules B.toRelStructure (Set.range f)
    have hHClosed : IsUClosed rules (B.toRelStructure.induce H) :=
      hBClosed.induce_UClosureHull (Set.range f)
    have hHIrred : IsUIrreducible rules (B.toRelStructure.induce H) :=
      hTestClosed.homomorphic_image_hull_isUIrreducible hTestIrred hBClosed hf
    obtain ⟨dH, hdH⟩ := hBPart.on_test
      (B.toRelStructure.induce H) hHClosed hHIrred
      (inclusion B.toRelStructure H)
    have hIn (x : E) : f x ∈ H :=
      subset_UClosureHull rules B.toRelStructure (Set.range f) ⟨x, rfl⟩
    let dTest : E → H := fun x => ⟨f x, hIn x⟩
    have hPart (x : E) : dH (dTest x) = Pwr.part (e x) := by
      calc
        dH (dTest x) = B.part (f x) := hdH (dTest x)
        _ = Pwr.part (e x) := (e x).belongs k
    constructor
    · intro x y hxy
      have hd : dH (dTest x) = dH (dTest y) :=
        (hPart x).trans (hxy.trans (hPart y).symm)
      exact congrArg Subtype.val (dH.injective hd)
    · intro R z hA
      have hAT : A.rel R (dH ∘ (dTest ∘ z)) := by
        convert hA using 1
        funext j
        exact hPart (z j)
      exact (dH.map_rel_iff R (dTest ∘ z)).mp hAT
  let d : RelStructure.Embedding Test A := {
    toFun := fun x => Pwr.part (e x)
    injective := by
      intro x y hxy
      apply e.injective
      apply NonInduced.Vertex.ext B
      · exact hxy
      · intro k
        exact (hPerCoord k).1 x y hxy
    map_rel_iff := by
      intro R z
      constructor
      · intro hA
        have hp : Pwr.rel R (e ∘ z) := by
          intro k
          exact (hPerCoord k).2 R z hA
        exact (e.map_rel_iff R z).mp hp
      · intro hT
        have hp : Pwr.rel R (e ∘ z) :=
          (e.map_rel_iff R z).mpr hT
        exact (power_projection_homomorphism hPartOrdinary hN)
          R (e ∘ z) hp
  }
  exact ⟨d, fun _ => rfl⟩

/-- Unconditional preservation of closed-test protection by every
positive native coordinate power of a closed protected system. -/
theorem power_part_protected
    {rules : ClosureDescription L} {A : RelStructure L P}
    (B : System L P V)
    (hBClosed : IsUClosed rules B.toRelStructure)
    (hBPart : IsClosedUHomomorphismEmbedding rules
      B.toRelStructure A B.part)
    (hN : 0 < N) :
    IsClosedUHomomorphismEmbedding rules
      (power B N).toRelStructure A (power B N).part := by
  constructor
  · have hOrd : B.IsPartiteOver A :=
      StructuralRamsey.RelStructure.IsClosedUHomomorphismEmbedding.toHomomorphismEmbedding_of_closed
        hBPart hBClosed
    exact power_projection_homomorphism hOrd hN
  · intro X Test hClosed hIrred e
    exact part_embedding_on_closed_uIrreducible_test
      B hBClosed hBPart hN Test hClosed hIrred e

end StructuralRamsey.Partite.Induced
