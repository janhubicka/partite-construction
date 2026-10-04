import PartiteConstruction.Functional.Induced
import PartiteConstruction.Functional.Homomorphism
import PartiteConstruction.Structure.IrreducibleHomImage

/-! # Full partite invariant for the functional Hales--Jewett power

The direct functional partite power already preserves the full projection
homomorphism.  For the EHN refinement we need the stronger statement that the
partition projection is a homomorphism-embedding.

For an irreducible substructure of the power, every coordinate projection is
a full homomorphism into the previous stage.  Its range is therefore an
irreducible homomorphic image.  The previous partite
homomorphism-embedding gives an induced embedding of that coordinate image
into the part structure.  These coordinate embeddings show that the common
part map is injective and reflects all relations on the irreducible source.
-/
namespace StructuralRamsey.FunctionalPartite.Induced

open Structure

universe u v
variable {L : Language.{u}} {P V : Type v}
variable {A : Structure L P} {B : System L P V}
variable {N : ℕ}

/-- Evaluation at one coordinate is a full homomorphism from the power back
to the copied system. -/
theorem coordinateHom
    (hB : B.ProjectionHom A)
    (i : Fin N) :
    (power B N).toStructure.IsHomomorphism B.toStructure
      (fun z => z.coord i) := by
  constructor
  · intro R z hz
    exact hz i
  · intro F x
    classical
    let args (j : Fin N) : Fin (L.funcArity F) → V :=
      fun k => (x k).coord j
    have hparts (j : Fin N) :
        B.part ∘ args j = (power B N).part ∘ x := by
      funext k
      exact (x k).belongs j
    ext b
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy i
    · intro hb
      have hbPart :
          B.part b ∈ A.func F ((power B N).part ∘ x) := by
        have himg :
            B.part b ∈
              Structure.imageSet B.part (B.func F (args i)) :=
          ⟨b, hb, rfl⟩
        rw [hB.2 F (args i)] at himg
        rwa [hparts i] at himg
      have hex : ∀ j : Fin N,
          ∃ c : V, c ∈ B.func F (args j) ∧ B.part c = B.part b := by
        intro j
        have hj :
            B.part b ∈ A.func F (B.part ∘ args j) := by
          rw [hparts j]
          exact hbPart
        rw [← hB.2 F (args j)] at hj
        rcases hj with ⟨c, hc, hpart⟩
        exact ⟨c, hc, hpart⟩
      choose c hc hpc using hex
      let coord : Fin N → V := fun j =>
        if hj : j = i then b else c j
      let y : Vertex B N := {
        part := B.part b
        coord := coord
        belongs := by
          intro j
          by_cases hj : j = i
          · subst j
            simp [coord]
          · simp [coord, hj, hpc j]
      }
      refine ⟨y, ?_, ?_⟩
      · intro j
        by_cases hj : j = i
        · subst j
          simp only [y, coord, dite_eq_left]
          convert hb using 1
        · simp only [y, coord, dite_eq_right hj]
          convert hc j using 1
      · simp [y, coord]

/-- The direct functional coordinate power preserves the full
homomorphism-embedding partite invariant. -/
theorem power_isPartiteOver
    (hB : B.IsPartiteOver A) (hN : 0 < N) :
    (power B N).IsPartiteOver A := by
  classical
  let C := power B N
  have hProj : C.ProjectionHom A :=
    power_projectionHom (FunctionalPartite.System.projectionHom hB) hN
  constructor
  · exact hProj
  · intro X E hE e
    let q (i : Fin N) : X → V :=
      fun x => (e x).coord i
    have hq (i : Fin N) :
        E.IsHomomorphism B.toStructure (q i) := by
      exact (coordinateHom (FunctionalPartite.System.projectionHom hB) i).comp e.isHomomorphism
    let S (i : Fin N) : Set V := Set.range (q i)
    have hSclosed (i : Fin N) :
        B.toStructure.IsClosed (S i) :=
      (hq i).range_isClosed
    have hSirr (i : Fin N) :
        (B.toStructure.induce (S i) (hSclosed i)).Irreducible := by
      exact hE.range_homomorphism (hq i)
    let incl (i : Fin N) :
        Structure.Embedding (B.toStructure.induce (S i) (hSclosed i))
          B.toStructure :=
      inclusion B.toStructure (S i) (hSclosed i)
    have hex (i : Fin N) :
        ∃ g : Structure.Embedding
            (B.toStructure.induce (S i) (hSclosed i)) A,
          ∀ z, g z = B.part z.1 := by
      exact hB.2
        (B.toStructure.induce (S i) (hSclosed i))
        (hSirr i) (incl i)
    choose g hg using hex
    let target : X → P := fun x => C.part (e x)
    have htarget_coord (i : Fin N) (x : X) :
        target x = B.part (q i x) := by
      exact (e x).belongs i
    have htargetHom : E.IsHomomorphism A target := by
      change E.IsHomomorphism A (C.part ∘ e)
      exact hProj.comp e.isHomomorphism
    let i0 : Fin N := ⟨0, hN⟩
    have hinj : Function.Injective target := by
      intro x y hxy
      apply e.injective
      apply Vertex.ext B
      · exact hxy
      · intro i
        let sx : S i := ⟨q i x, ⟨x, rfl⟩⟩
        let sy : S i := ⟨q i y, ⟨y, rfl⟩⟩
        have hgi : g i sx = g i sy := by
          rw [hg i sx, hg i sy]
          exact (htarget_coord i x).symm.trans
            (hxy.trans (htarget_coord i y))
        have hs : sx = sy := (g i).injective hgi
        exact congrArg Subtype.val hs
    let ge : Structure.Embedding E A := {
      toFun := target
      injective := hinj
      map_rel_iff := by
        intro R z
        constructor
        · intro hArel
          have hcoords :
              ∀ i : Fin N,
                B.rel R (fun k => (e (z k)).coord i) := by
            intro i
            let zs : Fin (L.relArity R) →
                S i :=
              fun k => ⟨q i (z k), ⟨z k, rfl⟩⟩
            have htargetRange :
                A.rel R (g i ∘ zs) := by
              convert hArel using 1
              funext k
              rw [hg i (zs k)]
              exact (htarget_coord i (z k)).symm
            have hsourceRange :=
              ((g i).map_rel_iff R zs).mp htargetRange
            exact hsourceRange
          have hPower :
              C.rel R (e ∘ z) := by
            intro i
            exact hcoords i
          exact (e.map_rel_iff R z).mp hPower
        · intro hErel
          exact htargetHom.1 R z hErel
      map_func := htargetHom.2
    }
    exact ⟨ge, fun _ => rfl⟩

end StructuralRamsey.FunctionalPartite.Induced
