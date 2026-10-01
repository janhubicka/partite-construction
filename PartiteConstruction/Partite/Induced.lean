import PartiteConstruction.Relational.Homomorphism
import PartiteConstruction.Partite.NonInduced
import PartiteConstruction.Partite.Operations

/-! # The induced Partite Lemma

The carrier of the power is the same tagged product used by the non-induced
construction. Here relations are interpreted coordinatewise. The projection
to the part structure is assumed to be a homomorphism-embedding; relation
preservation is the only part of that hypothesis needed for the Hales--Jewett
argument itself. The stronger projection invariant is verified separately.
-/
namespace StructuralRamsey.Partite

open RelStructure HalesJewett SuccessorTree

universe u v w z

variable {L : RelLanguage.{u}} {P : Type v} {V : Type w}

/-- The survey's notion of an `A`-partite system: the partition projection
is a homomorphism-embedding of the relational reduct to `A`. -/
def System.IsPartiteOver (B : System L P V) (A : RelStructure L P) : Prop :=
  B.toRelStructure.IsHomomorphismEmbedding A B.part

namespace Induced

variable (A : RelStructure L P) (B : System L P V)

/-- Relabelling the parts along an induced embedding preserves the
homomorphism-embedding projection invariant. -/
theorem relabel_isPartiteOver {Q : Type z} {D : RelStructure L Q}
    (hB : B.IsPartiteOver A) (α : RelStructure.Embedding A D) :
    (B.relabel α.toFunctionEmbedding).IsPartiteOver D := by
  change B.toRelStructure.IsHomomorphismEmbedding D (α ∘ B.part)
  exact α.isHomomorphismEmbedding.comp hB

/-- Restricting a partite system to the parts in the image of an induced
embedding again gives a partite system over the source structure. -/
theorem restrict_isPartiteOver {Q : Type z} (D : RelStructure L P)
    (C : System L P V) (A₀ : RelStructure L Q)
    (hC : C.IsPartiteOver D) (α : RelStructure.Embedding A₀ D) :
    (C.restrict α.toFunctionEmbedding).IsPartiteOver A₀ := by
  let αf : Q ↪ P := α.toFunctionEmbedding
  let E := C.restrict αf
  have hhom : E.toRelStructure.IsHomomorphism A₀ E.part := by
    intro R x hx
    have hD : D.rel R (C.part ∘ (Subtype.val ∘ x)) :=
      hC.1 R (Subtype.val ∘ x) hx
    have heq : α ∘ (E.part ∘ x) = C.part ∘ (Subtype.val ∘ x) := by
      funext i
      exact C.restrictedPart_spec αf (x i)
    have htarget : D.rel R (α ∘ (E.part ∘ x)) := by
      rw [heq]
      exact hD
    exact (α.map_rel_iff R (E.part ∘ x)).mp htarget
  refine ⟨hhom, ?_⟩
  intro S hS
  let T : Set V := Set.range (fun s : S => (s.1 : C.support αf).1)
  have hT : (C.toRelStructure.induce T).Irreducible := by
    intro a b hab
    rcases a.property with ⟨sa, hsa⟩
    rcases b.property with ⟨sb, hsb⟩
    have hsab : sa ≠ sb := by
      intro heq
      apply hab
      apply Subtype.ext
      rw [← hsa, ← hsb, heq]
    obtain ⟨R, x, i, j, hx, hxi, hxj⟩ := hS hsab
    change E.rel R (Subtype.val ∘ x) at hx
    let xT : Fin (L.arity R) → T :=
      fun k => ⟨((x k).1 : C.support αf).1, ⟨x k, rfl⟩⟩
    refine ⟨R, xT, i, j, ?_, ?_, ?_⟩
    · change C.rel R (Subtype.val ∘ xT)
      change C.rel R (Subtype.val ∘ (Subtype.val ∘ x)) at hx
      convert hx using 1
      funext k
      rfl
    · apply Subtype.ext
      change ((x i).1 : C.support αf).1 = a.1
      rw [hxi]
      exact hsa
    · apply Subtype.ext
      change ((x j).1 : C.support αf).1 = b.1
      rw [hxj]
      exact hsb
  let e : RelStructure.Embedding (E.toRelStructure.induce S) A₀ := {
    toFun := fun x => E.part x.1
    injective := by
      intro x y hxy
      by_contra hne
      obtain ⟨R, z, i, j, hz, hzi, hzj⟩ := hS hne
      change E.rel R (Subtype.val ∘ z) at hz
      have hp :
          E.part ((Subtype.val ∘ z) i) =
            E.part ((Subtype.val ∘ z) j) := by
        simpa [Function.comp_apply, hzi, hzj] using hxy
      have hv := E.transversal R (Subtype.val ∘ z) hz i j hp
      have hzij : z i = z j := Subtype.ext hv
      exact hne (hzi.symm.trans (hzij.trans hzj))
    map_rel_iff := by
      intro R x
      constructor
      · intro hA
        let y : Fin (L.arity R) → V :=
          fun k => ((x k).1 : C.support αf).1
        have hyT : ∀ k, y k ∈ T := by
          intro k
          exact ⟨x k, rfl⟩
        have hDα : D.rel R (α ∘ (E.part ∘ (Subtype.val ∘ x))) :=
          (α.map_rel_iff R (E.part ∘ (Subtype.val ∘ x))).mpr hA
        have hD : D.rel R (C.part ∘ y) := by
          convert hDα using 1
          funext k
          exact (C.restrictedPart_spec αf ((x k).1)).symm
        have hCrel := hC.reflect_rel_on T hT R y hyT hD
        change E.rel R (Subtype.val ∘ x)
        exact hCrel
      · intro hx
        exact hhom R (Subtype.val ∘ x) hx
  }
  exact ⟨e, fun _ => rfl⟩

abbrev Letter := NonInduced.Letter A B
abbrev Vertex (N : ℕ) := NonInduced.Vertex B N

variable {A B} {N : ℕ}

/-- Coordinatewise power from the induced partite construction. -/
def power (B : System L P V) (N : ℕ) : System L P (Vertex B N) where
  part := NonInduced.Vertex.part
  rel R z := ∀ i, B.rel R (fun j => (z j).coord i)
  transversal := by
    intro R z hz i j hp
    apply NonInduced.Vertex.ext B hp
    intro k
    apply B.transversal R (fun t => (z t).coord k) (hz k) i j
    exact ((z i).belongs k).trans (hp.trans ((z j).belongs k).symm)

/-- For a positive power, its projection preserves all relations. Positivity
is essential: at exponent zero the coordinatewise relation condition is
vacuous. -/
theorem power_projection_homomorphism (hB : B.IsPartiteOver A) (hN : 0 < N) :
    (power B N).toRelStructure.IsHomomorphism A (power B N).part := by
  intro R z hz
  let i0 : Fin N := ⟨0, hN⟩
  have hcoord : B.rel R (fun j => (z j).coord i0) := hz i0
  have hA := hB.1 R (fun j => (z j).coord i0) hcoord
  convert hA using 1
  funext j
  exact ((z j).belongs i0).symm

/-- Positive coordinate powers remain `A`-partite. The nontrivial
reflection step is checked on each coordinate image of an irreducible
substructure: that image is again irreducible, so the original projection
homomorphism-embedding reflects the relation there. -/
theorem power_isPartiteOver (hB : B.IsPartiteOver A) (hN : 0 < N) :
    (power B N).IsPartiteOver A := by
  constructor
  · exact power_projection_homomorphism hB hN
  · intro S hS
    let e : RelStructure.Embedding ((power B N).toRelStructure.induce S) A := {
      toFun := fun x => (power B N).part x.1
      injective := by
        intro x y hxy
        by_contra hne
        obtain ⟨R, z, i, j, hz, hzi, hzj⟩ := hS hne
        change (power B N).rel R (Subtype.val ∘ z) at hz
        have hp :
            (power B N).part ((Subtype.val ∘ z) i) =
              (power B N).part ((Subtype.val ∘ z) j) := by
          simpa [Function.comp_apply, hzi, hzj] using hxy
        have hv := (power B N).transversal R (Subtype.val ∘ z) hz i j hp
        have hzij : z i = z j := Subtype.ext hv
        exact hne (hzi.symm.trans (hzij.trans hzj))
      map_rel_iff := by
        intro R x
        constructor
        · intro hA
          change (power B N).rel R (Subtype.val ∘ x)
          intro k
          let y : Fin (L.arity R) → V := fun j => (x j).1.coord k
          let T : Set V := Set.range (fun s : S => s.1.coord k)
          have hT : (B.toRelStructure.induce T).Irreducible := by
            intro a b hab
            rcases a.property with ⟨sa, hsa⟩
            rcases b.property with ⟨sb, hsb⟩
            have hsab : sa ≠ sb := by
              intro heq
              apply hab
              apply Subtype.ext
              rw [← hsa, ← hsb, heq]
            obtain ⟨R', z, i, j, hz, hzi, hzj⟩ := hS hsab
            change (power B N).rel R' (Subtype.val ∘ z) at hz
            have hzB : B.rel R' (fun t => (z t).1.coord k) := hz k
            let zT : Fin (L.arity R') → T :=
              fun t => ⟨(z t).1.coord k, ⟨z t, rfl⟩⟩
            refine ⟨R', zT, i, j, ?_, ?_, ?_⟩
            · change B.rel R' (Subtype.val ∘ zT)
              convert hzB using 1
              funext t
              rfl
            · apply Subtype.ext
              change (z i).1.coord k = a.1
              rw [hzi]
              exact hsa
            · apply Subtype.ext
              change (z j).1.coord k = b.1
              rw [hzj]
              exact hsb
          have hyT : ∀ j, y j ∈ T := by
            intro j
            exact ⟨x j, rfl⟩
          have hAcoord : A.rel R (B.part ∘ y) := by
            convert hA using 1
            funext j
            exact (x j).1.belongs k
          exact hB.reflect_rel_on T hT R y hyT hAcoord
        · intro hx
          change (power B N).rel R (Subtype.val ∘ x) at hx
          have hA := power_projection_homomorphism hB hN R
            (Subtype.val ∘ x) hx
          convert hA using 1
          funext j
          rfl
    }
    exact ⟨e, fun _ => rfl⟩

/-- Reflection for each Hales--Jewett line is immediate from a parameter
coordinate; preservation at constant coordinates uses the projection
homomorphism and the letter embedding. -/
theorem lineMap_rel_iff (hB : B.IsPartiteOver A)
    (W : Line (Letter A B) N) (R : L.Symbol)
    (x : Fin (L.arity R) → V) :
    (power B N).rel R (NonInduced.lineMap W ∘ x) ↔ B.rel R x := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := W.hasParameter
    have hiRel := h i
    simpa only [NonInduced.lineMap, hi, Function.comp_apply] using hiRel
  · intro hx i
    cases hi : W.symbol i with
    | parameter =>
        simpa only [NonInduced.lineMap, hi, Function.comp_apply] using hx
    | const e =>
        have hA : A.rel R (B.part ∘ x) := hB.1 R x hx
        have he : B.rel R (e ∘ (B.part ∘ x)) :=
          (e.toEmbedding.map_rel_iff R (B.part ∘ x)).mpr hA
        have htarget : B.rel R (fun j => e (B.part (x j))) := by
          convert he using 1
          funext j
          rfl
        simpa only [NonInduced.lineMap, hi, Function.comp_apply] using htarget

/-- Every parameter word gives an induced part-preserving embedding into the
coordinatewise power. -/
def lineEmbedding (hB : B.IsPartiteOver A) (W : Line (Letter A B) N) :
    Partite.Embedding B (power B N) where
  toFun := NonInduced.lineMap W
  injective := NonInduced.lineMap_injective W
  map_rel_iff := lineMap_rel_iff hB W
  map_part := fun _ => rfl

/-- Word embedding into the coordinatewise power. -/
def wordEmbedding (hB : B.IsPartiteOver A) (hN : 0 < N)
    (w : Fin N → Letter A B) :
    Partite.Embedding (transversal A) (power B N) :=
  (lineEmbedding hB (NonInduced.firstLine hN w)).comp (w ⟨0, hN⟩)

@[simp] theorem wordEmbedding_apply (hB : B.IsPartiteOver A) (hN : 0 < N)
    (w : Fin N → Letter A B) (p : P) :
    wordEmbedding hB hN w p = NonInduced.wordMap w p := by
  change NonInduced.lineMap (NonInduced.firstLine hN w) (w ⟨0, hN⟩ p) = _
  rw [NonInduced.lineMap_comp_letter, NonInduced.firstLine_eval]

theorem lineEmbedding_comp_letter (hB : B.IsPartiteOver A) (hN : 0 < N)
    (W : Line (Letter A B) N) (e : Letter A B) :
    (lineEmbedding hB W).comp e = wordEmbedding hB hN (W.eval e) := by
  apply Partite.Embedding.ext
  intro p
  exact (NonInduced.lineMap_comp_letter W e p).trans
    (wordEmbedding_apply hB hN (W.eval e) p).symm

/-- Induced Partite Lemma for any finite colour type. -/
theorem partiteLemma (hB : B.IsPartiteOver A) [Finite P] [Finite V]
    (κ : Type*) [Fintype κ] :
    ∃ N : ℕ, 0 < N ∧ Partite.Arrow (transversal A) B (power B N) κ := by
  classical
  let : Fintype (Letter A B) := Fintype.ofFinite _
  obtain ⟨N, hN, hHJ⟩ := HalesJewett.finite (α := Letter A B) (κ := κ)
  refine ⟨N, hN, ?_⟩
  intro χ
  obtain ⟨W, hW⟩ := hHJ (fun w => χ (wordEmbedding hB hN w))
  refine ⟨lineEmbedding hB W, ?_⟩
  intro e₁ e₂
  simpa only [lineEmbedding_comp_letter hB hN] using hW e₁ e₂

end Induced
end StructuralRamsey.Partite
