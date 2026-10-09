import PartiteConstruction.Ramsey.ClosureDescription2019
import PartiteConstruction.Partite.Induced

/-! # Closedness of native positive partite powers

For a U-closed part structure A and a U-closed A-partite B, the EXISTING
positive coordinatewise power of B is U-closed. Coordinate root embeddings
have unique closure tuples in B. Their projections all equal the unique
closure tuple over the common root in A, so their output coordinates have
consistent part tags and really define vertices of the partite power.

This uses ordinary partiteness, not a protected core-projection premise.
It proves closedness only: it does not equate ordinary and closed-test
homomorphism-embeddings. The latter still require a separate invariant.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure

universe u v w
variable {L : RelLanguage.{u}} {P V : Type v} {N : ℕ}

/-- Coordinate evaluation of the native positive power is an ordinary
homomorphism-embedding. Fullness on irreducible tests follows by composing
with the part map, whose restriction is already an embedding. -/
theorem coordinate_isHomomorphismEmbedding
    {A : RelStructure L P} (B : System L P V)
    (hB : B.IsPartiteOver A) (k : Fin N) :
    (power B N).toRelStructure.IsHomomorphismEmbedding B.toRelStructure
      (fun x => x.coord k) := by
  have hN : 0 < N := Nat.zero_lt_of_lt k.isLt
  have hPower := power_isPartiteOver hB hN
  constructor
  · intro R z hz
    exact hz k
  · intro S hS
    obtain ⟨g, hg⟩ := hPower.embeddingOn S hS
    let d : RelStructure.Embedding ((power B N).toRelStructure.induce S)
        B.toRelStructure := {
      toFun := fun x => x.1.coord k
      injective := by
        intro x y hxy
        apply g.injective
        calc
          g x = (power B N).part x.1 := hg x
          _ = B.part (x.1.coord k) := (x.1.belongs k).symm
          _ = B.part (y.1.coord k) := congrArg B.part hxy
          _ = (power B N).part y.1 := y.1.belongs k
          _ = g y := (hg y).symm
      map_rel_iff := by
        intro R z
        constructor
        · intro hz
          have hA : A.rel R (B.part ∘ (fun i => (z i).1.coord k)) :=
            hB.1 R _ hz
          have hEq : g ∘ z = B.part ∘ (fun i => (z i).1.coord k) := by
            funext i
            exact (hg (z i)).trans ((z i).1.belongs k).symm
          apply (g.map_rel_iff R z).mp
          rw [hEq]
          exact hA
        · intro hz
          exact hz k
    }
    exact ⟨d, fun _ => rfl⟩

/-- Native positive coordinate powers preserve all relational closure
rules. Positivity supplies a coordinate for root reflection and tag
uniqueness. No finite vertex or nonempty-part hypothesis is needed. -/
theorem power_isUClosed
    {rules : ClosureDescription L} {A : RelStructure L P}
    (B : System L P V) (hPart : B.IsPartiteOver A)
    (hA : IsUClosed rules A) (hB : IsUClosed rules B.toRelStructure)
    (hN : 0 < N) : IsUClosed rules (power B N).toRelStructure := by
  classical
  let k0 : Fin N := ⟨0, hN⟩
  intro rule hrule
  constructor
  · intro t ht
    have hRoots : ∀ k : Fin N, ∃ r : RelStructure.Embedding rule.root B.toRelStructure,
        ∀ i : Fin rule.rootSize, (t (i.castLE rule.rootLE)).coord k = r i := by
      intro k
      exact (hB rule hrule).1 (fun j => (t j).coord k) (ht k)
    let r (k : Fin N) : RelStructure.Embedding rule.root B.toRelStructure :=
      Classical.choose (hRoots k)
    have hr (k : Fin N) (i : Fin rule.rootSize) :
        (t (i.castLE rule.rootLE)).coord k = r k i :=
      Classical.choose_spec (hRoots k) i
    let e : RelStructure.Embedding rule.root (power B N).toRelStructure := {
      toFun := fun i => t (i.castLE rule.rootLE)
      injective := by
        intro i j hij
        apply (r k0).injective
        exact (hr k0 i).symm.trans
          ((congrArg (fun x : Vertex B N => x.coord k0) hij).trans (hr k0 j))
      map_rel_iff := by
        intro R z
        constructor
        · intro hz
          have hCoord : B.rel R
              (fun j => (t ((z j).castLE rule.rootLE)).coord k0) := hz k0
          have hEq : (fun j => (t ((z j).castLE rule.rootLE)).coord k0) =
              r k0 ∘ z := funext (fun j => hr k0 (z j))
          apply ((r k0).map_rel_iff R z).mp
          rw [← hEq]
          exact hCoord
        · intro hz k
          have hCoord : B.rel R (r k ∘ z) := ((r k).map_rel_iff R z).mpr hz
          have hEq : (fun j => (t ((z j).castLE rule.rootLE)).coord k) =
              r k ∘ z := funext (fun j => hr k (z j))
          change B.rel R (fun j => (t ((z j).castLE rule.rootLE)).coord k)
          rw [hEq]
          exact hCoord
    }
    exact ⟨e, fun _ => rfl⟩
  · intro e
    have hPartPower := power_isPartiteOver hPart hN
    obtain ⟨eA, heA⟩ := hPartPower.after_irreducible_embedding
      rule.rootIrreducible e
    obtain ⟨tA, htA, hUniqueA⟩ := (hA rule hrule).2 eA
    have hCoords : ∀ k : Fin N, ∃ r : RelStructure.Embedding rule.root B.toRelStructure,
        ∀ i, r i = (e i).coord k := by
      intro k
      exact (coordinate_isHomomorphismEmbedding B hPart k).after_irreducible_embedding
        rule.rootIrreducible e
    let r (k : Fin N) : RelStructure.Embedding rule.root B.toRelStructure :=
      Classical.choose (hCoords k)
    have hr (k : Fin N) (i : Fin rule.rootSize) : r k i = (e i).coord k :=
      Classical.choose_spec (hCoords k) i
    let ts (k : Fin N) : Fin (L.arity rule.symbol) → V :=
      Classical.choose ((hB rule hrule).2 (r k))
    have hts (k : Fin N) : B.rel rule.symbol (ts k) ∧
        ∀ i : Fin rule.rootSize, ts k (i.castLE rule.rootLE) = r k i :=
      (Classical.choose_spec ((hB rule hrule).2 (r k))).1
    have hUnique (k : Fin N) : ∀ s : Fin (L.arity rule.symbol) → V,
        (B.rel rule.symbol s ∧
          ∀ i : Fin rule.rootSize, s (i.castLE rule.rootLE) = r k i) → s = ts k :=
      (Classical.choose_spec ((hB rule hrule).2 (r k))).2
    have hTags (k : Fin N) : B.part ∘ ts k = tA := by
      apply hUniqueA
      constructor
      · exact hPart.1 rule.symbol (ts k) (hts k).1
      · intro i
        calc
          B.part (ts k (i.castLE rule.rootLE)) = B.part (r k i) :=
            congrArg B.part ((hts k).2 i)
          _ = B.part ((e i).coord k) := congrArg B.part (hr k i)
          _ = (power B N).part (e i) := (e i).belongs k
          _ = eA i := (heA i).symm
    let t : Fin (L.arity rule.symbol) → Vertex B N := fun j => {
      part := tA j
      coord := fun k => ts k j
      belongs := fun k => congrFun (hTags k) j
    }
    have hRootT (i : Fin rule.rootSize) : t (i.castLE rule.rootLE) = e i := by
      apply NonInduced.Vertex.ext B
      · exact (htA.2 i).trans (heA i)
      · intro k
        exact ((hts k).2 i).trans (hr k i)
    refine ⟨t, ⟨?_, hRootT⟩, ?_⟩
    · intro k
      exact (hts k).1
    · intro s hs
      have hCoordEq (k : Fin N) : (fun j => (s j).coord k) = ts k := by
        apply hUnique k
        constructor
        · exact hs.1 k
        · intro i
          exact (congrArg (fun x : Vertex B N => x.coord k) (hs.2 i)).trans
            (hr k i).symm
      funext j
      apply NonInduced.Vertex.ext B
      · calc
          (s j).part = B.part ((s j).coord k0) := ((s j).belongs k0).symm
          _ = B.part (ts k0 j) := congrArg B.part (congrFun (hCoordEq k0) j)
          _ = tA j := congrFun (hTags k0) j
      · intro k
        exact congrFun (hCoordEq k) j

end StructuralRamsey.Partite.Induced
