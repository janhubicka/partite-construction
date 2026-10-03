import PartiteConstruction.Iterated.MixedOverlapObstruction

/-! # A concrete reducible-overlap obstruction

An irreducible ternary structure can have a reducible two-vertex induced
substructure. On such an overlap, homomorphism-embeddings are allowed to
collapse vertices. Two valid side witnesses may therefore have incompatible
kernels, exactly blocking the current mixed gluing interface.
-/
namespace StructuralRamsey.RelStructure.MixedOverlapExample

universe u

/-- One ternary relation symbol. -/
def L : RelLanguage where
  Symbol := Unit
  arity := fun _ => 3

/-- A three-point irreducible structure: a ternary tuple is a relation exactly
when its three coordinates are pairwise separated, i.e. the tuple map is
injective. -/
def A : RelStructure L (Fin 3) where
  rel := fun _ x => Function.Injective x

/-- A two-point structure with no relation tuples. -/
def G : RelStructure L Bool where
  rel := fun _ _ => False

theorem A_irreducible : A.Irreducible := by
  intro x y hxy
  let z : Fin 3 → Fin 3 := fun i => i
  refine ⟨(), z, x, y, ?_, rfl, rfl⟩
  change Function.Injective z
  exact Function.injective_id

/-- Any irreducible induced substructure of the empty two-point structure has
at most one point. -/
theorem G_irreducible_subsingleton
    (S : Set Bool) (hS : (G.induce S).Irreducible) :
    ∀ x y : S, x = y := by
  intro x y
  by_contra hxy
  obtain ⟨R, z, i, j, hz, _, _⟩ := hS hxy
  exact hz.elim

/-- Every map from G to A is a homomorphism-embedding: on every irreducible
induced subset of G the domain has at most one point. -/
theorem any_map_isHomomorphismEmbedding (h : Bool → Fin 3) :
    G.IsHomomorphismEmbedding A h := by
  constructor
  · intro R x hx
    exact hx.elim
  · intro S hS
    have hall : ∀ x y : S, x = y :=
      G_irreducible_subsingleton S hS
    let e : Embedding (G.induce S) A := {
      toFun := fun x => h x.1
      injective := by
        intro x y _
        exact hall x y
      map_rel_iff := by
        intro R x
        constructor
        · intro hinj
          change Function.Injective (fun i => h (x i).1) at hinj
          have h01 : (0 : Fin 3) ≠ 1 := by decide
          apply h01
          apply hinj
          have hsub : x 0 = x 1 := hall (x 0) (x 1)
          exact congrArg (fun q : S => h q.1) hsub
        · intro hfalse
          exact hfalse.elim
    }
    exact ⟨e, fun _ => rfl⟩

/-- Left witness collapses the two overlap points. -/
def leftMap : Bool → Fin 3 := fun _ => 0

/-- Right witness separates them. -/
def rightMap : Bool → Fin 3
  | false => 0
  | true => 1

theorem left_valid : G.IsHomomorphismEmbedding A leftMap :=
  any_map_isHomomorphismEmbedding leftMap

theorem right_valid : G.IsHomomorphismEmbedding A rightMap :=
  any_map_isHomomorphismEmbedding rightMap

theorem kernel_mismatch :
    leftMap false = leftMap true ∧
      rightMap false ≠ rightMap true := by
  constructor <;> decide

/-- Although both side maps are valid homomorphism-embeddings into the same
irreducible target A, they cannot factor compatibly through embeddings of one
common target overlap. -/
theorem no_common_embedded_overlap :
    ¬ ∃ (X : Type) (H : RelStructure L X)
        (tE : Embedding H A) (tF : Embedding H A)
        (q : Bool → X),
        (∀ d, leftMap d = tE (q d)) ∧
        (∀ d, rightMap d = tF (q d)) := by
  rcases kernel_mismatch with ⟨hc, hs⟩
  exact
    LocallyTreeLike.no_compatible_overlap_of_kernel_mismatch
      (Dsrc := G) (Esrc := G) (Fsrc := G)
      (ETgt := A) (FTgt := A)
      (sE := Embedding.id G) (sF := Embedding.id G)
      leftMap rightMap false true hc hs

end StructuralRamsey.RelStructure.MixedOverlapExample
