import PartiteConstruction.Structure.NullaryRoot
import PartiteConstruction.Functional.FunctionalTreeAmalgam
import PartiteConstruction.Structure.FreeAmalgamationClass

/-! # Closed local tree completions for function languages

For structures with set-valued functions, a genuine substructure is carried by
a function-closed set.  This file packages the local conclusion needed for the
functional sparsening theorem without silently replacing closed substructures
by weak induced subsets.

The global projection used by the functional partite construction may remain
weak.  The completion maps in this file are full homomorphism-embeddings and
the target trees are genuine function-language tree amalgams.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {V W X : Type v}

/-- A full relation/function structure admits a full homomorphism-embedding
into a genuine tree amalgam of copies of `Base`. -/
def HasTreeCompletion
    (Base : Structure L V) (C : Structure L W) : Prop :=
  ∃ (Y : Type v) (T : Structure L Y),
    TreeAmalgam Base Y T ∧
      ∃ f : W → Y, C.IsHomomorphismEmbedding T f

/-- Every *closed* substructure on at most `n` vertices has a full tree
completion.  The explicit `IsClosed` hypothesis is the function-language
meaning of "substructure" in the survey. -/
def LocallyClosedTreeCompletable
    (Base : Structure L V) (C : Structure L W) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    ∀ hS : C.IsClosed (↑S : Set W),
      HasTreeCompletion Base (C.induce (↑S : Set W) hS)


/-- An injective local completion.  This is the strengthened invariant used
internally by the functional mixed-step argument; forgetting injectivity gives
`LocallyClosedTreeCompletable`. -/
def HasInjectiveTreeCompletion
    (Base : Structure L V) (C : Structure L W) : Prop :=
  ∃ (Y : Type v) (T : Structure L Y),
    TreeAmalgam Base Y T ∧
      ∃ f : W → Y,
        C.IsHomomorphismEmbedding T f ∧ Function.Injective f

def LocallyClosedTreeEmbeddable
    (Base : Structure L V) (C : Structure L W) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    ∀ hS : C.IsClosed (↑S : Set W),
      HasInjectiveTreeCompletion Base (C.induce (↑S : Set W) hS)

namespace LocallyClosedTreeEmbeddable

variable {Base : Structure L V} {C : Structure L W}
variable {m n : ℕ}

theorem toLocallyClosedTreeCompletable
    (h : LocallyClosedTreeEmbeddable Base C n) :
    LocallyClosedTreeCompletable Base C n := by
  intro S hS hclosed
  obtain ⟨Y, T, hTree, f, hf, _⟩ := h S hS hclosed
  exact ⟨Y, T, hTree, f, hf⟩

theorem mono
    (h : LocallyClosedTreeEmbeddable Base C n) (hmn : m ≤ n) :
    LocallyClosedTreeEmbeddable Base C m := by
  intro S hS hclosed
  exact h S (hS.trans hmn) hclosed

theorem of_treeAmalgam
    (hTree : TreeAmalgam Base W C) (n : ℕ) :
    LocallyClosedTreeEmbeddable Base C n := by
  intro S _ hS
  let e : Embedding (C.induce (↑S : Set W) hS) C :=
    inclusion C (↑S : Set W) hS
  exact ⟨W, C, hTree, e, e.isHomomorphismEmbedding, e.injective⟩

theorem base (Base : Structure L V) (n : ℕ) :
    LocallyClosedTreeEmbeddable Base Base n := by
  have hTree : TreeAmalgam Base V Base :=
    TreeAmalgam.copy (Embedding.id Base) (by
      intro x
      exact ⟨x, rfl⟩)
  exact of_treeAmalgam hTree n

end LocallyClosedTreeEmbeddable

namespace LocallyClosedTreeCompletable

variable {Base : Structure L V} {C : Structure L W}
variable {m n : ℕ}

/-- Monotonicity in the size bound. -/
theorem mono
    (h : LocallyClosedTreeCompletable Base C n) (hmn : m ≤ n) :
    LocallyClosedTreeCompletable Base C m := by
  intro S hS hclosed
  exact h S (hS.trans hmn) hclosed

/-- If the whole structure is already a tree amalgam of copies of the base,
then every closed finite substructure has the required completion, via its
full inclusion map. -/
theorem of_treeAmalgam
    (hTree : TreeAmalgam Base W C) (n : ℕ) :
    LocallyClosedTreeCompletable Base C n := by
  intro S _ hS
  let e : Embedding (C.induce (↑S : Set W) hS) C :=
    inclusion C (↑S : Set W) hS
  exact ⟨W, C, hTree, e, e.isHomomorphismEmbedding⟩

/-- One copy of the base is locally tree completable at every scale. -/
theorem base (Base : Structure L V) (n : ℕ) :
    LocallyClosedTreeCompletable Base Base n := by
  have hTree : TreeAmalgam Base V Base :=
    TreeAmalgam.copy (Embedding.id Base) (by
      intro x
      exact ⟨x, rfl⟩)
  exact of_treeAmalgam hTree n


/-- Closed local tree-completability pulls back along a genuine full
embedding.  The image of a closed test is closed because full embeddings map
complete function fibres onto complete function fibres. -/
theorem pullback_embedding
    {C' : Structure L X}
    (h : LocallyClosedTreeCompletable Base C n)
    (e : Embedding C' C) :
    LocallyClosedTreeCompletable Base C' n := by
  classical
  intro S hScard hS
  let I : Finset W := S.image e
  have hIcard : I.card ≤ n := by
    exact (Finset.card_image_le).trans hScard
  have hset :
      (↑I : Set W) = imageSet e (↑S : Set X) := by
    ext y
    simp [I, imageSet]
  have hIclosed : C.IsClosed (↑I : Set W) := by
    rw [hset]
    exact e.image_isClosed hS
  obtain ⟨Y, T, hTree, f, hf⟩ :=
    h I hIcard hIclosed
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
  exact ⟨Y, T, hTree, f ∘ ee, hf.comp ee.isHomomorphismEmbedding⟩

end LocallyClosedTreeCompletable

/-- Function-closed subsets of the relational graph encoding are exactly
closed subsets in the original function structure. -/
theorem isClosed_iff_graph_functionClosedSet
    (A : Structure L W) (S : Set W) :
    A.IsClosed S ↔ RelStructure.FunctionClosedSet A.graph S := by
  constructor
  · intro h F x y hy hx
    apply h F x hx
    exact (graph_func_snoc A F x y).mp hy
  · intro h F x hx y hy
    apply h F x y
    · exact (graph_func_snoc A F x y).2 hy
    · exact hx



/-- For an arbitrary relational function-graph, graph closure is exactly
ordinary function closure after decoding with `Structure.ofGraph`. -/
theorem ofGraph_isClosed_iff_functionClosedSet
    (R : RelStructure L.graph W) (S : Set W) :
    (Structure.ofGraph R).IsClosed S ↔
      RelStructure.FunctionClosedSet R S := by
  constructor
  · intro h F x y hy hx
    exact h F x hx hy
  · intro h F x hx y hy
    exact h F x y hy hx

/-- Factor a full embedding through another full embedding whose range
contains it.  This is the function-language analogue of the relational helper
used by the tree-gluing proofs. -/
noncomputable def Embedding.factorThroughRange
    {A : Structure L V} {B : Structure L W} {C : Structure L X}
    (e : Embedding A C) (i : Embedding B C)
    (h : ∀ x : V, ∃ b : W, e x = i b) :
    Embedding A B where
  toFun x := Classical.choose (h x)
  injective := by
    intro x y hxy
    apply e.injective
    calc
      e x = i (Classical.choose (h x)) := Classical.choose_spec (h x)
      _ = i (Classical.choose (h y)) := congrArg i hxy
      _ = e y := (Classical.choose_spec (h y)).symm
  map_rel_iff := by
    intro R x
    let q : V → W := fun a => Classical.choose (h a)
    have heq : i ∘ (q ∘ x) = e ∘ x := by
      funext k
      exact (Classical.choose_spec (h (x k))).symm
    calc
      B.rel R (q ∘ x) ↔ C.rel R (i ∘ (q ∘ x)) :=
        (i.map_rel_iff R (q ∘ x)).symm
      _ ↔ C.rel R (e ∘ x) := by rw [heq]
      _ ↔ A.rel R x := e.map_rel_iff R x
  map_func := by
    intro F x
    let q : V → W := fun a => Classical.choose (h a)
    have heq (a : V) : i (q a) = e a :=
      (Classical.choose_spec (h a)).symm
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hea :
          e a ∈ C.func F (e ∘ x) := by
        have hm : e a ∈ imageSet e (A.func F x) := ⟨a, ha, rfl⟩
        rw [e.map_func F x] at hm
        exact hm
      have hargs : i ∘ (q ∘ x) = e ∘ x := by
        funext k
        exact heq (x k)
      have hiqa :
          i (q a) ∈ C.func F (i ∘ (q ∘ x)) := by
        rw [heq a, hargs]
        exact hea
      rw [← i.map_func F (q ∘ x)] at hiqa
      rcases hiqa with ⟨c, hc, hic⟩
      have hcq : c = q a := i.injective hic
      simpa [hcq] using hc
    · intro hb
      have hib :
          i b ∈ C.func F (i ∘ (q ∘ x)) := by
        have hm : i b ∈ imageSet i (B.func F (q ∘ x)) :=
          ⟨b, hb, rfl⟩
        rw [i.map_func F (q ∘ x)] at hm
        exact hm
      have hargs : i ∘ (q ∘ x) = e ∘ x := by
        funext k
        exact heq (x k)
      rw [hargs, ← e.map_func F x] at hib
      rcases hib with ⟨a, ha, hia⟩
      refine ⟨a, ha, ?_⟩
      apply i.injective
      calc
        i (q a) = e a := heq a
        _ = i b := hia

end StructuralRamsey.Structure

namespace StructuralRamsey.Structure

/-- On a closed set, genuine functional induction and relational graph
induction are canonically identical. -/
def induceGraphIso
    (A : Structure L W) (S : Set W) (hS : A.IsClosed S) :
    RelStructure.Iso
      (A.induce S hS).graph
      (A.graph.induce S) where
  toEquiv := Equiv.refl S
  map_rel_iff := by
    intro R x
    cases R with
    | inl R =>
        rfl
    | inr F =>
        change
          A.graph.rel (.inr F) (Subtype.val ∘ x) ↔
            (x (Fin.last (L.funcArity F))).1 ∈
              A.func F
                (fun i =>
                  (x (Fin.castSucc i)).1)
        change
          (Subtype.val ∘ x) (Fin.last (L.funcArity F)) ∈
              A.func F
                (fun i => (Subtype.val ∘ x) (Fin.castSucc i)) ↔ _
        rfl

/-- A closed test set pulls back to a closed test set along any full
embedding; in particular this applies to the side embeddings of a free
amalgam. -/
theorem closed_preimage
    {A : Structure L V} {C : Structure L W}
    (e : Embedding A C) (S : Set W) (hS : C.IsClosed S) :
    A.IsClosed (e ⁻¹' S) := by
  intro F x hx y hy
  have hey : e y ∈ C.func F (e ∘ x) := by
    have himg : e y ∈ imageSet e (A.func F x) := ⟨y, hy, rfl⟩
    rw [e.map_func F x] at himg
    exact himg
  exact hS F (e ∘ x) hx hey


namespace IsFreeAmalgam

/-- A closed test inside a full free amalgam restricts to closed tests on
both sides, and the two induced root tests agree.  This is the closure
bookkeeping used in the functional mixed-step induction. -/
theorem closedPieces
    {H E F C : Type v}
    {D : Structure L H} {A : Structure L E}
    {B : Structure L F} {T : Structure L C}
    {sA : Embedding D A} {sB : Embedding D B}
    {iA : Embedding A T} {iB : Embedding B T}
    (hfree : IsFreeAmalgam sA sB iA iB)
    (S : Set C) (hS : T.IsClosed S) :
    let ES : Set E := iA ⁻¹' S
    let FS : Set F := iB ⁻¹' S
    let HS : Set H := sA ⁻¹' ES
    A.IsClosed ES ∧
      B.IsClosed FS ∧
      D.IsClosed HS ∧
      HS = sB ⁻¹' FS := by
  dsimp
  have hEA : A.IsClosed (iA ⁻¹' S) :=
    closed_preimage iA S hS
  have hFB : B.IsClosed (iB ⁻¹' S) :=
    closed_preimage iB S hS
  have hHD : D.IsClosed (sA ⁻¹' (iA ⁻¹' S)) :=
    closed_preimage sA (iA ⁻¹' S) hEA
  refine ⟨hEA, hFB, hHD, ?_⟩
  ext d
  change iA (sA d) ∈ S ↔ iB (sB d) ∈ S
  have hcomm : iA (sA d) = iB (sB d) :=
    (hfree.overlap (sA d) (sB d)).mpr ⟨d, rfl, rfl⟩
  rw [hcomm]

end IsFreeAmalgam

end StructuralRamsey.Structure
