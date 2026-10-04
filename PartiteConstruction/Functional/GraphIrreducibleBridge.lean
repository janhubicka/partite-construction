import PartiteConstruction.Functional.WeakInvariant
import PartiteConstruction.Structure.WeakSubstructure

set_option autoImplicit false

/-! # From EHN projections to graph homomorphism-embeddings

The functional EHN construction keeps a weak projection globally and a full
embedding on every closed functional irreducible.  The iterated sparsening
machinery works with irreducibility of the relational graph encoding.  These
notions are compatible: a graph-irreducible weak substructure generates an
irreducible closed functional hull.  Consequently every EHN
homomorphism-embedding is a homomorphism-embedding on graph encodings.
-/
namespace StructuralRamsey.Structure

open StructuralRamsey

universe u v
variable {L : Language.{u}} {U V W X : Type v}

/-- The relational graph encoding of a full functional free amalgam is a
relational free amalgam. -/
theorem IsFreeAmalgam.graph
    {D : Structure L U} {A : Structure L V}
    {B : Structure L W} {C : Structure L X}
    {fA : Embedding D A} {fB : Embedding D B}
    {iA : Embedding A C} {iB : Embedding B C}
    (h : IsFreeAmalgam fA fB iA iB) :
    RelStructure.IsFreeAmalgam fA.graph fB.graph iA.graph iB.graph := by
  refine {
    covers := h.covers
    overlap := h.overlap
    rel_iff := ?_
  }
  intro R z
  cases R with
  | inl R =>
      exact h.rel_iff R z
  | inr F =>
      let args : Fin (L.funcArity F) → X :=
        fun k => z k.castSucc
      let out : X := z (Fin.last (L.funcArity F))
      have heta : funcTuple args out = z := by
        simpa [args, out] using (funcTuple_eta z)
      constructor
      · intro hz
        have hz' : out ∈ C.func F args := by
          change
            z (Fin.last (L.funcArity F)) ∈
              C.func F (fun k => z k.castSucc)
          exact hz
        rcases (h.func_iff F args out).mp hz' with
          ⟨a, b, hb, hargs, hout⟩ | ⟨a, b, hb, hargs, hout⟩
        · refine Or.inl ⟨funcTuple a b, ?_, ?_⟩
          · exact (graph_func_snoc A F a b).2 hb
          · calc
              z = funcTuple args out := heta.symm
              _ = funcTuple (iA ∘ a) (iA b) := by
                rw [hargs, hout]
              _ = iA ∘ funcTuple a b :=
                (comp_funcTuple (iA : V → X) a b).symm
        · refine Or.inr ⟨funcTuple a b, ?_, ?_⟩
          · exact (graph_func_snoc B F a b).2 hb
          · calc
              z = funcTuple args out := heta.symm
              _ = funcTuple (iB ∘ a) (iB b) := by
                rw [hargs, hout]
              _ = iB ∘ funcTuple a b :=
                (comp_funcTuple (iB : W → X) a b).symm
      · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
        · exact (iA.graph.map_rel_iff (.inr F) t).mpr ht
        · exact (iB.graph.map_rel_iff (.inr F) t).mpr ht

/-- Graph irreducibility is stronger than functional free-amalgamation
irreducibility. -/
theorem Irreducible.of_graph
    {A : Structure L V} (hA : A.graph.Irreducible) :
    A.Irreducible := by
  intro H E F C Dsrc Esrc Fsrc Csrc sE sF iE iF hfree e
  exact hA hfree.graph e.graph

/-- The graph of a weak substructure is irreducible whenever the corresponding
induced substructure of the ambient graph is irreducible. -/
theorem weakInduce_irreducible_of_graph
    (A : Structure L V) (S : Set V)
    (hS : (A.graph.induce S).Irreducible) :
    (A.weakInduce S).Irreducible := by
  apply Irreducible.of_graph
  intro x y hxy
  obtain ⟨R, z, i, j, hz, hzi, hzj⟩ := hS hxy
  refine ⟨R, z, i, j, ?_, hzi, hzj⟩
  exact ((weakGraphFromInduce A S).map_rel_iff R z).mpr hz

/-- The canonical inclusion of a weak substructure is a weak homomorphism of
the original function structures. -/
theorem weakInduce_isWeakHomomorphism
    (A : Structure L V) (S : Set V) :
    (A.weakInduce S).IsWeakHomomorphism A Subtype.val := by
  constructor
  · intro R x hx
    exact hx
  · intro F x y hy
    exact hy

/-- A graph-irreducible finite set generates an irreducible closed functional
hull. -/
theorem graphIrreducible_functionClosure
    (A : Structure L V) (S : Set V)
    (hS : (A.graph.induce S).Irreducible) :
    (A.induce
      (A.functionClosure (Set.range (Subtype.val : S → V)))
      (A.functionClosure_isClosed
        (Set.range (Subtype.val : S → V)))).Irreducible := by
  have hWeak : (A.weakInduce S).Irreducible :=
    weakInduce_irreducible_of_graph A S hS
  exact hWeak.functionClosure_weakImage
    (weakInduce_isWeakHomomorphism A S)

/-- Weak functional homomorphisms induce relational homomorphisms on graph
encodings. -/
theorem IsWeakHomomorphism.graph
    {A : Structure L V} {B : Structure L W} {f : V → W}
    (h : A.IsWeakHomomorphism B f) :
    A.graph.IsHomomorphism B.graph f := by
  intro R x hx
  cases R with
  | inl R =>
      exact h.1 R x hx
  | inr F =>
      change
        f (x (Fin.last (L.funcArity F))) ∈
          B.func F (fun i => f (x i.castSucc))
      have hs :
          x (Fin.last (L.funcArity F)) ∈
            A.func F (fun i => x i.castSucc) := hx
      simpa [Function.comp_apply] using
        h.2 F (fun i => x i.castSucc)
          (x (Fin.last (L.funcArity F))) hs

/-- The EHN projection invariant implies the graph homomorphism-embedding
invariant used by the relational iterated construction. -/
theorem IsEHNHomomorphismEmbedding.graph
    {A : Structure L V} {B : Structure L W} {f : V → W}
    (h : A.IsEHNHomomorphismEmbedding B f) :
    A.graph.IsHomomorphismEmbedding B.graph f := by
  constructor
  · exact h.1.graph
  · intro S hS
    let Hset : Set V :=
      A.functionClosure (Set.range (Subtype.val : S → V))
    have hHclosed : A.IsClosed Hset :=
      A.functionClosure_isClosed (Set.range (Subtype.val : S → V))
    let H : Structure L Hset := A.induce Hset hHclosed
    have hH : H.Irreducible := by
      exact graphIrreducible_functionClosure A S hS
    let inc : Embedding H A := inclusion A Hset hHclosed
    obtain ⟨g, hg⟩ := h.2 H hH inc
    let toH : RelStructure.Embedding (A.graph.induce S) H.graph := {
      toFun := fun x =>
        ⟨x.1, A.subset_functionClosure
          (Set.range (Subtype.val : S → V)) ⟨x, rfl⟩⟩
      injective := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg Subtype.val hxy
      map_rel_iff := by
        intro R x
        change
          A.graph.rel R
              (Subtype.val ∘
                (fun i =>
                  (⟨(x i).1,
                    A.subset_functionClosure
                      (Set.range (Subtype.val : S → V))
                      ⟨x i, rfl⟩⟩ : Hset))) ↔
            A.graph.rel R (Subtype.val ∘ x)
        congr 1
        funext i
        rfl
    }
    refine ⟨g.graph.comp toH, ?_⟩
    intro x
    change g (toH x) = f x.1
    exact hg (toH x)

end StructuralRamsey.Structure
