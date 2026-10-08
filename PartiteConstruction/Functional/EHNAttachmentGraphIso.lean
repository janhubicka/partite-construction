import PartiteConstruction.Functional.EHNAttachmentGraph
import PartiteConstruction.Iterated.LocalTreeLike

/-! # Functional free attachment commutes with function-graph encoding

This is the exact geometric compatibility needed by the direct iterated
function-language argument. A full functional attachment has the very same
vertices and incidences as the ordinary relational free attachment of the
function graphs: a graph tuple (inputs, output) is attached precisely when
the corresponding value comes from the core or one full copied structure.

The support is already closed under genuine functions. No U-closed
relational intermediate structure or recursive repair is involved.
-/

namespace StructuralRamsey.Structure.Attachment

universe u v
variable {L : Language.{u}} {V W I : Type v}

/-- Passing to the graph of actual set-valued functions commutes with
attaching a family of full copies over a closed substructure. -/
noncomputable def graphAttachmentIso
    (B : Structure L V)
    (S : Set V) (hS : B.IsClosed S)
    (D : Structure L W)
    (f : I → Embedding (B.induce S hS) D) :
    RelStructure.Iso
      ((attach B S hS D f).graph)
      (RelStructure.Attachment.attach B.graph S D.graph
        (fun i => attachingGraphMap B S hS D (f i))) where
  toEquiv := Equiv.refl _
  map_rel_iff := by
    classical
    intro R z
    apply Iff.symm
    change ((attach B S hS D f).graph.rel R z) ↔
      (RelStructure.Attachment.attach B.graph S D.graph
        (fun i => attachingGraphMap B S hS D (f i))).rel R z
    cases R with
    | inl R =>
        constructor
        · intro hz
          rcases hz with ⟨a, ha, hz⟩ | ⟨i, a, ha, hz⟩
          · exact Or.inl ⟨a, ha, hz⟩
          · refine Or.inr ⟨i, a, ha, ?_⟩
            rw [hz]
            funext k
            exact copyMap_graph_eq B S hS D f i (a k)
        · intro hz
          rcases hz with ⟨a, ha, hz⟩ | ⟨i, a, ha, hz⟩
          · exact Or.inl ⟨a, ha, hz⟩
          · refine Or.inr ⟨i, a, ha, ?_⟩
            rw [hz]
            funext k
            exact (copyMap_graph_eq B S hS D f i (a k)).symm
    | inr F =>
        change
          z (Fin.last (L.funcArity F)) ∈
            (attach B S hS D f).func F
              (fun k : Fin (L.funcArity F) => z k.castSucc) ↔
          (RelStructure.Attachment.attach B.graph S D.graph
            (fun i => attachingGraphMap B S hS D (f i))).rel (.inr F) z
        constructor
        · intro hz
          rcases hz with ⟨a, b, hb, ha, hout⟩ |
            ⟨i, a, b, hb, ha, hout⟩
          · refine Or.inl ⟨Structure.funcTuple a b, ?_, ?_⟩
            · exact (Structure.graph_func_snoc D F a b).mpr hb
            · funext k
              refine Fin.lastCases ?_ (fun l => ?_) k
              · change z (Fin.last (L.funcArity F)) = Sum.inl b
                exact hout
              · change z l.castSucc = Sum.inl (a l)
                exact congrFun ha l
          · refine Or.inr ⟨i, Structure.funcTuple a b, ?_, ?_⟩
            · exact (Structure.graph_func_snoc B F a b).mpr hb
            · funext k
              refine Fin.lastCases ?_ (fun l => ?_) k
              · change z (Fin.last (L.funcArity F)) =
                    RelStructure.Attachment.copyMap B.graph S D.graph
                      (fun j => attachingGraphMap B S hS D (f j)) i b
                exact hout.trans (copyMap_graph_eq B S hS D f i b)
              · change z l.castSucc =
                    RelStructure.Attachment.copyMap B.graph S D.graph
                      (fun j => attachingGraphMap B S hS D (f j)) i (a l)
                exact (congrFun ha l).trans
                  (copyMap_graph_eq B S hS D f i (a l))
        · intro hz
          rcases hz with ⟨t, ht, heq⟩ | ⟨i, t, ht, heq⟩
          · have ht' : t (Fin.last (L.funcArity F)) ∈
                D.func F (fun k => t k.castSucc) := ht
            refine Or.inl ⟨(fun k => t k.castSucc),
              t (Fin.last (L.funcArity F)), ht', ?_, ?_⟩
            · funext k
              exact congrFun heq k.castSucc
            · exact congrFun heq (Fin.last (L.funcArity F))
          · have ht' : t (Fin.last (L.funcArity F)) ∈
                B.func F (fun k => t k.castSucc) := ht
            refine Or.inr ⟨i, (fun k => t k.castSucc),
              t (Fin.last (L.funcArity F)), ht', ?_, ?_⟩
            · funext k
              calc
                z k.castSucc =
                    RelStructure.Attachment.copyMap B.graph S D.graph
                      (fun j => attachingGraphMap B S hS D (f j))
                      i (t k.castSucc) := congrFun heq k.castSucc
                _ = copyMap B S hS D f i (t k.castSucc) :=
                    (copyMap_graph_eq B S hS D f i (t k.castSucc)).symm
            · calc
                z (Fin.last (L.funcArity F)) =
                    RelStructure.Attachment.copyMap B.graph S D.graph
                      (fun j => attachingGraphMap B S hS D (f j))
                      i (t (Fin.last (L.funcArity F))) :=
                    congrFun heq (Fin.last (L.funcArity F))
                _ = copyMap B S hS D f i (t (Fin.last (L.funcArity F))) :=
                    (copyMap_graph_eq B S hS D f i
                      (t (Fin.last (L.funcArity F)))).symm

end StructuralRamsey.Structure.Attachment
