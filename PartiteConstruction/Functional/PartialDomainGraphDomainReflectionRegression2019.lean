import PartiteConstruction.Functional.PartialDomainGraphFullEmbedding2019

/-!
# Track A: domain reflection is necessary even with a closed target image

The previously verified exact homomorphism graph dictionary needs only
positive preservation of the independent domain/output relations plus
full-fibre surjectivity on source-defined inputs. This is weaker than a
FULL embedding. A full embedding MUST reflect the domain of every
operation, even if the target image is function-closed.

The simplest genuinely partial counterexample has a one-vertex carrier,
no ordinary relations, and one unary operation:
- source: undefined (`none`);
- target: defined-empty (`some ∅`).

Its identity map is a positive domain/output graph homomorphism,
the image is function-closed, and there are no source-defined inputs
on which extra target outputs could occur. Nevertheless the map is
not an induced domain/output graph embedding and cannot be any full
partial-function embedding. A positive graph homomorphism with closed
image therefore cannot replace the induced graph embedding in the
full-embedding theorem.

This is a source-semantic counterexample, not a counterexample to
the corrected ambient OLD/U-closed theorem or to the 2019 partite
construction.
-/

namespace StructuralRamsey.PartialSetStructure

/-- The independent domain/output graph sees no positive source fact
which is not preserved by mapping to the defined-empty target. -/
theorem undefinedToDefinedEmpty_graphHom :
    (domainGraph undefinedExample).IsHomomorphism
      (domainGraph definedEmptyExample) (id : Unit → Unit) := by
  intro symbol xs hx
  cases symbol with
  | inl R =>
      exact Empty.elim R
  | inr symbol =>
      cases symbol with
      | inl F =>
          obtain ⟨U, hU⟩ := hx
          cases hU
      | inr F =>
          obtain ⟨U, hU, _⟩ := hx
          cases hU

/-- The target range is literally its entire singleton carrier; it is
function-closed even though the target operation is defined-empty. -/
theorem undefinedToDefinedEmpty_closedRange :
    definedEmptyExample.IsClosed (Set.range (id : Unit → Unit)) := by
  intro F xs T _hArgs _hValue y _hy
  exact ⟨y, rfl⟩

/-- The exact-fibre condition also holds, vacuously, because there is
no source-defined input. This is deliberately not domain reflection. -/
theorem undefinedToDefinedEmpty_noExtra :
    NoExtraTargetOutputsOnDefined
      undefinedExample definedEmptyExample (id : Unit → Unit) := by
  intro F xs U hU y hy
  cases hU

/-- The identity cannot underlie a full genuine partial-function
embedding: full embeddings must distinguish undefined from defined-empty. -/
theorem undefinedToDefinedEmpty_noFull :
    ¬ ∃ e : Embedding undefinedExample definedEmptyExample,
      e.toFun = (id : Unit → Unit) := by
  rintro ⟨e, _⟩
  have hF := e.map_func () (fun _ : Fin 1 => ())
  change (none : Option (Set Unit)) = some ∅ at hF
  cases hF

/-- A positive domain/output graph homomorphism need not be an INDUCED
graph embedding even with the exact same closed target vertex range. -/
theorem undefinedToDefinedEmpty_noGraphEmbedding :
    ¬ ∃ g : RelStructure.Embedding
      (domainGraph undefinedExample) (domainGraph definedEmptyExample),
      g.toFun = (id : Unit → Unit) := by
  rintro ⟨g, _⟩
  have hTarget : (domainGraph definedEmptyExample).rel
      (.inr (.inl ())) (g.toFun ∘ (fun _ : Fin 1 => ())) := ⟨∅, rfl⟩
  have hSource :=
    (g.map_rel_iff (.inr (.inl ())) (fun _ : Fin 1 => ())).mp hTarget
  obtain ⟨U, hU⟩ := hSource
  cases hU

/-- Conjunction of all hypotheses that tempt one to remove domain
reflection, together with the failure of the full embedding. -/
theorem graphHom_closedRange_noExtra_not_full :
    (domainGraph undefinedExample).IsHomomorphism
        (domainGraph definedEmptyExample) (id : Unit → Unit) ∧
      definedEmptyExample.IsClosed (Set.range (id : Unit → Unit)) ∧
      NoExtraTargetOutputsOnDefined
        undefinedExample definedEmptyExample (id : Unit → Unit) ∧
      ¬ ∃ e : Embedding undefinedExample definedEmptyExample,
          e.toFun = (id : Unit → Unit) := by
  exact ⟨undefinedToDefinedEmpty_graphHom,
    undefinedToDefinedEmpty_closedRange,
    undefinedToDefinedEmpty_noExtra,
    undefinedToDefinedEmpty_noFull⟩

end StructuralRamsey.PartialSetStructure
