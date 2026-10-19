import PartiteConstruction.Functional.CanonicalTagFreeAmalgam2019
import PartiteConstruction.Functional.PartialFunctionPatternGraph2019
import PartiteConstruction.Structure.FreeAmalgam

/-!
# Genuine native functional free amalgams preserve OLD equality-pattern graphs

For a FULL native relation/set-valued-function free amalgam, every
positive primitive function value comes from exactly one side.
The equality-pattern argMap is SURJECTIVE onto the distinct native
input root vertices. Therefore all distinct root vertices also
lie in the chosen side; the original complete-domain and output
graph relations cannot cross the free-amalgam cut.

This verifies the source diagram in the OLD relational function
pattern language with the EXACT same vertices and full side maps.
Composing it with the verified fresh-tag free-amalgam theorem then
preserves the canonical 2019 U-closure-pattern source geometry.

All actual input equality patterns, repeated coordinates, nullaries
and MULTIVALUED function fibres are retained. No function-generated
closure changes a weak test or its cardinality. This is a SOURCE
free-amalgam theorem, not a common strict B-tree TARGET completion.
-/

namespace StructuralRamsey.Structure

universe v
variable {E C : Type v}

/-- Lift the entire DISTINCT input-root enumeration through one
injective map, given that every root coordinate occurs as an
original argument coordinate.

This is the elementary exact-equality-pattern step used in the
native functional / U-closed correspondence. It does not add any
vertices and holds even for repeated arguments and nullaries. -/
theorem surjectiveInputRoot_factor
    (i : E → C) (hi : Function.Injective i)
    {a m : ℕ}
    (r : Fin a → Fin m) (hr : Function.Surjective r)
    (root : Fin m → C) (args : Fin a → E)
    (h : root ∘ r = i ∘ args) :
    ∃ sourceRoot : Fin m → E,
      root = i ∘ sourceRoot ∧ args = sourceRoot ∘ r := by
  classical
  let sourceRoot : Fin m → E :=
    fun j => args (Classical.choose (hr j))
  have hRoot : root = i ∘ sourceRoot := by
    funext j
    change root j = i (sourceRoot j)
    change root j = i (args (Classical.choose (hr j)))
    calc
      root j = root (r (Classical.choose (hr j))) := by
        rw [Classical.choose_spec (hr j)]
      _ = i (args (Classical.choose (hr j))) :=
        congrFun h (Classical.choose (hr j))
  have hArgs : args = sourceRoot ∘ r := by
    funext k
    apply hi
    calc
      i (args k) = root (r k) := (congrFun h k).symm
      _ = i (sourceRoot (r k)) := congrFun hRoot (r k)
  exact ⟨sourceRoot, hRoot, hArgs⟩

end StructuralRamsey.Structure

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {H E F C : Type v}

/-- An ACTUAL full native functional free amalgam stays a
relational free amalgam on the SAME vertices when all functions
are represented by COMPLETE equality-pattern active-domain
and output-graph relations.

For an old active domain, native nonemptiness supplies a true
output and hFree.func_iff selects one side. Surjectivity of
the equality-pattern argument map then puts every distinct
root vertex on that side. An old output-graph tuple uses the
same argument and adds precisely that side's selected output.

The converse direction uses each FULL source-side
embedding's induced full pattern-graph embedding. -/
theorem patternGraph
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) :
    RelStructure.IsFreeAmalgam
      sL.patternGraph sR.patternGraph
      iL.patternGraph iR.patternGraph := by
  classical
  refine {
    covers := hFree.covers
    overlap := hFree.overlap
    rel_iff := ?_
  }
  intro R z
  rcases R with R | S
  · exact hFree.rel_iff R z
  rcases S with pat | pat
  · constructor
    · rintro ⟨hInj, ⟨out, hOut⟩⟩
      rcases (hFree.func_iff pat.symbol
          (z ∘ pat.argMap) out).mp hOut with
        ⟨a, b, hb, ha, _hout⟩ | ⟨a, b, hb, ha, _hout⟩
      · obtain ⟨root, hroot, hargs⟩ :=
          Structure.surjectiveInputRoot_factor
            iL iL.injective pat.argMap pat.onto z a ha
        have hinj : Function.Injective root := by
          intro j k hjk
          apply hInj
          calc
            z j = iL (root j) := congrFun hroot j
            _ = iL (root k) := congrArg iL hjk
            _ = z k := (congrFun hroot k).symm
        have hdefined : (Left.func pat.symbol
            (root ∘ pat.argMap)).Nonempty := by
          refine ⟨b, ?_⟩
          rw [← hargs]
          exact hb
        exact Or.inl ⟨root, ⟨hinj, hdefined⟩, hroot⟩
      · obtain ⟨root, hroot, hargs⟩ :=
          Structure.surjectiveInputRoot_factor
            iR iR.injective pat.argMap pat.onto z a ha
        have hinj : Function.Injective root := by
          intro j k hjk
          apply hInj
          calc
            z j = iR (root j) := congrFun hroot j
            _ = iR (root k) := congrArg iR hjk
            _ = z k := (congrFun hroot k).symm
        have hdefined : (Right.func pat.symbol
            (root ∘ pat.argMap)).Nonempty := by
          refine ⟨b, ?_⟩
          rw [← hargs]
          exact hb
        exact Or.inr ⟨root, ⟨hinj, hdefined⟩, hroot⟩
    · rintro (⟨w, hw, hz⟩ | ⟨w, hw, hz⟩)
      · rw [hz]
        exact (iL.patternGraph.map_rel_iff (.inr (.inl pat)) w).mpr hw
      · rw [hz]
        exact (iR.patternGraph.map_rel_iff (.inr (.inl pat)) w).mpr hw
  · constructor
    · rintro ⟨hInj, hOut⟩
      let x : Fin pat.rootSize → C := fun j => z j.castSucc
      let y : C := z (Fin.last pat.rootSize)
      have hNative : y ∈ Whole.func pat.symbol
          (x ∘ pat.argMap) := hOut
      rcases (hFree.func_iff pat.symbol
          (x ∘ pat.argMap) y).mp hNative with
        ⟨a, b, hb, ha, hy⟩ | ⟨a, b, hb, ha, hy⟩
      · obtain ⟨root, hroot, hargs⟩ :=
          Structure.surjectiveInputRoot_factor
            iL iL.injective pat.argMap pat.onto x a ha
        have hinj : Function.Injective root := by
          intro j k hjk
          apply hInj
          calc
            x j = iL (root j) := congrFun hroot j
            _ = iL (root k) := congrArg iL hjk
            _ = x k := (congrFun hroot k).symm
        let w : Fin (pat.rootSize + 1) → E :=
          Structure.funcTuple root b
        have hw : (Left.patternGraph).rel (.inr (.inr pat)) w := by
          change Function.Injective
              (fun j : Fin pat.rootSize => w j.castSucc) ∧
            w (Fin.last pat.rootSize) ∈
              Left.func pat.symbol
                ((fun j : Fin pat.rootSize => w j.castSucc) ∘ pat.argMap)
          simpa only [w, Structure.funcTuple_castSucc,
            Structure.funcTuple_last] using
            (show Function.Injective root ∧
                b ∈ Left.func pat.symbol (root ∘ pat.argMap)
              from ⟨hinj, by rw [← hargs]; exact hb⟩)
        have hz : z = iL ∘ w := by
          funext j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · change y = iL (w (Fin.last pat.rootSize))
            simpa only [w, Structure.funcTuple_last] using hy
          · change x k = iL (w k.castSucc)
            simpa only [w, Structure.funcTuple_castSucc,
              Function.comp_apply] using (congrFun hroot k)
        exact Or.inl ⟨w, hw, hz⟩
      · obtain ⟨root, hroot, hargs⟩ :=
          Structure.surjectiveInputRoot_factor
            iR iR.injective pat.argMap pat.onto x a ha
        have hinj : Function.Injective root := by
          intro j k hjk
          apply hInj
          calc
            x j = iR (root j) := congrFun hroot j
            _ = iR (root k) := congrArg iR hjk
            _ = x k := (congrFun hroot k).symm
        let w : Fin (pat.rootSize + 1) → F :=
          Structure.funcTuple root b
        have hw : (Right.patternGraph).rel (.inr (.inr pat)) w := by
          change Function.Injective
              (fun j : Fin pat.rootSize => w j.castSucc) ∧
            w (Fin.last pat.rootSize) ∈
              Right.func pat.symbol
                ((fun j : Fin pat.rootSize => w j.castSucc) ∘ pat.argMap)
          simpa only [w, Structure.funcTuple_castSucc,
            Structure.funcTuple_last] using
            (show Function.Injective root ∧
                b ∈ Right.func pat.symbol (root ∘ pat.argMap)
              from ⟨hinj, by rw [← hargs]; exact hb⟩)
        have hz : z = iR ∘ w := by
          funext j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · change y = iR (w (Fin.last pat.rootSize))
            simpa only [w, Structure.funcTuple_last] using hy
          · change x k = iR (w k.castSucc)
            simpa only [w, Structure.funcTuple_castSucc,
              Function.comp_apply] using (congrFun hroot k)
        exact Or.inr ⟨w, hw, hz⟩
    · rintro (⟨w, hw, hz⟩ | ⟨w, hw, hz⟩)
      · rw [hz]
        exact (iL.patternGraph.map_rel_iff (.inr (.inr pat)) w).mpr hw
      · rw [hz]
        exact (iR.patternGraph.map_rel_iff (.inr (.inr pat)) w).mpr hw

/-- Combining the ACTUAL native free function diagram with the
generic full-root canonical tag free-amalgam lemma provides
the exact full 2019 U-pattern source free-amalgam diagram.

All four source maps are FULL on the native function side
and on the canonical tagged side; no vertices or function
closure points are added. -/
theorem taggedPatternGraph
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) :
    RelStructure.IsFreeAmalgam
      (sL.patternGraph).patternTag
      (sR.patternGraph).patternTag
      (iL.patternGraph).patternTag
      (iR.patternGraph).patternTag :=
  hFree.patternGraph.patternTagExpansion

end StructuralRamsey.Structure.IsFreeAmalgam
