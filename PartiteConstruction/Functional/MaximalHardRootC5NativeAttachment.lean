import PartiteConstruction.Functional.MaximalHardRootFiveCycleFixture
import PartiteConstruction.Functional.EHNAttachmentDecompose
import PartiteConstruction.Iterated.OddCycleEdgeTreeObstruction

/-!
# Five-cycle in one actual binary native functional EHN attachment

The old and core forest partite systems and full closed-support map
are verified finite data. In the function-free graph instance, the
ACTUAL FunctionalPartite.Attachment.UnitAttachD is a native functional
partite system, rather than a separately chosen relational free amalgam.

We exhibit its five cyclic edges with full core/copy embeddings,
overlap equalities, and five different control part labels. This
certifies a non-two-colourable attached partite graph and its exact
five-vertex mixed cycle test, once the label-injectivity proof is
complete. The actual core used here still is NOT the genuine HJ
selected-support power (it has a vertex in part 1, outside {0,3}),
so do not infer failure of the history-restricted Picture theorem.

No nonclosed source weak test is replaced by a generated hull.
-/

namespace StructuralRamsey.Structure.MaximalHardRootFiveCycle

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite

noncomputable section

/-- One genuine native FUNCTIONAL-partite EHN binary attachment. -/
abbrev nativeAttached :=
  FunctionalPartite.Attachment.UnitAttachD
    oldSystem support support_closed coreSystem supportPartiteEmbedding

/-- The actual native vertex carrier for this attachment. -/
abbrev NativeVertex :=
  FunctionalPartite.Attachment.Vertex support (W := Fin 5) (I := PUnit.{1})

/-- Full part-respecting core embedding. -/
def nativeCore : FunctionalPartite.Embedding coreSystem nativeAttached :=
  FunctionalPartite.Attachment.coreEmbedding
    oldSystem support support_closed coreSystem
    (fun _ : PUnit.{1} => supportPartiteEmbedding)

/-- Full part-respecting attached OLD-copy embedding. -/
def nativeCopy : FunctionalPartite.Embedding oldSystem nativeAttached :=
  FunctionalPartite.Attachment.copyEmbedding
    oldSystem support support_closed coreSystem
    (fun _ : PUnit.{1} => supportPartiteEmbedding) PUnit.unit

/-- In the native copy, old a0 and a3 are identified with
core c0 and c3 exactly, not with extra closure vertices. -/
theorem native_overlap_a0 : nativeCore 0 = nativeCopy 0 := by
  have hs : (0 : Fin 6) ∈ support := by
    simp [support]
  have h := FunctionalPartite.Attachment.copy_extends
    oldSystem support support_closed coreSystem
    (fun _ : PUnit.{1} => supportPartiteEmbedding) PUnit.unit
    (⟨0,hs⟩ : support)
  simpa [nativeCore,nativeCopy,supportPartiteEmbedding,
    supportEmbedding,supportMap] using h.symm

theorem native_overlap_a3 : nativeCore 2 = nativeCopy 3 := by
  have hs : (3 : Fin 6) ∈ support := by
    simp [support]
  have h := FunctionalPartite.Attachment.copy_extends
    oldSystem support support_closed coreSystem
    (fun _ : PUnit.{1} => supportPartiteEmbedding) PUnit.unit
    (⟨3,hs⟩ : support)
  simpa [nativeCore,nativeCopy,supportPartiteEmbedding,
    supportEmbedding,supportMap] using h.symm

/-- An edge is an ordinary binary relation tuple in the actual
native functional attachment. -/
def nativeEdge (a b : NativeVertex) : Prop :=
  nativeAttached.toStructure.rel ()
    (fun k : Fin 2 => if k = 0 then a else b)

/-- The core and the attached copy retain their OLD edge relations
without changing the endpoints or projecting to a closure hull. -/
theorem nativeEdge_core (a b : Fin 5) (h : coreEdge a b) :
    nativeEdge (nativeCore a) (nativeCore b) := by
  let tup : Fin 2 → Fin 5 := fun k => if k = 0 then a else b
  have hsource : core.rel () tup := by
    change coreEdge (tup 0) (tup 1)
    simpa [tup] using h
  have hmap : nativeAttached.toStructure.rel ()
      (nativeCore ∘ tup) :=
    (nativeCore.toEmbedding.map_rel_iff () tup).mpr hsource
  have heq : (nativeCore ∘ tup) =
      (fun k : Fin 2 =>
        if k = 0 then nativeCore a else nativeCore b) := by
    funext k
    by_cases hk : k = 0 <;> simp [tup,hk]
  change nativeAttached.toStructure.rel ()
    (fun k : Fin 2 =>
      if k = 0 then nativeCore a else nativeCore b)
  exact heq ▸ hmap

theorem nativeEdge_old (a b : Fin 6) (h : oldEdge a b) :
    nativeEdge (nativeCopy a) (nativeCopy b) := by
  let tup : Fin 2 → Fin 6 := fun k => if k = 0 then a else b
  have hsource : old.rel () tup := by
    change oldEdge (tup 0) (tup 1)
    simpa [tup] using h
  have hmap : nativeAttached.toStructure.rel ()
      (nativeCopy ∘ tup) :=
    (nativeCopy.toEmbedding.map_rel_iff () tup).mpr hsource
  have heq : (nativeCopy ∘ tup) =
      (fun k : Fin 2 =>
        if k = 0 then nativeCopy a else nativeCopy b) := by
    funext k
    by_cases hk : k = 0 <;> simp [tup,hk]
  exact heq ▸ hmap

/-- The actual five cyclic vertices c0,d1,c3,b2,b4. -/
def nativeCycle : Fin 5 → NativeVertex
  | 0 => nativeCore 0
  | 1 => nativeCore 1
  | 2 => nativeCore 2
  | 3 => nativeCopy 2
  | 4 => nativeCopy 1

/-- Their control parts 0,1,3,2,4 are pairwise distinct. -/
def nativeCyclePart : Fin 5 → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2
  | 4 => 4

theorem nativeCycle_part (i : Fin 5) :
    nativeAttached.part (nativeCycle i) = nativeCyclePart i := by
  fin_cases i
  · simpa [nativeCycle,nativeCyclePart,coreSystem,corePart] using
      nativeCore.map_part (0 : Fin 5)
  · simpa [nativeCycle,nativeCyclePart,coreSystem,corePart] using
      nativeCore.map_part (1 : Fin 5)
  · simpa [nativeCycle,nativeCyclePart,coreSystem,corePart] using
      nativeCore.map_part (2 : Fin 5)
  · simpa [nativeCycle,nativeCyclePart,oldSystem,oldPart] using
      nativeCopy.map_part (2 : Fin 6)
  · simpa [nativeCycle,nativeCyclePart,oldSystem,oldPart] using
      nativeCopy.map_part (1 : Fin 6)

theorem nativeCyclePart_injective : Function.Injective nativeCyclePart := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [nativeCyclePart]

theorem nativeCycle_injective : Function.Injective nativeCycle := by
  intro i j h
  apply nativeCyclePart_injective
  calc
    nativeCyclePart i = nativeAttached.part (nativeCycle i) :=
      (nativeCycle_part i).symm
    _ = nativeAttached.part (nativeCycle j) := congrArg nativeAttached.part h
    _ = nativeCyclePart j := nativeCycle_part j

/-- In the FUNCTION-FREE native language this five-vertex test is
closed under all functions, vacuously. No additional hull vertices. -/
def nativeCycleSet : Set NativeVertex := Set.range nativeCycle

theorem nativeCycleSet_closed :
    nativeAttached.toStructure.IsClosed nativeCycleSet := by
  intro F
  exact Empty.elim F

/-- The five vertices project bijectively to ALL five different
control parts, so the maximal projected-image case has no collision. -/
theorem nativeCycle_projected_parts :
    nativeAttached.part '' nativeCycleSet = (Set.univ : Set (Fin 5)) := by
  ext p
  constructor
  · intro _
    exact Set.mem_univ p
  · intro _
    have hOnto : Function.Surjective nativeCyclePart := by decide
    obtain ⟨i,hi⟩ := hOnto p
    refine ⟨nativeCycle i,⟨i,rfl⟩,?_⟩
    exact (nativeCycle_part i).trans hi

/-- The genuine native attached graph cannot be properly two-coloured:
its OLD and CORE full embeddings form a five-edge odd cycle. -/
theorem nativeAttached_not_twoColorable :
    ¬ ∃ c : NativeVertex → Bool,
      ∀ xs : Fin 2 → NativeVertex,
        nativeAttached.toStructure.rel () xs →
          c (xs 0) ≠ c (xs 1) := by
  rintro ⟨c,hc⟩
  have edgeColor (a b : NativeVertex)
      (h : nativeEdge a b) : c a ≠ c b := by
    have h' := hc (fun k : Fin 2 => if k = 0 then a else b) h
    simpa using h'
  have h01 : c (nativeCore 0) ≠ c (nativeCore 1) :=
    edgeColor _ _ (nativeEdge_core 0 1 (by simp [coreEdge]))
  have h12 : c (nativeCore 1) ≠ c (nativeCore 2) :=
    edgeColor _ _ (nativeEdge_core 1 2 (by simp [coreEdge]))
  have h23 : c (nativeCore 2) ≠ c (nativeCopy 2) := by
    rw [native_overlap_a3]
    exact edgeColor _ _ (nativeEdge_old 3 2 (by simp [oldEdge]))
  have h34 : c (nativeCopy 2) ≠ c (nativeCopy 1) :=
    edgeColor _ _ (nativeEdge_old 2 1 (by simp [oldEdge]))
  have h40 : c (nativeCopy 1) ≠ c (nativeCore 0) := by
    rw [native_overlap_a0]
    exact edgeColor _ _ (nativeEdge_old 1 0 (by simp [oldEdge]))
  have h02 : c (nativeCore 0) = c (nativeCore 2) :=
    RelStructure.LooseNotStrictifiable.bool_eq_of_ne_ne h01 h12
  have h24 : c (nativeCore 2) = c (nativeCopy 1) :=
    RelStructure.LooseNotStrictifiable.bool_eq_of_ne_ne h23 h34
  exact h40 (h02.trans h24).symm

end

end StructuralRamsey.Structure.MaximalHardRootFiveCycle
