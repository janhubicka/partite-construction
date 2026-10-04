import PartiteConstruction.Functional.WeakAttachment

/-! # Finite class-preserving functional stages

Finite star attachment is iterated binary free amalgamation. This is the
geometric attachment inside one Picture step, not another Ramsey pass.
-/
namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}} {P V I : Type v}

structure Stage (K : Structure.StructureClass (L := L)) (D : Structure L P) where
  Carrier : Type v
  finiteCarrier : Finite Carrier
  system : System L P Carrier
  over : system.WeaklyPartiteOver D
  mem : K system.toStructure

attribute [instance] Stage.finiteCarrier

variable {K : Structure.StructureClass (L := L)} {D : Structure L P}

noncomputable def Stage.attach
    (T : Stage K D) (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (f : FunctionalPartite.Embedding (B.induce S hS) T.system) : Stage K D where
  Carrier := Structure.Attachment.Vertex S (W := T.Carrier) (I := Unit)
  finiteCarrier := inferInstance
  system := FunctionalPartite.Attachment.attach B S hS T.system (fun _ : Unit => f)
  over := FunctionalPartite.Attachment.unit_weaklyPartiteOver B S hS T.system f D hB T.over
  mem := FunctionalPartite.Attachment.unit_mem B S hS T.system f hK hmB T.mem

/-- Attach a finite list of prescribed maps, retaining every earlier copy. -/
theorem attachList
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (E : Stage K D)
    (maps : I → FunctionalPartite.Embedding (B.induce S hS) E.system)
    (xs : List I) :
    ∃ T : Stage K D, ∃ core : FunctionalPartite.Embedding E.system T.system,
      ∀ i ∈ xs, ∃ copy : FunctionalPartite.Embedding B T.system,
        ∀ x : S, copy x.1 = core (maps i x) := by
  induction xs with
  | nil =>
      exact ⟨E, FunctionalPartite.Embedding.id E.system,
        fun _ h => (List.not_mem_nil h).elim⟩
  | cons i xs ih =>
      obtain ⟨T, core, hcopies⟩ := ih
      let f := core.comp (maps i)
      let R := T.attach hK B hB hmB S hS f
      let j : FunctionalPartite.Embedding T.system R.system :=
        FunctionalPartite.Attachment.coreEmbedding B S hS T.system (fun _ : Unit => f)
      let b : FunctionalPartite.Embedding B R.system :=
        FunctionalPartite.Attachment.copyEmbedding B S hS T.system (fun _ : Unit => f) ()
      refine ⟨R, j.comp core, ?_⟩
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · refine ⟨b, ?_⟩
        intro x
        exact FunctionalPartite.Attachment.copy_extends B S hS T.system
          (fun _ : Unit => f) () x
      · obtain ⟨copy, hc⟩ := hcopies k hk
        exact ⟨j.comp copy, fun x => congrArg j (hc x)⟩

/-- Finite star attachment with class membership and weak irreducible control. -/
theorem attachAll
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (E : Stage K D) [Finite I]
    (maps : I → FunctionalPartite.Embedding (B.induce S hS) E.system) :
    ∃ T : Stage K D, ∃ core : FunctionalPartite.Embedding E.system T.system,
      ∀ i, ∃ copy : FunctionalPartite.Embedding B T.system,
        ∀ x : S, copy x.1 = core (maps i x) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  obtain ⟨T, core, hc⟩ := attachList hK B hB hmB S hS E maps Finset.univ.toList
  exact ⟨T, core, fun i => hc i (by simp)⟩

/-- A power with a weak irreducible embedding projection into a class member
belongs to the class, by the finite irreducible member test. -/
theorem mem_of_weaklyPartiteOver
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hD : K D) : K B.toStructure := by
  apply hK.mem_of_irreducibles
  intro X _ E hE e
  obtain ⟨g, _⟩ := hB.2 E hE e
  exact hK.hereditary hD g

end StructuralRamsey.FunctionalPartite.EHN
