import PartiteConstruction.Partite.Basic

/-! # Initial pictures

A disjoint copy of B is placed along every member of a prescribed family of
injective projections. This is the initial picture in Appendix A. The family
can later be restricted, for example to increasing projections.
-/
namespace StructuralRamsey.Partite.Initial

universe u v w z
variable {L : RelLanguage.{u}} {P : Type v} {V : Type w} {I : Type z}
variable (B : RelStructure L V) (β : I → V ↪ P)

def picture : System L P (I × V) where
  rel R z := ∃ i x, B.rel R x ∧ z = (fun v => (i, v)) ∘ x
  part iv := β iv.1 iv.2
  transversal R z hz k l hkl := by
    obtain ⟨i, x, hx, rfl⟩ := hz
    exact congrArg (fun v => (i, v)) ((β i).injective hkl)

def copyEmbedding (i : I) : RelStructure.Embedding B (picture B β).toRelStructure where
  toFun v := (i, v)
  injective _ _ h := congrArg Prod.snd h
  map_rel_iff R x := by
    constructor
    · rintro ⟨j, y, hy, h⟩
      have heq : x = y := funext (fun k => congrArg Prod.snd (congrFun h k))
      simpa only [heq] using hy
    · intro hx
      exact ⟨i, x, hx, rfl⟩

@[simp] theorem copy_part (i : I) (v : V) :
    (picture B β).part (copyEmbedding B β i v) = β i v := rfl

end StructuralRamsey.Partite.Initial
