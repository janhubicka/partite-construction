import PartiteConstruction.Functional.WholeMaskClosureTags2019

/-!
# Extract the full old root of an active complete-value mask

An active mask domain on a distinct input-root enumeration determines
a FULL old root pattern by pulling back every old relation. The original
enumeration is then literally a full relational embedding of this root.
This reuses the exact vertices and does not create a closure hull.

For genuine partial set-valued structures, the active output mask SET
on each fixed function input is unique. The current finite language
admits several orders of the same mask; equality of mask SETS is what
is justified, not equality of their ordered enumerations in an
arbitrary tagged target. Target coherence requires a further invariant.
-/

namespace StructuralRamsey

universe u v w

namespace Language.WholeMaskRootPattern

variable {L : Language.{u}} {P : Type v} {V : Type w}
variable [Fintype P]

/-- Pull back ALL OLD relations, including domain masks and internal
complete-value graph tuples, along the literal distinct input list. -/
def ofActiveDomain
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (input : FunctionInputPattern L)
    (mask : CompleteOutputParts P)
    (hInput : 0 < input.rootSize)
    (hMask : 0 < mask.size)
    (e : Fin input.rootSize → V)
    (hDomain : E.rel (.inr (.inl (input, mask))) e) :
    WholeMaskRootPattern L P where
  input := input
  mask := mask
  rootPositive := hInput
  outputPositive := hMask
  root := {rel := fun R xs => E.rel R (e ∘ xs)}
  hasDomain := by
    change E.rel (.inr (.inl (input, mask))) (e ∘ id)
    simpa only [Function.comp_id] using hDomain

/-- The root extraction carries a literal FULL OLD embedding. Its
carrier consists of exactly the given distinct function-input
vertices, not their generated closure. -/
def ofActiveDomain_embedding
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (input : FunctionInputPattern L)
    (mask : CompleteOutputParts P)
    (hInput : 0 < input.rootSize)
    (hMask : 0 < mask.size)
    (e : Fin input.rootSize → V)
    (hInj : Function.Injective e)
    (hDomain : E.rel (.inr (.inl (input, mask))) e) :
    RelStructure.Embedding
      (ofActiveDomain E input mask hInput hMask e hDomain).root E where
  toFun := e
  injective := hInj
  map_rel_iff := by
    intro R xs
    rfl

end Language.WholeMaskRootPattern

namespace PartialSetStructure

variable {L : Language.{u}} {P : Type v} {V : Type w}
variable [Fintype P]

/-- A genuinely partial operation has one complete output-part SET
on a fixed input tuple. Distinct ordered enumerations of that same
set are permitted, but two different sets cannot both be active. -/
theorem wholeMaskPatternGraph_domain_mask_set_unique
    (A : PartialSetStructure L V) (part : V → P)
    (input : Language.FunctionInputPattern L)
    (q₁ q₂ : Language.CompleteOutputParts P)
    (root : Fin input.rootSize → V)
    (h₁ : (A.wholeMaskPatternGraph part).rel
      (.inr (.inl (input, q₁))) root)
    (h₂ : (A.wholeMaskPatternGraph part).rel
      (.inr (.inl (input, q₂))) root) :
    Set.range q₁.label = Set.range q₂.label := by
  change Function.Injective root ∧
      ∃ U : Set V, A.func input.symbol (root ∘ input.argMap) = some U ∧
        part '' U = Set.range q₁.label at h₁
  change Function.Injective root ∧
      ∃ U : Set V, A.func input.symbol (root ∘ input.argMap) = some U ∧
        part '' U = Set.range q₂.label at h₂
  obtain ⟨_, U₁, hVal₁, hMask₁⟩ := h₁
  obtain ⟨_, U₂, hVal₂, hMask₂⟩ := h₂
  have hEq : U₁ = U₂ :=
    Option.some.inj (hVal₁.symm.trans hVal₂)
  calc
    Set.range q₁.label = part '' U₁ := hMask₁.symm
    _ = part '' U₂ := by rw [hEq]
    _ = Set.range q₂.label := hMask₂

end PartialSetStructure
end StructuralRamsey
