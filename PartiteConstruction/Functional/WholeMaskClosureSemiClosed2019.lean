import PartiteConstruction.Functional.WholeMaskClosureTags2019
import PartiteConstruction.Ramsey.ClosureSemiClosed2019
import PartiteConstruction.Structure.PartialSetFunctionsTransversal

/-!
# Canonical whole-value tagged sources are U-semi-closed

The fresh complete-value closure tags use FULL induced OLD input-root
patterns, with separate persistent activation relations. Every tag
therefore has a valid tagged root. If the underlying function outputs
are transversal by parts, two complete-value tuples of the SAME output
part pattern over the same input root must coincide coordinatewise.
Thus the canonical source is U-semi-closed; arbitrary weak vertex
restrictions inherit this property.

This is partial uniqueness and root validity, not the existence part
of U-closedness. The target completion/normalization problem remains open.
-/

namespace StructuralRamsey

open StructuralRamsey.RelStructure

universe u v w z

namespace RelStructure.Embedding

variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V : Type w} {W : Type z}
variable {E : RelStructure (L.wholeMaskPatternLanguage P) V}
variable {F : RelStructure (L.wholeMaskPatternLanguage P) W}

/-- A full embedding of the OLD complete-mask relational structures
lifts to a full embedding of their canonical FULL-root tagged sources.
No active root tags are recomputed from clipped function fibres. -/
noncomputable def wholeMaskTag (f : Embedding E F) :
    Embedding (wholeMaskTagExpansion E) (wholeMaskTagExpansion F) where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    intro R xs
    rcases R with R | p
    · exact f.map_rel_iff R xs
    · change
        (F.rel (.inr (.inr (p.input, p.mask))) (f ∘ xs) ∧
          ∃ g : Embedding p.root F,
            ∀ i : Fin p.input.rootSize,
              (f ∘ xs) (Fin.castAdd p.mask.size i) = g i) ↔
        (E.rel (.inr (.inr (p.input, p.mask))) xs ∧
          ∃ g : Embedding p.root E,
            ∀ i : Fin p.input.rootSize,
              xs (Fin.castAdd p.mask.size i) = g i)
      constructor
      · rintro ⟨hOldF, gF, hPrefixF⟩
        have hOldE : E.rel (.inr (.inr (p.input, p.mask))) xs :=
          (f.map_rel_iff (.inr (.inr (p.input, p.mask))) xs).mp hOldF
        let q : Fin p.input.rootSize → V :=
          fun i => xs (Fin.castAdd p.mask.size i)
        let gE : Embedding p.root E := {
          toFun := q
          injective := by
            intro i j hij
            apply gF.injective
            calc
              gF i = f (q i) := (hPrefixF i).symm
              _ = f (q j) := congrArg f hij
              _ = gF j := hPrefixF j
          map_rel_iff := by
            intro S ys
            have hEq : f ∘ (q ∘ ys) = gF ∘ ys := by
              funext i
              exact hPrefixF (ys i)
            calc
              E.rel S (q ∘ ys) ↔ F.rel S (f ∘ (q ∘ ys)) :=
                (f.map_rel_iff S (q ∘ ys)).symm
              _ ↔ F.rel S (gF ∘ ys) := by rw [hEq]
              _ ↔ p.root.rel S ys := gF.map_rel_iff S ys
        }
        exact ⟨hOldE, gE, fun _ => rfl⟩
      · rintro ⟨hOldE, gE, hPrefixE⟩
        have hOldF : F.rel (.inr (.inr (p.input, p.mask))) (f ∘ xs) :=
          (f.map_rel_iff (.inr (.inr (p.input, p.mask))) xs).mpr hOldE
        refine ⟨hOldF, f.comp gE, ?_⟩
        intro i
        exact congrArg f (hPrefixE i)

/-- Forgetting all fresh tags from a full tagged embedding recovers the
full OLD relational embedding, including domain-mask reflection. -/
def wholeMaskTagReduct
    {A : RelStructure (L.wholeMaskTagLanguage P) V}
    {B : RelStructure (L.wholeMaskTagLanguage P) W}
    (f : Embedding A B) :
    Embedding (wholeMaskTagReduct A) (wholeMaskTagReduct B) where
  toFun := f
  injective := f.injective
  map_rel_iff := fun R xs => f.map_rel_iff (.inl R) xs

end RelStructure.Embedding

namespace PartialSetStructure

variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V : Type w}

/-- Transversality makes each output coordinate uniquely determined by
its named part and the complete value set, even if the root has repeated
primitive input arguments or outputs coincide with input vertices. -/
theorem wholeMaskPatternGraph_unique_outputs
    (A : PartialSetStructure L V) (part : V → P)
    (hTrans : FibreTransversal A part)
    (p : Language.FunctionInputPattern L)
    (q : Language.CompleteOutputParts P)
    (t₁ t₂ : Fin (p.rootSize + q.size) → V)
    (ht₁ : (A.wholeMaskPatternGraph part).rel (.inr (.inr (p,q))) t₁)
    (ht₂ : (A.wholeMaskPatternGraph part).rel (.inr (.inr (p,q))) t₂)
    (hRoot : ∀ i : Fin p.rootSize,
      t₁ (Fin.castAdd q.size i) = t₂ (Fin.castAdd q.size i)) :
    t₁ = t₂ := by
  let inp₁ : Fin p.rootSize → V := fun i => t₁ (Fin.castAdd q.size i)
  let inp₂ : Fin p.rootSize → V := fun i => t₂ (Fin.castAdd q.size i)
  let out₁ : Fin q.size → V := fun i => t₁ (Fin.natAdd p.rootSize i)
  let out₂ : Fin q.size → V := fun i => t₂ (Fin.natAdd p.rootSize i)
  have hInp : inp₁ = inp₂ := funext hRoot
  have hv₁ : A.func p.symbol (inp₁ ∘ p.argMap) =
      some (Set.range out₁) := ht₁.2.1
  have hv₂ : A.func p.symbol (inp₂ ∘ p.argMap) =
      some (Set.range out₂) := ht₂.2.1
  have hValue : Set.range out₁ = Set.range out₂ :=
    Option.some.inj
      (hv₁.symm.trans
        ((congrArg (fun v => A.func p.symbol (v ∘ p.argMap)) hInp).trans hv₂))
  have hOut : ∀ j : Fin q.size, out₁ j = out₂ j := by
    intro j
    have hy : out₁ j ∈ Set.range out₁ := ⟨j,rfl⟩
    have hz : out₂ j ∈ Set.range out₁ := by
      rw [hValue]
      exact ⟨j,rfl⟩
    have hp : part (out₁ j) = part (out₂ j) :=
      (ht₁.2.2 j).trans (ht₂.2.2 j).symm
    exact hTrans p.symbol (inp₁ ∘ p.argMap)
      (Set.range out₁) hv₁ (out₁ j) hy (out₂ j) hz hp
  funext k
  exact Fin.addCases (fun i => hRoot i) (fun j => hOut j) k

/-- Canonical whole-mask tags satisfy the partial uniqueness/root-validity
axiom of the 2019 U-semi-closed formalism. Domain activation remains
ambient and is not inferred from weakly clipped outputs. -/
theorem wholeMaskTagExpansion_isUSemiClosed
    (A : PartialSetStructure L V) (part : V → P)
    (hTrans : FibreTransversal A part) :
    IsUSemiClosed (L.wholeMaskClosureRules P)
      (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)) := by
  intro rule hrule
  obtain ⟨p, rfl⟩ := hrule
  constructor
  · intro t ht
    change (A.wholeMaskPatternGraph part).rel
        (.inr (.inr (p.input,p.mask))) t ∧
      ∃ e : RelStructure.Embedding p.root (A.wholeMaskPatternGraph part),
        ∀ i : Fin p.input.rootSize,
          t (Fin.castAdd p.mask.size i) = e i at ht
    obtain ⟨_,e,he⟩ := ht
    exact ⟨e.wholeMaskTag, he⟩
  · intro t₁ t₂ ht₁ ht₂ hRoot
    have hOld₁ : (A.wholeMaskPatternGraph part).rel
        (.inr (.inr (p.input,p.mask))) t₁ := ht₁.1
    have hOld₂ : (A.wholeMaskPatternGraph part).rel
        (.inr (.inr (p.input,p.mask))) t₂ := ht₂.1
    have hPrefix : ∀ i : Fin p.input.rootSize,
        t₁ (Fin.castAdd p.mask.size i) =
          t₂ (Fin.castAdd p.mask.size i) := by
      intro i
      have hIdx :
          i.castLE p.closureRule.rootLE =
            Fin.castAdd p.mask.size i := by
        apply Fin.ext
        rfl
      rw [← hIdx]
      exact hRoot i
    exact A.wholeMaskPatternGraph_unique_outputs part hTrans
      p.input p.mask t₁ t₂ hOld₁ hOld₂ hPrefix

end PartialSetStructure
end StructuralRamsey
