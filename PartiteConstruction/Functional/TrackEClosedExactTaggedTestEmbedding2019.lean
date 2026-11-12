import PartiteConstruction.Functional.TrackEExactInducedDomainReflection2019
import PartiteConstruction.Functional.WholeMaskCoveredExactWeakLocalMap2019
import PartiteConstruction.Structure.PartialSetFunctionsClosure

/-!
# Track E: a full tagged exact test gives a FULL functional copy when closed

The corrected two-pass 2019 source is not assumed canonical in the OLD
complete-mask language. Nevertheless, on an exact vertex set S that is
genuinely CLOSED in its decoded Option(Set) structure, a FULL embedding
of the tagged INDUCED restriction of the actual final covered witness
into a canonical target induces a FULL partial-function embedding.

The source-defined whole-value law comes from the verified exact-weak
OLD-to-partial homomorphism. Domain reflection is obtained by the Track E
literal induced-domain mask lemma. Closedness prevents the whole-fibre
weak restriction from losing a formerly defined operation. Primitive
relations reflect because the tagged test map is FULL.

This theorem does NOT supply the full tagged test embedding itself,
or prove that every native irreducible full test is U-closed and
U-irreducible inside the final tagged witness. It supplies a smaller
closing interface than requiring an exact canonical-tagged E lift.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure

universe u v w z
variable {L : Language.{u}} {P : Type z} [Fintype P]
variable {V Q : Type v} {W : Type w}

/-- An actual final B-covered tagged source has a full genuine partial
function embedding on every exact decoded-function-CLOSED vertex set
S for which the tagged induced source has a FULL embedding into the
canonical target. The map, parts and vertex sets are not changed.

No source canonicalization, global domain reflection of a partial
projection, or strict full-functional tree is assumed. -/
noncomputable def wholeMaskCovered_closedExactTaggedTest_toPartialEmbedding
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L Q) (basePart : Q → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph basePart))))
    (S : Set V)
    (hClosed : ((wholeMaskTagReduct C).wholeMaskPartialDecode).IsClosed S)
    (Target : PartialSetStructure L W) [Finite W]
    (part : W → P)
    (hTrans : PartialSetStructure.FibreTransversal Target part)
    (g : Embedding (C.induce S)
      (wholeMaskTagExpansion (Target.wholeMaskPatternGraph part))) :
    PartialSetStructure.Embedding
      (PartialSetStructure.wholeWeakInduce
        ((wholeMaskTagReduct C).wholeMaskPartialDecode) S) Target := by
  classical
  let A : PartialSetStructure L V :=
    (wholeMaskTagReduct C).wholeMaskPartialDecode
  have hOldHom :
      ((wholeMaskTagReduct C).induce S).IsHomomorphism
        (Target.wholeMaskPatternGraph part) g := by
    intro R xs hR
    exact (g.map_rel_iff (.inl R) xs).mpr hR
  have hPartial :
      PartialSetStructure.IsOriginalPartialHomomorphism
        (PartialSetStructure.wholeWeakInduce A S) Target g :=
    wholeMaskPartialDecode_weak_originalPartial_of_coveredOldHom
      C Base basePart hC hPos hCover S Target part g hOldHom
  have hDomain (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → S) :
      A.Defined F (Subtype.val ∘ xs) ↔
        Target.Defined F (g ∘ xs) :=
    wholeMaskCovered_defined_iff_of_exact_tagged_embedding
      C Base basePart hC hPos hCover Target part hTrans S g F xs
  refine {
    toFun := g
    injective := g.injective
    map_rel_iff := ?_
    map_func := ?_
  }
  · intro R xs
    exact g.map_rel_iff (.inl (.inl R)) xs
  · intro F xs
    cases hValue :
      (PartialSetStructure.wholeWeakInduce A S).func F xs with
    | none =>
        have hAmbientNot : ¬ A.Defined F (Subtype.val ∘ xs) := by
          rintro ⟨T, hT⟩
          have hTS : T ⊆ S :=
            hClosed F (Subtype.val ∘ xs) T
              (fun i => (xs i).2) hT
          have hWeakValue :
              (PartialSetStructure.wholeWeakInduce A S).func F xs =
                some {z : S | z.1 ∈ T} := by
            change PartialSetStructure.wholeWeakValue S
              (A.func F (Subtype.val ∘ xs)) = _
            rw [hT]
            exact PartialSetStructure.wholeWeakValue_of_subset S T hTS
          rw [hValue] at hWeakValue
          cases hWeakValue
        have hTargetNot : ¬ Target.Defined F (g ∘ xs) := by
          intro hTarget
          exact hAmbientNot ((hDomain F xs).mpr hTarget)
        cases hTarget : Target.func F (g ∘ xs) with
        | none =>
            simpa only [hValue, Option.map_none, hTarget]
        | some T =>
            exact (hTargetNot ⟨T, hTarget⟩).elim
    | some T =>
        have hTarget :
            Target.func F (g ∘ xs) =
              some (Structure.imageSet g T) :=
          hPartial.2 F xs T hValue
        simpa only [hValue, Option.map_some] using hTarget.symm

end StructuralRamsey.RelStructure
