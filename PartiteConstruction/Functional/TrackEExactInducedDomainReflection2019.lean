import PartiteConstruction.Functional.WholeMaskCoveredPartialDecoding2019
import PartiteConstruction.Functional.WholeMaskOldEmbeddingTransport2019

/-!
# Track E: domain reflection on exact induced tagged tests

An OLD complete-mask active domain relation has only input-root vertices.
Every such root lies in the original primitive arguments, even for repeated
arguments and nullary functions. Thus OLD-domain activation commutes with
restriction to an EXACT induced vertex subset; unlike weak native clipping,
the ambient OLD domain mask is not recomputed from the surviving outputs.

If the final covered tagged target has exact OLD domain decoding, a FULL
tagged embedding of its exact induced test into a canonical control target
REFLECTS definedness on that test. The same map and every original test
vertex are retained. We do NOT infer that every native irreducible test
is a closed U-irreducible test, or claim an unconditional global native HE.
-/

namespace StructuralRamsey.RelStructure

universe u v w z
variable {L : Language.{u}} {P : Type z} [Fintype P]
variable {V Q : Type v} {W : Type w}

/-- Domain masks survive exact induction iff their literal primitive
argument tuple lies in the induced carrier. The reverse direction uses
surjectivity of the input equality-pattern's root enumeration, not a
generated closure hull. -/
theorem hasWholeMaskDomain_induce_iff
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (S : Set V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S) :
    HasWholeMaskDomain (E.induce S) F xs ↔
      HasWholeMaskDomain E F (Subtype.val ∘ xs) := by
  classical
  constructor
  · rintro ⟨m, r, hr, q, root, hDomain, hArgs⟩
    refine ⟨m, r, hr, q, Subtype.val ∘ root, hDomain, ?_⟩
    intro i
    exact congrArg Subtype.val (hArgs i)
  · rintro ⟨m, r, hr, q, root, hDomain, hArgs⟩
    let rootS : Fin m → S := fun j => ⟨root j, by
      obtain ⟨i, hi⟩ := hr j
      have hArg : (xs i).1 = root (r i) := hArgs i
      rw [← hi, ← hArg]
      exact (xs i).2⟩
    have hDomainS :
        (E.induce S).rel
          (.inr (.inl
            ((⟨F, m, r, hr⟩ : Language.FunctionInputPattern L), q)))
          rootS := by
      change E.rel
        (.inr (.inl
          ((⟨F, m, r, hr⟩ : Language.FunctionInputPattern L), q)))
        (Subtype.val ∘ rootS)
      have hRootComp : (Subtype.val ∘ rootS) = root := by
        funext j
        rfl
      simpa only [hRootComp] using hDomain
    refine ⟨m, r, hr, q, rootS, hDomainS, ?_⟩
    intro i
    apply Subtype.ext
    exact hArgs i

/-- Once OLD-domain activation agrees with the decoded partial domain,
a full tagged embedding of the ACTUAL induced test into a canonical
control target reflects domains of all primitive functions, on the
same literal argument vertices. No source or target hull is used. -/
theorem wholeMaskDecoded_defined_iff_of_exact_tagged_embedding
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (hDomain : ∀ (F : L.FuncSymbol)
        (x : Fin (L.funcArity F) → V),
      (wholeMaskTagReduct C).wholeMaskPartialDecode.Defined F x ↔
        HasWholeMaskDomain (wholeMaskTagReduct C) F x)
    (Target : PartialSetStructure L W) [Finite W]
    (part : W → P) (hTrans : PartialSetStructure.FibreTransversal Target part)
    (S : Set V)
    (g : Embedding (C.induce S)
      (wholeMaskTagExpansion (Target.wholeMaskPatternGraph part)))
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S) :
    (wholeMaskTagReduct C).wholeMaskPartialDecode.Defined F
        (Subtype.val ∘ xs) ↔
      Target.Defined F (g ∘ xs) := by
  have hOldMap :
      HasWholeMaskDomain ((wholeMaskTagReduct C).induce S) F xs ↔
        HasWholeMaskDomain (Target.wholeMaskPatternGraph part) F
          (g ∘ xs) :=
    (g.wholeMaskTagReduct).hasWholeMaskDomain_map_iff F xs
  calc
    (wholeMaskTagReduct C).wholeMaskPartialDecode.Defined F
        (Subtype.val ∘ xs) ↔
        HasWholeMaskDomain (wholeMaskTagReduct C) F
          (Subtype.val ∘ xs) :=
      hDomain F (Subtype.val ∘ xs)
    _ ↔ HasWholeMaskDomain ((wholeMaskTagReduct C).induce S) F xs :=
      (hasWholeMaskDomain_induce_iff (wholeMaskTagReduct C) S F xs).symm
    _ ↔ HasWholeMaskDomain (Target.wholeMaskPatternGraph part) F
          (g ∘ xs) := hOldMap
    _ ↔ Target.Defined F (g ∘ xs) :=
      Target.hasWholeMaskDomain_iff_sourceDefined part hTrans F (g ∘ xs)

/-- The ACTUAL final U-closed, protected-B-covered 2019 picture satisfies
the domain-decoding premise. Any full canonical tagged embedding of its
exact induced test therefore reflects target-defined input tuples on
the original same-carrier source test. This is one local ingredient for
upgrading the selected global control map to a native HE. -/
theorem wholeMaskCovered_defined_iff_of_exact_tagged_embedding
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
    (Target : PartialSetStructure L W) [Finite W]
    (part : W → P) (hTrans : PartialSetStructure.FibreTransversal Target part)
    (S : Set V)
    (g : Embedding (C.induce S)
      (wholeMaskTagExpansion (Target.wholeMaskPatternGraph part)))
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S) :
    (wholeMaskTagReduct C).wholeMaskPartialDecode.Defined F
        (Subtype.val ∘ xs) ↔
      Target.Defined F (g ∘ xs) := by
  exact wholeMaskDecoded_defined_iff_of_exact_tagged_embedding
    C (fun F x =>
      wholeMaskPartialDecode_defined_iff_OLD_domain_of_closed_coverage
        C Base basePart hC hPos hCover F x)
    Target part hTrans S g F xs

end StructuralRamsey.RelStructure
