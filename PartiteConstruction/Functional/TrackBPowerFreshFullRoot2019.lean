import PartiteConstruction.Functional.TrackBPowerOldRootTransversal2019
import PartiteConstruction.Functional.PatternCompleteRootExtraction2019

/-!
# Track B: complete fresh U-root tags in actual native functional powers

A fresh 2019 closure symbol is indexed by the COMPLETE OLD induced
structure of the positive distinct-input root, not only by its domain
mask or its output part. An exact tagged source tuple therefore requires:

(1) an actual OLD output graph witness;
(2) global injectivity of its displayed input root in the true carrier;
(3) preservation AND reflection of EVERY OLD relation on that root,
    including original relations, equality-pattern domains and output
    tuples with all repetitions.

This source-level criterion is independent of any fictional relational
coordinate power. The second theorem specializes it to the TRUE native
Hales--Jewett functional power and substitutes the verified exact
coordinatewise output-value criterion. The full OLD root profile remains
an explicit conjunct; it is not inferred from the active domain alone.

No root or tested weak carrier is enlarged, and no source-defined EHN
projection is promoted into a full function embedding.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A fresh 2019 U-closure tag on a concrete tuple is equivalent to an
OLD function-output tuple together with the exact FULL induced OLD
root pattern on its original displayed vertices. This quantifies over
ALL OLD relation symbols and ALL tuples in the complete root, not just
the symbol's own active-domain bit.

No arbitrary `PatternTagNormal` assumption is needed: the target is
the literal canonical expansion of E itself. -/
theorem patternTagExpansion_fresh_iff_fullOldRoot
    (E : RelStructure (L.patternGraph) V)
    (p : Language.FunctionRootPattern L)
    (t : Fin (p.input.rootSize + 1) → V) :
    (patternTagExpansion E).rel (.inr p) t ↔
      E.rel (.inr (.inr p.input)) t ∧
      Function.Injective (fun i : Fin p.input.rootSize => t i.castSucc) ∧
      (∀ (R : (L.patternGraph).Symbol)
          (ys : Fin ((L.patternGraph).arity R) → Fin p.input.rootSize),
        E.rel R ((fun i : Fin p.input.rootSize => t i.castSucc) ∘ ys) ↔
          p.root.rel R ys) := by
  constructor
  · rintro ⟨hOutput, e, he⟩
    have hInjective :
        Function.Injective
          (fun i : Fin p.input.rootSize => t i.castSucc) := by
      intro i j hij
      apply e.injective
      calc
        e i = t i.castSucc := (he i).symm
        _ = t j.castSucc := hij
        _ = e j := he j
    refine ⟨hOutput, hInjective, ?_⟩
    intro R ys
    have hSame :
        ((fun i : Fin p.input.rootSize => t i.castSucc) ∘ ys) =
          e.toFun ∘ ys := by
      funext k
      exact he (ys k)
    rw [hSame]
    exact e.map_rel_iff R ys
  · rintro ⟨hOutput, hInjective, hFull⟩
    refine ⟨hOutput, ?_⟩
    refine ⟨{
      toFun := fun i => t i.castSucc
      injective := hInjective
      map_rel_iff := ?_
    }, fun _ => rfl⟩
    intro R ys
    exact hFull R ys

end StructuralRamsey.RelStructure

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}

/-- The genuine native Hales--Jewett power has a fresh U-closure tag
exactly when (a) the WHOLE native-power root is injective,
(b) the selected native-power output WORD belongs to every actual
coordinate function fibre, and (c) the whole root realizes the
prescribed FULL OLD induced pattern (all original relations, all
function domain masks, all function-output tuples).

The root-pattern comparison is not replaced by a coordinatewise
conjunction of input/domain bits; that stronger simplification is
false for roots with coordinate collisions, even before fresh tags. -/
theorem nativePower_freshTag_iff_completeOldRootProfile
    (B : System L P V) (N : ℕ)
    (p : Language.FunctionRootPattern L)
    (t : Fin (p.input.rootSize + 1) → Vertex B N) :
    (patternTagExpansion ((power B N).toStructure.patternGraph)).rel
        (.inr p) t ↔
      Function.Injective
        (fun j : Fin p.input.rootSize => t j.castSucc) ∧
      (∀ i : Fin N,
        (t (Fin.last p.input.rootSize)).coord i ∈
          B.func p.input.symbol
            (fun k => (t (Fin.castSucc (p.input.argMap k))).coord i)) ∧
      (∀ (R : (L.patternGraph).Symbol)
          (ys : Fin ((L.patternGraph).arity R) → Fin p.input.rootSize),
        ((power B N).toStructure.patternGraph).rel R
            ((fun j : Fin p.input.rootSize => t j.castSucc) ∘ ys) ↔
          p.root.rel R ys) := by
  let E := (power B N).toStructure.patternGraph
  constructor
  · intro h
    obtain ⟨hOutput, hRoot, hFull⟩ :=
      (RelStructure.patternTagExpansion_fresh_iff_fullOldRoot E p t).mp h
    have hCoord :=
      (nativePower_oldOutputPattern_iff B N p.input t).mp hOutput
    exact ⟨hRoot, hCoord.2, hFull⟩
  · rintro ⟨hRoot, hCoord, hFull⟩
    apply (RelStructure.patternTagExpansion_fresh_iff_fullOldRoot E p t).mpr
    refine ⟨?_, hRoot, hFull⟩
    exact (nativePower_oldOutputPattern_iff B N p.input t).mpr
      ⟨hRoot, hCoord⟩


/-- Every genuine native-power OLD output relation with positive
distinct-input root has a CANONICAL fresh 2019 closure tag on the
SAME original root and output vertices.

The fresh symbol is constructed from the COMPLETE OLD induced
root structure, not from a bare domain bit or a guessed
coordinatewise OLD root. All primitive repeated inputs are
retained through pat.argMap; no new vertices are introduced. -/
theorem nativePower_oldOutput_admits_canonicalFreshRoot
    (B : System L P V) (N : ℕ)
    (pat : Language.FunctionInputPattern L)
    (hPositive : 0 < pat.rootSize)
    (t : Fin (pat.rootSize + 1) → Vertex B N)
    (hOutput :
      ((power B N).toStructure.patternGraph).rel
        (.inr (.inr pat)) t) :
    ∃ (q : Language.FunctionRootPattern L),
      q.input = pat ∧
        (patternTagExpansion ((power B N).toStructure.patternGraph)).rel
          (.inr q) t := by
  let E := (power B N).toStructure.patternGraph
  have hInjective :
      Function.Injective
        (fun j : Fin pat.rootSize => t j.castSucc) := hOutput.1
  have hDomain :
      E.rel (.inr (.inl pat))
        (fun j : Fin pat.rootSize => t j.castSucc) := by
    refine ⟨hInjective, ?_⟩
    exact ⟨t (Fin.last pat.rootSize), hOutput.2⟩
  refine ⟨Language.FunctionRootPattern.ofActiveDomain E pat
      hPositive (fun j : Fin pat.rootSize => t j.castSucc) hDomain,
      rfl, ?_⟩
  exact RelStructure.patternTagExpansion_tag_of_valid_old_output
    E pat hPositive t hOutput hInjective hDomain


end StructuralRamsey.FunctionalPartite.Induced
