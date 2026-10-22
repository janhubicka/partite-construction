import PartiteConstruction.Functional.WholeMaskPartialDecode2019
import PartiteConstruction.Functional.TupleEqualityPattern2019
import PartiteConstruction.Structure.PartialSetFunctionsWholePartRepresent

/-!
# The complete-mask Option(Set) decoder is exactly faithful on sources

For a finite genuine partial set-valued A whose values are transversal
to a fixed finite part map, the canonical complete-mask OLD relational
graph remembers every function value on the literal original carrier:
  - if F(x) = none, there is NO full OLD output tuple;
  - if F(x) = some U, U is represented by a complete output tuple;
  - U = empty is represented by a complete tuple with ZERO outputs,
    never identified with an undefined value.

An arbitrary primitive input x may repeat coordinates. Its exact
surjective equality pattern reconstructs a distinct-input root
without adding vertices, while transversality gives an injectively
part-labelled enumeration of the ENTIRE output set.

The generic complete-mask partial decoder is noncanonical on
inconsistent OLD graphs; here the canonical source semantics show all
of its witnesses have the SAME full value, so it decodes exactly the
original Option(Set) operation. This is source round-trip fidelity,
not normalization of an arbitrary final target or the outstanding
strict mixed-step B-tree completion.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V : Type w}

/-- A complete OLD graph value witness in a canonical genuine partial
source is EQUIVALENT to precisely that original whole function value.
The statement includes defined-empty values and nullary inputs. -/
theorem hasWholeMaskValue_iff_source_func_some
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V)
    (U : Set V) :
    HasWholeMaskValue (A.wholeMaskPatternGraph part) F x U ↔
      A.func F x = some U := by
  classical
  constructor
  · rintro ⟨m, r, hr, q, t, hGraph, hArgs, hU⟩
    have hVal : A.func F
        ((fun i : Fin m => t (Fin.castAdd q.size i)) ∘ r) =
        some (Set.range (fun j : Fin q.size =>
          t (Fin.natAdd m j))) := hGraph.2.1
    have hXs : ((fun i : Fin m =>
        t (Fin.castAdd q.size i)) ∘ r) = x := by
      funext i
      exact (hArgs i).symm
    rw [hXs, ← hU] at hVal
    exact hVal
  · intro hValue
    obtain ⟨q, ys, hRange, hParts⟩ :=
      A.completeOutputPartGraph_represents_value
        part hTrans F x U hValue
    obtain ⟨m, r, root, hr, hInj, hFact, _⟩ :=
      exists_tuple_equality_pattern_exact x
    let p : Language.FunctionInputPattern L :=
      ⟨F, m, r, hr⟩
    let t : Fin (m + q.size) → V := Fin.append root ys
    have hArgEq : root ∘ r = x := by
      funext i
      exact (hFact i).symm
    have hGraph : (A.wholeMaskPatternGraph part).rel
        (.inr (.inr (p,q))) t := by
      change
        Function.Injective
          (fun i : Fin m => t (Fin.castAdd q.size i)) ∧
        A.func F
          ((fun i : Fin m =>
            t (Fin.castAdd q.size i)) ∘ r) =
          some (Set.range (fun j : Fin q.size =>
            t (Fin.natAdd m j))) ∧
        (∀ j : Fin q.size,
          part (t (Fin.natAdd m j)) = q.label j)
      simp only [t, Fin.append_left, Fin.append_right]
      refine ⟨hInj, ?_, hParts⟩
      rw [hArgEq, hRange]
      exact hValue
    refine ⟨m, r, hr, q, t, hGraph, ?_, ?_⟩
    · intro i
      simpa only [t, Fin.append_left] using hFact i
    · simpa only [t, Fin.append_right] using hRange.symm

/-- On the canonical OLD complete-mask graph of a genuine finite
transverse partial-function structure, the generic decoder recovers
each primitive Option(Set) function literally, including none and
some empty. This is a pointwise equality on the EXACT vertex carrier. -/
theorem wholeMaskPartialDecode_canonical_func
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) :
    ((A.wholeMaskPatternGraph part).wholeMaskPartialDecode).func F x =
      A.func F x := by
  classical
  let E := A.wholeMaskPatternGraph part
  have hUnique (U T : Set V)
      (hU : HasWholeMaskValue E F x U)
      (hT : HasWholeMaskValue E F x T) : U = T := by
    have hu : A.func F x = some U :=
      (A.hasWholeMaskValue_iff_source_func_some
        part hTrans F x U).mp hU
    have ht : A.func F x = some T :=
      (A.hasWholeMaskValue_iff_source_func_some
        part hTrans F x T).mp hT
    exact Option.some.inj (hu.symm.trans ht)
  cases hA : A.func F x with
  | none =>
      have hNo : ¬ ∃ U : Set V, HasWholeMaskValue E F x U := by
        rintro ⟨U, hU⟩
        have hSome : A.func F x = some U :=
          (A.hasWholeMaskValue_iff_source_func_some
            part hTrans F x U).mp hU
        rw [hA] at hSome
        cases hSome
      have hDecoded :
          E.wholeMaskPartialDecode.func F x = none :=
        (E.wholeMaskPartialDecode_func_none_iff F x).mpr hNo
      exact hDecoded.trans hA.symm
  | some U =>
      have hValue : HasWholeMaskValue E F x U :=
        (A.hasWholeMaskValue_iff_source_func_some
          part hTrans F x U).mpr hA
      have hDecoded :
          E.wholeMaskPartialDecode.func F x = some U :=
        (E.wholeMaskPartialDecode_func_some_iff F x hUnique U).mpr hValue
      exact hDecoded.trans hA.symm

/-- All original relational predicates are preserved by the source
round trip, independently of the primitive function semantics. -/
theorem wholeMaskPartialDecode_canonical_rel
    (A : PartialSetStructure L V)
    (part : V → P) (R : L.RelSymbol)
    (x : Fin (L.relArity R) → V) :
    ((A.wholeMaskPatternGraph part).wholeMaskPartialDecode).rel R x =
      A.rel R x := rfl

end StructuralRamsey.PartialSetStructure
