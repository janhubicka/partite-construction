import PartiteConstruction.Functional.WholeMaskCoveredPartialDecoding2019
import PartiteConstruction.Structure.PartialSetFunctionsTransversal
import PartiteConstruction.Functional.WholeMaskTagFreeAmalgam2019

/-!
# Complete-mask output-part laws and transversal decoded functions

The old relational whole-mask language labels the OUTPUT COORDINATES
of each complete-valued function relation by an injective list of
parts. The language does not by itself force an arbitrary target's
actual part map to agree with those labels.

We therefore record the exact required partite invariant explicitly:
each output of a positive old complete-value tuple lies in its
declared part. Canonical genuine partial sources satisfy the law;
it is hereditary on exact induced carriers and survives a genuine
FULL OLD free amalgam if both side maps respect the part labels.

For any old graph satisfying this law, UNIQUE COMPLETE VALUES ensure
that the decoded Option(Set) fibres are transversal to the actual
part map. In particular the final U-closed canonical-B-covered
target has transversal decoded values provided the same independently
maintained partite label law holds.

Nothing here asserts the part-label law follows from bare U-closedness
or B-copy coverage: the target's chosen partition is EXTERNAL to the
unexpanded relational language. No exact weak source test is closed,
and no strict B-tree target completion is constructed.
-/

namespace StructuralRamsey.RelStructure

universe u v w z
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V : Type v} {W : Type z}

/-- Every complete OLD output tuple respects its own output-part
labels under the ACTUAL target part map. This condition is not
deducible merely from the 2019 U-closure rules. -/
def WholeMaskOutputPartsCompatible
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (part : V → P) : Prop :=
  ∀ (p : Language.FunctionInputPattern L)
    (q : Language.CompleteOutputParts P)
    (t : Fin (p.rootSize + q.size) → V),
    E.rel (.inr (.inr (p,q))) t →
    ∀ j : Fin q.size,
      part (t (Fin.natAdd p.rootSize j)) = q.label j

/-- The canonical graph of any genuinely partial source records
the correct output-part labels, whether the value is singleton,
multivalued, defined-empty, or attached to repeated inputs. -/
theorem PartialSetStructure.wholeMaskPatternGraph_outputPartsCompatible
    (A : PartialSetStructure L V) (part : V → P) :
    WholeMaskOutputPartsCompatible (A.wholeMaskPatternGraph part) part := by
  intro p q t ht j
  exact ht.2.2 j

/-- Restriction to an EXACT vertex subset retains ambient relation
labels. It does not recompute the domain masks from a weak function. -/
theorem WholeMaskOutputPartsCompatible.induce
    {E : RelStructure (L.wholeMaskPatternLanguage P) V}
    {part : V → P}
    (h : WholeMaskOutputPartsCompatible E part)
    (S : Set V) :
    WholeMaskOutputPartsCompatible (E.induce S)
      (part ∘ Subtype.val) := by
  intro p q t ht j
  exact h p q (Subtype.val ∘ t) ht j

/-- Complete-value coherence plus correct output-part labels makes
all actual decoded Option(Set) function fibres transversal.
The decoder remains genuinely PARTIAL; none and some-empty are not
conflated. This is an abstract semantic lemma, with no U-closedness
or B-coverage assumption. -/
theorem WholeMaskOutputPartsCompatible.decoder_fibreTransversal
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (part : V → P)
    (hParts : WholeMaskOutputPartsCompatible E part)
    (hUnique : ∀ (F : L.FuncSymbol)
      (x : Fin (L.funcArity F) → V) (U T : Set V),
      HasWholeMaskValue E F x U →
      HasWholeMaskValue E F x T → U = T) :
    PartialSetStructure.FibreTransversal
      E.wholeMaskPartialDecode part := by
  intro F x U hSome y hy z hz hyz
  have hValue : HasWholeMaskValue E F x U :=
    (E.wholeMaskPartialDecode_func_some_iff
      F x (hUnique F x) U).mp hSome
  obtain ⟨m,r,hr,q,t,hTuple,_hArgs,hU⟩ := hValue
  have hyRange : y ∈ Set.range
      (fun j : Fin q.size => t (Fin.natAdd m j)) := by
    rw [← hU]
    exact hy
  have hzRange : z ∈ Set.range
      (fun j : Fin q.size => t (Fin.natAdd m j)) := by
    rw [← hU]
    exact hz
  obtain ⟨i,hi⟩ := hyRange
  obtain ⟨j,hj⟩ := hzRange
  let pat : Language.FunctionInputPattern L := ⟨F,m,r,hr⟩
  have hLabels : ∀ k : Fin q.size,
      part (t (Fin.natAdd m k)) = q.label k :=
    hParts pat q t hTuple
  have hij : i = j := q.label_injective (by
    calc
      q.label i = part (t (Fin.natAdd m i)) := (hLabels i).symm
      _ = part y := congrArg part hi
      _ = part z := hyz
      _ = part (t (Fin.natAdd m j)) := (congrArg part hj).symm
      _ = q.label j := hLabels j)
  calc
    y = t (Fin.natAdd m i) := hi.symm
    _ = t (Fin.natAdd m j) :=
      congrArg (fun k : Fin q.size => t (Fin.natAdd m k)) hij
    _ = z := hj

/-- In particular, final protected canonical B-copy coverage supplies
the UNIQUE complete values needed above, while compatibility with
the actual part map remains a separate input invariant. -/
theorem wholeMaskPartialDecode_fibreTransversal_of_closed_coverage
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (basePart : W → P)
    (part : V → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph basePart))))
    (hParts : WholeMaskOutputPartsCompatible
      (wholeMaskTagReduct C) part) :
    PartialSetStructure.FibreTransversal
      ((wholeMaskTagReduct C).wholeMaskPartialDecode) part := by
  exact hParts.decoder_fibreTransversal
    (wholeMaskTagReduct C) part
    (fun F x U T hU hT =>
      wholeMaskValue_unique_of_closed_coverage
        C Base basePart hC hPos hCover F x U T hU hT)

end StructuralRamsey.RelStructure

namespace StructuralRamsey.RelStructure.IsFreeAmalgam

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {H E F C : Type v}

/-- Part-compatible FULL relational free amalgams preserve the
complete output-part label law, on exactly the same source vertices.
Both side maps must explicitly agree with the WHOLE target part map;
bare OLD full embeddings do not imply this external compatibility. -/
theorem wholeMaskOutputPartsCompatible
    {Root : RelStructure (L.wholeMaskPatternLanguage P) H}
    {Left : RelStructure (L.wholeMaskPatternLanguage P) E}
    {Right : RelStructure (L.wholeMaskPatternLanguage P) F}
    {Whole : RelStructure (L.wholeMaskPatternLanguage P) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (partWhole : C → P) (partLeft : E → P) (partRight : F → P)
    (hPartLeft : ∀ x : E, partWhole (iL x) = partLeft x)
    (hPartRight : ∀ y : F, partWhole (iR y) = partRight y)
    (hLeft : WholeMaskOutputPartsCompatible Left partLeft)
    (hRight : WholeMaskOutputPartsCompatible Right partRight) :
    WholeMaskOutputPartsCompatible Whole partWhole := by
  intro p q t hTuple j
  rcases (hFree.rel_iff (.inr (.inr (p,q))) t).mp hTuple with
    ⟨tL,hL,ht⟩ | ⟨tR,hR,ht⟩
  · have hOutput : t (Fin.natAdd p.rootSize j) =
        iL (tL (Fin.natAdd p.rootSize j)) :=
      congrFun ht (Fin.natAdd p.rootSize j)
    rw [hOutput, hPartLeft]
    exact hLeft p q tL hL j
  · have hOutput : t (Fin.natAdd p.rootSize j) =
        iR (tR (Fin.natAdd p.rootSize j)) :=
      congrFun ht (Fin.natAdd p.rootSize j)
    rw [hOutput, hPartRight]
    exact hRight p q tR hR j

end StructuralRamsey.RelStructure.IsFreeAmalgam
