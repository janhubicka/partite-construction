import PartiteConstruction.Functional.OutputPartSingletonUClosedBridge
import PartiteConstruction.Ramsey.ClosureSemiClosed2019

/-!
# Real native multivalued functional weak tests are U-semi-closed

Every native genuine transversal partite System B is canonically
represented by singleton partial output-part operations (F,q).
The complete input-pattern tagged relational expansion of this
SPLIT structure is genuinely U-CLOSED by the already verified
canonical 2019 theorem and per-output-part transversality.

For ANY exact literal source vertex subset S, its induced
AMBIENT tagged structure is U-SEMI-CLOSED: partial closure
tuples remain single-valued over VALID full roots, but a root
may have no surviving tuple because its output lies outside S.

This is exactly the intermediate state permitted by the
published U-closed Picture construction; it does NOT demand
that nonclosed weak S be function-closed or enlarge S to its
generated hull. Input-root domain tags are induced from the
ambient structure, never recomputed from truncated fibres.

On finite positive-arity inputs, U-closedness of the same
induced tagged test is equivalent to actual native function-
closedness of S. In all cases arbitrary EHN projections remain
source-defined PARTIAL; compatible strict TARGET B-tree roots
still require a separate history-dependent proof.
-/

namespace StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}

/-- The AMBIENT canonical 2019 tagged expansion of the genuine
multivalued native System B, after its output-part singleton
split, is fully U-closed. For each original multivalued output
part q there is at most one output above a complete root.

No positive-function-arity restriction is imposed at this
point: the 2019 fresh closure rules are themselves
positive-root patterns; primitive nullaries remain in
the old domain/output incidence language. -/
theorem System.taggedOutputPart_isUClosed (B : System L P V) :
    RelStructure.IsUClosed
      (L.outputPartIndexed P).patternClosureRules
      (RelStructure.patternTagExpansion
        (B.splitOutputParts).toStructure.patternGraph) :=
  RelStructure.patternTagExpansion_isUClosed
    (B.splitOutputParts).toStructure
    B.splitOutputParts_singletonValued

/-- Every EXACT weak vertex test S of a true native
transversal functional partite System is U-SEMI-CLOSED
in its induced AMBIENT canonical tagged singleton
presentation, including when actual function outputs
are omitted and S is NOT function-closed.

Neither vertex set nor rank budget is altered. -/
theorem System.taggedOutputPart_weak_isUSemiClosed
    (B : System L P V) (S : Set V) :
    RelStructure.IsUSemiClosed
      (L.outputPartIndexed P).patternClosureRules
      ((RelStructure.patternTagExpansion
        (B.splitOutputParts).toStructure.patternGraph).induce S) :=
  (B.taggedOutputPart_isUClosed).induce_isUSemiClosed S

/-- For finite native Systems with POSITIVE primitive function
arities, the exact induced semi-closed tagged test becomes FULLY
U-closed precisely when S retains ALL original multivalued
native function outputs. The missing-target/root obligations
in a nonclosed S are intentionally not erased. -/
theorem System.taggedOutputPart_weak_isUClosed_iff_nativeClosed
    (B : System L P V) [Finite V]
    (hPos : L.PositiveFuncArity) (S : Set V) :
    RelStructure.IsUClosed
      (L.outputPartIndexed P).patternClosureRules
      ((RelStructure.patternTagExpansion
        (B.splitOutputParts).toStructure.patternGraph).induce S) ↔
      B.toStructure.IsClosed S :=
  (B.isClosed_iff_outputPartTaggedInduce_isUClosed hPos S).symm

end StructuralRamsey.FunctionalPartite

