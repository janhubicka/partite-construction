import PartiteConstruction.Functional.OutputPartSingletonization
import PartiteConstruction.Functional.NativeUClosedExactDictionary

/-!
# Genuine MULTIVALUED native partite closedness = U-closed tagged singleton split

The canonical output-part split of a transversal functional partite
system B has singleton-valued primitive functions indexed by pairs
(F,q), where q is an output part. It retains the original vertex
carrier, original relation symbols and all original function outputs
as separate per-part singleton fibres.

The verified native/2019 canonical tagged-root dictionary applies
to this singleton-valued split, as soon as the original function
arities are POSITIVE. The resulting exact induced tagged relational
structure is U-closed precisely when the ORIGINAL MULTIVALUED
native B is function-closed on the SAME vertex set S.

No linear ordering, arity ranking, generated closure, vertex
inflation, or change to the actual Hales--Jewett source Picture
is needed. This is the direct faithful presentation equivalence
for the functional partite class, not a claim about an arbitrary
source-undefined EHN projection or a compatible strict target-tree
root for a hard mixed attachment.
-/

namespace StructuralRamsey

universe u v w

namespace Language

/-- The output-part split retains positive primitive function
arity. Its new function symbols are exactly the lifted original
function symbols paired with a part label. -/
theorem PositiveFuncArity.outputPartIndexed
    {L : Language.{u}} {P : Type v}
    (h : L.PositiveFuncArity) :
    (L.outputPartIndexed P).PositiveFuncArity := by
  intro Fq
  exact h Fq.1.down

end Language

namespace FunctionalPartite

variable {L : Language.{u}} {P : Type v} {V : Type w}

/-- The FINAL EXACT closure dictionary for the original genuinely
MULTIVALUED transversal functional partite B:

Native function-closedness on S is equivalent to 2019 U-closedness
of the ambient canonical tagged full equality-pattern structure
of the SINGLETON output-part split induced on exactly S.

In particular, the induced AMBIENT old function-domain/root tags
survive weak vertex restriction even when some original native
function outputs lie outside S. It would be incorrect to replace
the right-hand side by tags newly computed from the truncated
weak function fibres. -/
theorem System.isClosed_iff_outputPartTaggedInduce_isUClosed
    (B : System L P V) [Finite V]
    (hPos : L.PositiveFuncArity) (S : Set V) :
    B.toStructure.IsClosed S ↔
      RelStructure.IsUClosed
        (L.outputPartIndexed P).patternClosureRules
        ((RelStructure.patternTagExpansion
          (B.splitOutputParts).toStructure.patternGraph).induce S) := by
  have hPositive : (L.outputPartIndexed P).PositiveFuncArity :=
    hPos.outputPartIndexed
  have hSingleton :
      (B.splitOutputParts).toStructure.SingletonValued :=
    B.splitOutputParts_singletonValued
  exact (B.isClosed_iff_splitOutputParts_isClosed S).trans
    (Structure.isClosed_iff_taggedPatternInduce_isUClosed
      (B.splitOutputParts).toStructure hPositive hSingleton S)

end FunctionalPartite
end StructuralRamsey
