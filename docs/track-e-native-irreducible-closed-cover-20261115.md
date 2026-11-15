# Track E: exact native free-cover obstruction to tagged U-irreducibility (15 November 2026)

## The mathematical gap and the correct statement

PRs #698 and #705 independently prove (a) finite U-closed selected-control
tagged B-saturation and (b) full genuine native B copies arising from internal
canonical tagged B copies. PR #713 combines them, but the native B-copy
statement there currently quantifies only over **closed U-irreducible tagged
tests**. The printed clause (3) requires **all native ordinary irreducible
function-closed source substructures**, and does not assert that they are
ordinarily relationally irreducible after tagging.

The missing implication, on the EXACT carrier S in the ACTUAL covered
noncanonical target C, should be:

*Assume S is closed under the decoded native set-valued functions,
and the full native induced structure N|S is irreducible in the universal
functional free-amalgam sense. Then C|S is U-closed and U-irreducible
for the whole-mask closure rules.*

Neither assumption can be replaced by ordinary graph-clique irreducibility.
The hull of S is not an admissible substitute for S.

## English proof

1. Exact closure transport: the checked
   `wholeMaskCovered_inducedUClosed_iff_decodedClosed` makes the
   L-tagged test C|S U-closed **iff** S is closed under the actual
   decoded complete partial fibres, equivalently under their native
   collapse. No syntactic canonicality of C is assumed.
2. Suppose C|S had a proper relational free-amalgam cover by two
   intrinsically U-closed embedded sides. Because C|S is U-closed,
   the verified range lemma makes the exact side ranges X,Y relative
   U-substructures, and they cover S. All tagged relation tuples
   lie on one side.
3. The checked
   `wholeMaskCovered_inducedUSubstructure_to_nativeClosed`
   makes X and Y native-function-closed inside N|S. Primitive
   original relation incidences localize automatically because they
   are OLD tagged relations.
4. Crucially, the checked
   `wholeMaskCovered_inducedNativeFunctionIncident_side` localizes
   **each genuine native function incidence** to one of X or Y:
   a decoded complete-value OLD tuple shows all primitive inputs and
   the output vertex on one common side. This handles repeated inputs,
   multi-output fibres, and empty/undefined inputs; no phantom crossing
   output is created.
5. A generic elementary native lemma says: if two function-closed
   subsets X,Y cover N and every relation tuple and every positive
   function incidence lies on one side, then N is literally the free
   amalgam of its *induced closed* sides N|X,N|Y over N|(X∩Y).
   Native irreducibility forces X or Y to equal the entire vertex
   carrier. This contradicts the assumed proper tagged U-free cover.
6. Therefore C|S is U-irreducible, and the existing #705 checked
   closed-tagged-test decoder supplies an internal full native B-copy
   covering S provided the source also has internal tagged B-extension
   and K-hereditariness (the exact #713 output hypotheses).

## For arbitrary native irreducible embedded E

Take a FULL native E→N. Its literal image S is function-closed
(`Structure.IsHomomorphism.range_isClosed`). Its induced full native
structure N|S is irreducible by the checked surjective homomorphic
image theorem (`Structure.Irreducible.range_homomorphism`). Apply the
lemma above to S, preserving original vertices. Then the internal
native B-copy β:B→N contains all of S, so it contains the entire E
image. This proves `IrreduciblesExtendTo` in the function language
on the same final source.

## Adversarial cautions / Lean acceptance

* If an empty function value is source-defined, it creates no
  positive function incidence; its domain bit is still preserved
  in the original partial decoder. The native collapsed statement
  must not claim to recover defined-empty versus undefined.
* This proof requires actual C to be U-closed AND externally B-covered;
  the final decoder has more guarantees than an arbitrary tagged target.
* Native irreducibility need not imply **ordinary relational**
  irreducibility of C|S. It is the weaker tagged U-irreducibility that
  is appropriate.
* The theorem does **not** transfer the special 2019 closure-profile
  tags to whole-mask part tags; a separate representation bridge is
  required to combine the actual coordinated upstream #1212 with
  these native facts.
* First prove the generic native closed-cover lemma, then prove the
  tagged closed-test bridge and finally the all-native-irred endpoint.
  Require full exact-head Lean compilation, named theorem axiom audit,
  and source/admission scan. No manuscript green marker beforehand.
