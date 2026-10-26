# Full genuine partial-function embeddings encode as FULL OLD complete-mask embeddings

26 October 2026.

For genuinely partial Option(Set) structures A,B with the same finite set of part labels, and a full function embedding e:A→B preserving each vertex's assigned part, the induced map of their canonical OLD complete-mask relational graphs is a FULL/induced relational embedding on exactly the same vertices.

The primitive relations are reflected by the source function embedding. For each old domain-mask tuple, target definedness is `some U` iff the source is `some T` with U=e[T]; a source undefined `none` cannot map to defined-empty `some ∅`. The target part set of the complete output is the original part set because e preserves the part map. The root remains injective.

For each OLD complete output tuple, equality of the full Option(Set) fibres yields equality of the WHOLE output vertex sets, not merely individual incidences. Reflection uses injectivity of e, showing `e[T]=e[range(out)]` implies `T=range(out)`. All ordered mask labels reflect because of part preservation. This includes repeated original input arguments and defined-empty outputs.

This is the forward half of the semantic full-embedding equivalence. The already Lean-verified `Embedding.ofWholeMaskPatternGraph` supplies the reverse direction for a normalized target, and its covered-target specialization is checked. Part preservation is essential: OLD complete-mask data does not by itself label isolated vertices. It must be tracked as a separate partite invariant in the Hales–Jewett stage and final decoder. No weak-test carrier, intrinsic generator rank, or projected image is enlarged.
