# Complete output tuples commute with whole-fibre weak restriction

20 October 2026. English proof before Lean validation.

For each function symbol F of input arity r and each nonnegative integer n,
introduce an (r+n)-ary relation. It holds on an input tuple x followed by an
output tuple y precisely when

    F(x) = some(range(y)).

This records the entire value set, not individual output incidences. The
output tuple may repeat vertices and need not use a canonical ordering.
Accordingly this preliminary relational language is not asserted to have
unique closure tuples. Its purpose is the exact weak-restriction law.

Let S be any vertex subset and y a tuple of vertices of S. Then

    wholeWeakValue(S,v) = some(range(y))

if and only if

    v = some(range(Subtype.val ∘ y)).

Indeed, a surviving whole-fibre value comes from a complete ambient value
U contained in S. If its subtype is the range of y, then U is exactly the
ambient range of that tuple. Conversely every vertex of that ambient range
belongs to S, so the whole application survives and has exactly the stated
subtype value. This argument also applies to the empty output tuple: its
range is empty and the relation records a defined-empty application.

Apply this equivalence to the input and output blocks of every relation
tuple. The complete-value graph of the whole-fibre weak restriction has
exactly the relations of the induced ambient complete-value graph on the
same vertices. The identity maps are full relational embeddings both ways.
No generated closure, fibre clipping, extra vertices, or positive-arity
hypothesis occurs.

Source-defined partial homomorphisms preserve these complete-value relations:
the image of the range of a tuple is the range of the image tuple. In
particular noninjective maps and defined-empty values are supported.

## Scope for the later U-closed translation

Only finite value sets have finite enumerations. The definition and the
restriction law hold without a finiteness hypothesis, but no reconstruction
of arbitrary infinite fibres is claimed. The partite construction has finite
transversal fibres, where this encoding can later be made canonical by the
output parts.

Repeated enumerations and arbitrary output orders are allowed here; the
language is not yet a canonical 2019 closure description. In particular the
proof makes no unique-output-tuple or U-closedness claim. For a later
semi-closed intermediate structure, ambient root/domain tags must also be
retained separately. They must not be recomputed from whichever complete
value tuples survive restriction.

This result is the relational weak-restriction bridge for the intended
whole-fibre convention. It does not supply the remaining target compatibility
or the complete iterated functional Ramsey theorem.
