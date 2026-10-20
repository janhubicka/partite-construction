# Finiteness of the source pattern syntax

20 October 2026. English proof before Lean validation.

A function-input pattern names a function F, a root of size m, and a
surjective map from the arity(F) argument positions onto its root labels.
Surjectivity gives m ≤ arity(F), including the zero-arity case. Therefore
the same data can be written as a dependent pair of F and an integer
m in Fin(arity(F)+1), followed by a surjective map between the two finite
sets. Decoding this bounded representation is an exact left inverse of
encoding. When the function-symbol set is finite, every factor in this
bounded dependent sum is finite, so the original pattern type is finite.

For a finite relational signature R and finite carrier V, the relation
predicates form a finite family: each predicate is a subset of the finite
set of tuples of the specified arity. The projection of a relational
structure to that family is injective. Thus the type of relational
structures on V is finite as well. No uniform arity bound is needed beyond
the already finite symbol set and each symbol's natural-number arity.

Together these lemmas supply the finite input-pattern and full-root-pattern
components used by the complete-output-mask expansion. Finiteness of the
part set is also needed for its output masks. An infinite original
signature is not made finite merely by having finitely many parts.

These are statements about the number of syntactic patterns and source
interpretations. They make no target-decoding or target-completion claim.
