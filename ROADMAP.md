# Roadmap

The target remains all of Appendix A, with reusable endpoints and survey
markers pinned to checked immutable commits. The authoritative status is the
[current coverage map](docs/appendix-a.md); the previous roadmap is retained
as [historical context](docs/archive/roadmap-before-closure-audit.md).

## Completed routes

The relational non-induced and induced constructions are end-to-end checked.
The positive-arity recursive construction is also assembled: the domain-aware
semi-closed step, singleton reduction, half-closed repair, and ordered graph
Ramsey theorem are not outstanding tasks.

Strict relational sparsening with A and B irreducible is checked through the
complete binary-relation expansion. It no longer relies on the stronger
synchronized tree invariant under mere irreducibility of A.

The two local closure observations now follow from one free-amalgam closure
criterion. The half-closed theorem has an unpacked witness interface without
an input-D transversality assumption.

## Next proof obligations

1. Finish the functional irreducible-image invariant and EHN class-membership
   transfer. Preserve the distinction between full functional homomorphisms,
   weak graph homomorphisms, and closed embeddings. The generated-image
   quotient regression prevents cancelling a noninjective map on input tuples.
2. Settle the literal strong `thm:tree_invariant` under mere irreducibility of A,
   or record the author's decision to use a weaker exact statement. Whole-copy
   localization alone does not repair partial-boundary synchronization.
3. Complete the separate function-language transfer for sparsening. Keep weak
   substructures (including dropped values leaving the subset) explicit.
4. Treat constants separately if expanding beyond the current positive-arity
   initial construction. The local closure calculus already handles them.

## Editorial follow-through

Keep the arbitrary-alpha Picture statement separate from the final recursive
proof until its text is replaced or independently justified. Remove TODOs
only when their exact missing assumption or argument has been supplied.
Representation choices alone are not manuscript errors. Never replace
irreducibility by hereditary irreducibility silently.
