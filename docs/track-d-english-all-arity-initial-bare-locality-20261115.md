# Track D — English-first all-arity initial BARE strict locality (15 November 2026)

The corrected printed Nešetřil-programme survey remains frozen.
This fills the STARTING-STAGE endpoint of the proposed weaker,
quantitatively budgeted native strict functional Picture iteration.

Assume a full hereditary free-amalgamation class K of finite
relation/set-valued-function structures, a finite FULL irreducible
Base∈K, an arbitrary control D and one FULL embedding beta0:Base↪D.
Nullary functions, positive-arity functions with genuinely multivalued
fibres, and nullary relations are allowed. Let n be any finite test bound.

The already kernel-checked theorem
`EHN.initial_allArity_tree` (merged PR #690) constructs an actual
finite native Stage T∈K over D which:

1. is a genuine strict full-functional TreeAmalgam of Base-copies;
2. represents every FULL placement beta:Base↪D by a genuine
   FULL Base-copy in T preserving every control vertex label.

**New corollary:** the same T satisfies the weaker BARE
local strict functional invariant `AtMostBare Base T n`
for **every** finite n, with no assumptions on the
local tree structure of control D.

Proof: for every EXACT weak finite S⊆T, use Target=T itself,
the verified strict TreeAmalgam hTree, and restrict the identity
FULL functional embedding of T to S. Its
`IsAmbientRelativeWeakHE` witness preserves all surviving
set-valued outputs and complete ambient nonempty function
fibres whenever wholly contained in S; it also protects
every full ambient irreducible source test entirely
contained in S. No closure or source-to-control map
is used for this local witness.

This corollary is the precise initial input needed by
the stage predicate Q=AtMostBare in the finite native
Hales–Jewett Picture theorem currently in draft #687,
and works with genuine nullary roots.

It does NOT supply the separately required
`AtMostBare Base D F_A(m)` bound for the external
Ramsey control D; that is the remaining genuinely
noncircular outer-rank scheduling problem.
Nor does it complete final copy coverage/2019 projection.

Lean acceptance: one additive theorem
`EHN.initial_allArity_bareRank` and a named
`#print axioms` check, exact-head full CI, no
new axioms or admissions, no manuscript changes.
