# Output-part singletonization respects genuine native functional Hales–Jewett data

**19 October 2026 — English-first proof and adversarial audit**

The main goal is the ORIGINAL functional iterated partite construction,
not replacement by a different relational Ramsey Picture. The previous
output-part split (PR #430) replaces each primitive multivalued F by
singleton-valued partial symbols (F,q), indexed by the actual output
part q. The native function fibres, full embeddings, exact weak tests,
and closed subsets are then completely recoverable from those symbols.

This note checks that the same singleton-language representation works
on the actual genuine functional Hales–Jewett POWER, not just on
static source systems.

## Projection to the split control

Let B be a genuine transversal System over part set P and let A
be the original functional control structure on P. Assume the
SURVEY'S FULL projection law

   p_B[F_B(x)] = F_A(p_B(x))

at each primitive input tuple. Let A^P be the canonical
output-part split of the transversal control System(A,id).

Then B^P, the canonical singleton split of B, still has a
FULL partite projection onto A^P. At (F,q) its projected
source fibre is

   p_B[{y∈F_B(x):p_B(y)=q}].

The target (F,q)-fibre consists of those p∈F_A(p_B x)
with p=q. Forwards: project an actual F-output y and
remember its part q. Backwards: any q∈F_A(p_B x)
is realized by some native F-output y with p_B(y)=q,
using the ORIGINAL full projection's WHOLE-fibre law.
This proves literal image-set equality for all symbols,
without singleton-valuedness of F_B or global injectivity
of p_B.

The actual native induced/Hales–Jewett partite lemma can
therefore run on the split control without losing ANY
original outputs or changing the chosen part set.

## Exact coordinatewise power output law

Let N>0. The actual native coordinatewise power of B
has vertices z=(p_z,z_i) whose coordinates all have part
p_z. For each primitive F, tuple x of power vertices,
and output vertex y, the ORIGINAL power fibre is

  y∈F_{power(B,N)}(x)
       iff ∀i<N, y_i∈F_B(x_i).

Splitting the ACTUAL POWER by output part q gives

  y∈F^q_{power(B,N)}(x)
       iff
    [∀i<N, y_i∈F_B(x_i)] and p_y=q.

Since N>0, the vertex condition supplies a coordinate i0.
For every i, p_B(y_i)=p_y. Thus the preceding condition
is EQUIVALENT to

  ∀i<N, [y_i∈F_B(x_i) and p_B(y_i)=q],

which is exactly the (F,q) coordinatewise power law of
the split B^P.

This is an exact fibre law, not just a homomorphism
or positive-incidence implication. It handles nullaries,
repeated inputs and genuinely multivalued original F.
No new vertices or closure-hull points appear.

**N>0 is essential:** at N=0, the coordinatewise function
condition is vacuous, while splitting the power imposes
p_y=q. The two operations need not commute for an empty
power, so a positive Hales–Jewett length must be explicit.

## Adversarial audit

* The fixed part type P is essential: (F,q) represents the
  same output-part label in every power coordinate. This
  holds in the TRUE native partite construction.
* The full projection theorem is needed to lift a required
  control output q back to a source output. An EHN projection
  at a source-undefined tuple is NOT sufficient.
* No full-function-domain reflection is asserted for the
  iterated EHN projection: it remains original-partial.
* The positive-length condition cannot be omitted.
* Distinct-coordinate output choices are allowed; the
  native transversality invariant enforces uniqueness only
  within a FIXED q, which is exactly what the split requires.
* This lemma certifies the native HJ POWER presentation,
  not arbitrary finite line-attachment history compatibility.
  The verified K2 parity/C5 obstructions are untouched.
* The separate Option(Set) defined-empty operation bit must
  be preserved separately before using that alternative API.

## Formalization target

Prove:
1. \`System.splitOutputParts_projectionHom\`: full original
   partite projection implies full singleton split projection
   to the canonically split control;
2. \`Induced.power_splitOutputParts_func_iff\` for N>0:
   the exact coordinatewise per-output-part function fibre
   law of the REAL native Hales–Jewett power.

Then strengthen to a canonical power-system full isomorphism
in the output-part-indexed language, and transport actual
line embeddings if necessary for iterated Picture attachment.
The complete functional n-pass theorem remains a separate
goal; do not add a survey verification marker.
