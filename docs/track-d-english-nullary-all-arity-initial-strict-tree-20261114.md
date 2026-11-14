# Track D — English proof FIRST: strict full-functional initial Picture for ALL arities, including nullaries

**14 November 2026.** Independent of the quantitative bare-control
rank branches #680/#683/#685/#687. This strengthens the verified native
`EHN.initialList_allArity` initial Picture with a genuine strict
full-functional `TreeAmalgam` certificate. It does not change the
frozen numbered Nešetřil programme survey or restore deleted TODOs.

## Exact result

Let K be a hereditary free-amalgamation class of finite
FULL relation/set-valued-function structures. Let Base be a finite
FULL member of K and assume Base is **irreducible**. Allow every
primitive relation/function arity, in particular nullary functions
and their full complete value fibres.

Let D be a control structure and beta0:Base↪D a FULL placement.
Given any finite list of additional FULL placements
beta:Base↪D, the existing all-arity native initial construction
may be chosen as a genuine finite partite Stage T over D with:

* its original exact FULL B-copy placements represented in T
  at the prescribed control parts;
* a distinguished FULL root embedding Base↪T whose part map
  is literally beta0;
* an ACTUAL strict full-functional
  `TreeAmalgam Base T.Carrier T.system.toStructure`.

Therefore every such finite all-arity initial Picture has
`AtMostBare(Base,T,n)` for EVERY finite n, and indeed the
stronger full strict identity-tree witness for every exact weak
vertex set. This removes the otherwise artificial
`Language.PositiveFuncArity` hypothesis from the strict
initial-tree base case.

## Complete English proof

Induct over the list of placements, following the ALREADY
checked code of `EHN.initialList_allArity`, but carry a
`TreeAmalgam` proof at every stage.

**Base list:** T is exactly one placed Base-copy with part
map beta0. Identity Base↪Base is a FULL surjective
embedding, so T is a one-copy strict Base-tree.

**Inductive step:** suppose the current T is a strict
Base-tree with a distinguished FULL embedding
root:Base↪T satisfying part(root(b))=beta0(b).

For a new FULL placement beta:Base↪D, form another placed
copy Q of Base with part map beta. Let

    R = Base.nullaryRoot

be the CANONICAL closed nullary root (it is the full
function-generated closure of the empty input set
in the appropriate native sense). The checked
`Base.nullaryRoot_isClosed` proves this is a valid
FULL source gluing root, including all nullary function
outputs. No false empty-root gluing is assumed.

The already verified `EHN.rootTransport(Base,beta0,beta)`
is a FULL embedding of Base|R to itself matching beta
against beta0 at every real root vertex. Define the
genuine FULL partite support map

    f : Q|R ↪ T,
    f = root ∘ inclusion_R ∘ rootTransport.

Part preservation follows from the checked
`rootTransport_spec` and the distinguished root part law.
This is literally the attaching map used by
`initialList_allArity`; no modified construction or
additional quotient is introduced.

Build the new stage T' by the TRUE native full
`Stage.attach` operation. It is the FULL functional
free amalgam of the previous T and Q over the two
FULL root embeddings f:R↪T and inc:R↪Q.
The checked `Structure.Attachment.unit_isFreeAmalgam`
supplies the exact free diagram.

To check the STRICT tree root-containment clause,
use irreducibility of the whole Base, not of R:

* the image f[R] lies in the distinguished FULL Base-copy
  root[Base] already inside T;
* inc[R] lies in the whole fresh Q=Base, whose identity
  embedding is a FULL irreducible Base-piece.

Thus both source-root embeddings have
`Embedding.ContainedInIrreducible` witnesses, even when
the nullary root R itself is reducible or has many vertices.
The checked `TreeAmalgam.glue` constructor proves T'
is again a strict FULL Base-tree.

The new distinguished root is the previous root followed
by the FULL core embedding T↪T'. Its original beta0 part
law is unchanged. The new Base copy realizes beta
on all its vertices, and previously represented placements
survive by composing with the FULL core embedding.

This closes the induction. Enumerating all FULL Base↪D
placements with `Fintype.ofFinite` yields the standard
unrestricted all-arity initial Picture.

## Sharp limitations

This theorem addresses the **initial stage**, not the
higher-rank mixed or pure-copy control problem. The nullary
root is never replaced by an empty source gluing overlap.
The strict target gluing roots are FULL and contained
inside one irreducible actual Base-copy on each side.

The control structure D need not itself have any strict
B-tree rank. Thus this initial theorem is compatible with
the documented fact that a Ramsey D=K3 may fail large
local K2-tree control budgets. It does not supply the
independent quantitative predecessor needed by the
proposed bare-rank finite HJ Picture theorem #687.

## Lean acceptance

Formalize `EHN.initialList_allArity_tree` by mirroring
the checked `EHN.initialList_allArity` and the checked
positive-arity `EHN.initialList_tree`, replacing the
empty root with the canonical nullary root.
Then derive `EHN.initial_allArity_tree` by enumerating
all embeddings into D.

Both require root-level `#print axioms` checks and
the exact-head full Lean/standard axioms/no-admissions
gate. No numbered manuscript edits.
