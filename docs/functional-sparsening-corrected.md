# A checked full-functional alternative to the published sparsening theorem

> **Semantics note (8 October 2026):** This correction addresses the
> 2026 survey's *total set-valued function* definition of homomorphism,
> which reflects empty fibres. Under the genuinely partial-function
> homomorphism convention of *All those Ramsey classes* (2019), our
> EHN weak projections are already full homomorphisms **on defined
> inputs**, in exactly the required original sense. The total-fibre
> and partial-function conclusions must not be conflated; see
> `docs/original-partial-homomorphism-audit.md`.

## Status and scope

The literal published statement with a full global homomorphism-embedding is false; see `PublishedTotalBinaryObstruction.lean` and `docs/published-total-binary-obstruction.md`. Its clauses (1) and (3) already contradict a three-point pigeonhole example. Consequently changing the local tree condition alone cannot repair the general theorem.

The present branch proves a genuine function-language replacement, keeping all three kinds of conclusions but making two changes explicit:

1. The global projection is **EHN weak**: it preserves relations and function incidences and restricts to a full embedding on each full irreducible.
2. The tree is a **loose full-functional B-tree**: the gluing roots are genuine closed substructures, but need not lie in irreducible containers on each side.

All Ramsey embeddings, local embeddings, and actual B-copy extensions are FULL function-language embeddings. No relational function-graph target is substituted.

## The theorem

For any relation/function language L, finite structures A,B,D and nonempty finite colour set kappa, assume D -> (B)^A_kappa. Then there is a finite genuine L-structure C such that:

- C -> (B)^A_kappa for full embeddings;
- an EHN weak homomorphism-embedding C -> D exists;
- C itself is a finite loose full-functional tree of B-copies;
- every irreducible full substructure of C is contained in an actual full B-copy in C;
- every genuine closed substructure of C, at every finite vertex bound n, fully embeds into a loose B-tree (C itself).

If A and B lie in a hereditary free-amalgamation class K, C may be chosen in K. No irreducibility assumption on A or B, no hereditary graph-irreducibility hypothesis, and no restriction on function arities is used. Nullary functions are included through the canonical shared closed root.

The endpoints are `Structure.sparseningRamsey_functional_looseFullTrees_inClass` and `Structure.sparseningRamsey_functional_looseFullTrees` in `Functional/PublishedSparseningLoose.lean`.

This is an existence theorem without a strict sparse-locality assertion. Since loose gluing can create cycles, its target condition must not be renamed the strict tree condition of the survey. The earlier weak-graph strict-tree theorem and this full-functional loose-tree theorem preserve different parts of the published conclusion; neither should be presented as the other.

## Proof following the original construction

### 1. The induced partite pass

The initial picture consists of full B-copies with their specified embeddings into D. For constants these copies share their canonical nullary root; the existing root transport aligns the different placements. The Hales–Jewett core is the actual tagged coordinatewise functional power. The Picture step attaches old pictures over full closed supports.

Retain the published intermediate invariant: every irreducible full substructure of the current picture projects into a full B-copy in D. For a core irreducible, project to any one coordinate. The closed hull of that weak image is irreducible in the old picture, so its projected vertices belong to an old B-placement. This use of a closure hull is solely an irreducible-localization argument; it never changes a measured weak vertex test or a local size budget. For a free attachment, every full irreducible lies in one side, and the invariant follows from that side.

The usual finite canonicalization and backward colour extraction therefore produce a finite full-functional Ramsey witness P, an EHN map p:P->D, and projected B-coverage. This is `EHN.inducedConstruction_allArity_projectedCover`, with no local-tree hypothesis hidden in its premises.

### 2. Full completion over closed roots

Induct on the finite size of P. If P is irreducible, the EHN restriction is a full embedding; projected coverage factors it through one B-copy in D. Use that B-copy as the target.

Otherwise take a proper full free decomposition P=L amalgam_R H. Complete the two smaller sides by induction. Their full embeddings carry the same original closed R into their respective targets. Freely amalgamate the targets over these two images of R. Injectivity of the side embeddings ensures exact root isolation, so the lift of P is a full embedding. The target is a loose B-tree, and its EHN map to D is obtained by gluing the two compatible weak maps.

This proves `ProjectsIrreduciblesInto.projectedLooseCompletion`. It requires no uniform bound on the number of irreducibles and no unproved simultaneous strict-root oracle.

### 3. The final conclusions

The full embedding P->C preserves the Ramsey arrow. Every irreducible full substructure of a loose tree of B-copies is contained in one constituent B-copy, giving the original extension clause. Free-amalgamation closure preserves K. The global loose-tree witness C supplies the full local embedding conclusion at every n.

## Verification

The full project build and permitted-axiom audit passed on immutable proof head `937d6d6f6b5377d6a572cdc49bd421fb0f424e19`, workflow `37783883233`. `CheckFunctionalCover.lean` explicitly imports and audits every layer, including the all-arity initial picture, complete Ramsey pass, final completion, and the two end-to-end endpoints.

The proof does not use the false `PublishedSparseningConclusion` as an axiom, nor assume projected coverage as an input to the final Ramsey theorem: coverage is proved for the native pass.

## Remaining strict problem

The meaningful remaining question is a corrected theorem with an EHN weak global projection but the original strict full-functional local B-tree conclusion. The original full-projection statement is no longer an open formalization target: it is refuted. A proof for strict trees must control the shape of the gluing roots, beyond the arbitrary closed roots allowed here. The previously checked counterexample to generic strict preservation under a native power remains relevant to that narrower task.

Uses of the original functional sparsening theorem in the survey must be checked against these exact distinctions; this note does not assert that every application follows from the loose-tree replacement.
