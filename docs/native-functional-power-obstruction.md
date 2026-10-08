# An adversarial 12-vertex test in a native functional power

**Research and verification note, 8 October 2026.** The concrete
seven-vertex stage, its tagged second native power, the exact staircase
function-domain matrix, the strict full-functional B-tree no-square theorem,
and the conclusion that the full tagged power has **no strict B-tree
completion** are Lean-verified (PR #114, proof commit
`0b0f2c421cf5f07e0608ce3f57f194286f8109d8`, complete build and
permitted-axiom audit green, workflow `37765314642`). The separate
seven-vertex input-stage **strict B-tree and EHN projection certificate**
and the sharper **12-vertex closed-test** certificate are still not formalized.
This does **not** disprove the final canonical n-pass theorem.

The already-verified positive result
`Structure.inducedRamsey_directFunctionalWeakGraph` remains unaffected:
its tests and their projected images are taken **weakly**, and its target
trees are **relational function-graph** trees.

## 1. Language and template

Use a language with unary relations X, Y, Z (pairwise disjoint roles), a
binary *set-valued function* F, and optionally a binary relation "<".
Let A=B have precisely three vertices x in X, y in Y, z in Z and

    F(x,y) = {z};     every other F-fibre is empty.

To meet the `A.graph.HereditarilyIrreducible` hypothesis used in the
native graph-size iteration, interpret "<" on A as the strict linear
order x<y<z, and in every later freely amalgamated structure keep only
the order tuples inherited from the constituent copies. Then every
induced **graph** subset of A is irreducible. The unary roles ensure
that full homomorphisms preserve the input sorts. All function arities
are positive, and B is irreducible.

The conclusion below depends only on F and the unary sorts; "<" does
not change the obstruction. We may use the unrestricted hereditary
free-amalgamation class of all finite structures in this language.

## 2. A genuine strict B-tree with a weak EHN projection

Let E have X-vertices x0,x1, Y-vertices y0,y1, and Z-vertices
z00,z10,z11. Its only defined fibres are

    F(x0,y0)={z00}, F(x1,y0)={z10}, F(x1,y1)={z11}.

Interpret unary sorts as their names indicate; the binary relation "<"
is the union of the three orders inherited from these hyperedges.
The three hyperedges (x0,y0,z00), (x1,y0,z10), (x1,y1,z11) form a
**genuine full functional strict B-tree** in the mathematical diagram:
glue along {y0}, then along {x1}. Both singleton overlaps are
function-closed and lie in an irreducible B-copy. This source-stage
diagram has not yet been reconstructed as a Lean `TreeAmalgam` proof.

The part projection p:E -> A sends all xi to x, all yj to y, and all
zij to z. It preserves every function incidence forward. Every
irreducible full functional substructure of E lies inside one
constituent B-copy, on which p is a full embedding. Thus it satisfies
the native EHN weak-partite projection condition. There is one output
of a given part for each defined input, so the partite function-output
transversality condition also holds. (The extra order tuples, when
present, are transversal by role.)

However p is **not a full function homomorphism**: F_E(x0,y1) is empty
whereas F_A(x,y)={z}. This is exactly a domain-reflection failure.

## 3. The second *native* Hales--Jewett power

Take the actual coordinatewise partite power E^2, with vertices
tagged by their common A-part; not the naive untagged Cartesian
product and not a U-closed recursive graph construction.

Select three X-vertices and three Y-vertices:

    a0 = (x0,x0),   a1 = (x0,x1),   a2 = (x1,x1),
    b0 = (y0,y0),   b1 = (y0,y1),   b2 = (y1,y1).

The function-domain incidence matrix M for F(ai,bj) != empty is

                b0 b1 b2
           a0   1  0  0
           a1   1  1  0
           a2   1  1  1.

For each of the six ones include the **unique** corresponding Z-output
tuple. All six outputs are distinct:

    (z00,z00), (z00,z10), (z00,z11),
    (z10,z10), (z10,z11), (z11,z11).

The resulting 12-vertex set S is genuinely function-closed in E^2.
The whole tagged power has only 17 vertices (4 X-words, 4 Y-words and
9 Z-words); its entire carrier is closed. Thus the checked
`actualPower_not_locallyStrictTreeCompletable` gives a finite-rank
obstruction without requiring the 12-vertex test to be assembled in Lean.
There are no other defined input tuples among these vertices. In
particular its full induced functional structure H is a legitimate
closed test on exactly 12 vertices; taking its closure adds **zero**
vertices.

The matrix has a K_{2,2} on a1,a2 and b0,b1. Crucially all row
neighbourhoods (100, 110, 111) and column neighbourhoods
(111, 011, 001) are distinct. This prevents identifying either of
the two same-role vertices of that 4-cycle in a full homomorphism.

By the checked EHN graph-power bridge, the weak image of H under the
projection to A has a one-copy **relational graph-tree** completion.
(The graph map need not reflect missing F-domains.)

## 4. Why no full functional strict B-tree completion exists

We use two elementary observations.

**Domain-forest invariant.** For a full functional strict tree T of
B-copies, let G(T) be its bipartite graph with an edge between an
X-vertex u and Y-vertex v exactly when F_T(u,v) is nonempty.
Then G(T) is a forest.

Proof by induction over the full functional `TreeAmalgam`:

* One B-copy has a single X--Y edge.
* At a strict gluing, the source root is contained, on each side,
  in an irreducible substructure. Every such irreducible lies inside a
  constituent full B-copy (the usual irreducible-containment induction
  for strict free amalgams).
* Consequently the root has at most one X-vertex and one Y-vertex.
  If it contains both, then its image is **function-closed** in each
  side by fullness of the embeddings and must also contain their
  unique F-output. Thus the domain graph of the root consists of
  one edge; otherwise it consists of at most one vertex.
* Each full side embedding preserves the entire function fibres, so
  the domain graph of the amalgam is exactly the union of the two
  domain forests along that empty, single-vertex or single-edge
  intersection. Such a union is a forest.

**No collapse of the displayed cycle.** Suppose
f:H -> T is a full homomorphism-embedding into such a T. Its full
function-fibre equality implies, for every displayed ai,bj,

    F_H(ai,bj) != empty  iff  F_T(f(ai),f(bj)) != empty.

If f(ai)=f(ak), the ith and kth rows of M must coincide. Thus f
is injective on {a0,a1,a2}. Likewise it is injective on
{b0,b1,b2}. The preserved disjoint unary sorts prevent
cross-role identifications. Therefore the K_{2,2} on
a1,a2,b0,b1 maps to a genuine 4-cycle in G(T), contradicting
the domain-forest invariant.

Hence H admits **no full functional homomorphism-embedding** into
any strict functional tree of B-copies. In particular, E^2 is not
locally full-functional B-tree-completable at vertex rank 12, even
though E itself is a strict full-functional B-tree and E^2 has the
expected weak graph-tree completion.

## 5. Consequences and exact limits

1. A **generic** strict functional local-tree invariant based only on
   (i) old-stage strict full B-tree completability,
   (ii) an EHN weak projection to A, and
   (iii) the previous control A being a B-tree,
   cannot be preserved by arbitrary native Hales--Jewett powers.
   All those premises hold above, but power E^2 fails at rank 12.
2. This is not a fibre *multiplicity* defect: each defined F-fibre
   contains one output and p is bijective on it. The failure is the
   pattern of **undefined** cross-input pairs.
3. This is stronger as a test of proof strategy than the earlier
   two-step unary path counterexample: the closed obstruction is
   *inside the native coordinatewise functional power* of a bona fide
   full B-tree and weakly-partite EHN stage.
4. It does **not** establish that E occurs as the selected closed
   A-support in the actual canonical initial/Picture trace, nor
   that the last stage of every n-pass construction fails. A
   *native-stage-specific* support invariant could still exclude
   this E configuration and rescue a stronger theorem.
5. The printed relational sparsening theorem and the verified direct
   functional **weak graph-tree** theorem are untouched.

## Recommended verification and alternatives

* The reduced three-role B-template, concrete E, actual tagged E^2,
  exact staircase matrix and finite-rank no-full-tree obstruction are
  now proved and axiom-audited in Lean. Formalize the remaining strict
  source-tree/EHN projection certificate and the 12-vertex closed subtype.
* The needed **no-4-cycle** invariant for genuine strict B-trees,
  and its combination with the tagged-power matrix, are now Lean
  proved (`strictTree_squareFree`, `actualPower_no_fullStrictTreeHom`).
  The stronger general forest assertion remains a separate optional claim.
* Check the actual canonical EHN Picture supports. A plausible
  strengthening is a special invariant of **selected closed
  A-supports**, not a universal strict-local-tree assertion about
  arbitrary weakly-partite stages. If E can be forced inside such a
  support, search for a genuine impossibility result for the target
  theorem instead of indefinitely strengthening the induction.
* Retain the existing weak-to-weak projection step
  `IsWeakHomomorphismEmbedding.weakImage`: replacing the weak image
  by a generated closed hull destroys the vertex-size accounting
  and does not resolve the domain obstruction.

**Hypothesis caution.** The checked Lean template has three unary role
relations and one binary set-valued function. Its function graph is not
hereditarily irreducible on arbitrary vertex subsets. To apply the exact
hypotheses of the iterated n-pass theorem, the extra binary pairwise-order
relation mentioned above should be added and its transport checked in Lean.
This is separate from the no-square obstruction for the reduced language.
