# The original full-functional sparsening conclusion is false

> **Scope correction (8 October 2026):** The counterexample refutes the
> *literal 2026 survey* sparsening theorem with its **total set-valued
> functions** and equality of entire fibres at **every** input. It does
> **not** refute the original **2019 partial-function homomorphism**:
> that definition imposes equality only on defined source inputs, without
> reflecting missing domains. The proof below uses the stronger total-fibre
> convention at its central `total_of_full_projection` step. See
> `docs/original-partial-homomorphism-audit.md`.

## Source and semantic check

The arXiv postprint of Hubička–Konečný, *Twenty years of Nešetřil’s classification programme of Ramsey classes*, arXiv:2501.17293v5, explicitly identifies itself as a postprint of the Computer Science Review article. Section 2.1 defines homomorphisms by preservation of complete function fibres, without a nonempty-domain exception. The free-amalgam definition excludes mixed function incidences as well as mixed relation tuples. Theorem 6.11 is the statement called `thm:sparseningRamsey` in the TeX source; Appendix A.3 gives its proof.

Source: https://arxiv.org/html/2501.17293v5

The separately requested historical commit message `zmeny z publikovany verze` has not been located. That missing Git reference no longer prevents checking the actual postprint statement and map conventions.

## Three finite input structures

Use one binary function F and no relation symbols. On every finite carrier put

    F(x,y) = {x}.

Let A, B and D have respectively one, two and three vertices. All injections are full embeddings. All these structures are irreducible: a pair of vertices in different exclusive sides of a proposed free decomposition would give a mixed function incidence. In particular A and B are both irreducible. The arrow D -> (B)^A_2 is the ordinary three-point pigeonhole principle.

There are no nullary functions, multiple outputs, empty input structures or nonrigid colouring-object issues. The operation is an ordinary total binary operation written in the survey's singleton-valued convention.

## Full projection already forces irreducibility

Suppose p:C -> D is a full homomorphism. For every x,y in C,

    p[F_C(x,y)] = F_D(p(x),p(y)) = {p(x)}.

Thus F_C(x,y) is nonempty for every pair. Consequently C is irreducible, regardless of whether p is injective: a mixed pair cannot be supported by either side of a free amalgam.

### Clauses (1) and (3) alone give a contradiction

Apply the irreducible-extension clause (3) to the whole, genuinely closed structure C. It lies in a B-copy inside C, hence C embeds into the two-point B. Colour each A-embedding in C by the image of its unique point in B. The two A-subcopies of every B-copy receive different colours, contradicting C -> (B)^A_2.

This argument uses only that p is a **full homomorphism**, not its additional embedding-on-irreducibles property. It uses no local-tree requirement at all, and therefore applies to every requested local rank n. Replacing strict trees by loose trees cannot fix this contradiction.

### Independent contradiction using clauses (1) and (2)

Since C is irreducible, a full homomorphism-embedding p:C -> D is injective, so |C| <= 3. At n=3, the local-tree clause applies to the whole C. Its full homomorphism-embedding into a B-tree is an embedding because C is irreducible. Every irreducible substructure of a full free tree of B-copies lies inside one constituent B-copy. Hence C embeds into B, contradicting the same singleton colouring.

This second argument does not use clause (3).

## Lean certificate

`PartiteConstruction/Functional/PublishedTotalBinaryObstruction.lean` proves:

- `total_irreducible`: a total binary function forces full functional irreducibility;
- `three_ramsey_two`: the exact full-function Ramsey arrow for A,B,D;
- `no_full_projection_and_local_trees`: clauses (1)+(2) fail at rank 3;
- `no_full_projection_and_irreducible_extension`: clauses (1)+(3) fail independently of local rank;
- `not_publishedSparseningConclusion_all`: the exact `PublishedSparseningConclusion A B D (Fin 2) n` fails for every n;
- `published_functional_counterexample`: all assumptions and the negated conclusion together.

The substantive proof passed the full build and permitted-axiom audit at commit `6cfcfbc25eaf24738a2b5966d931f381f315c2d0`, workflow `37780235492`. The expanded audit and note also passed at `ae065f7d4dfc455f74dd10ecb1d779d129db5ce3`, workflow `37781414762`. The dedicated `CheckPublishedSparsening.lean` is included in CI's build and axiom checks. No `sorry`, custom axiom, or unchecked computation is used.

## Consequences for the revision

This supersedes the earlier status that the literal general functional statement was merely unproved in Lean. Unlike the native-power examples, this is an existential counterexample: another construction cannot satisfy all the same clauses for these A,B,D.

A correct general functional statement retaining the Ramsey arrow and clause (3) must change the full-projection requirement or exclude examples such as this one. An EHN weak projection—forward preservation globally and a full embedding on every irreducible—is the natural candidate already supported by the native construction. The counterexample does **not** by itself prove that this change suffices for strict functional local trees or final B-copy extension.

The verified relational strict theorem remains intact. Unary functions are not covered by this obstruction: PR #116 actually proves that unary EHN projections are full, and packages the resulting full-projection Ramsey theorem. The general function-language result currently proved is `sparseningRamsey_functionalWeakGraph_inClass`, with weak EHN global projection and strict trees of the relational function graphs. It remains distinct from strict full-functional B-tree completion.

Keep the original partite proof organisation in the revision, but do not try to restore the disproved full-functional statement verbatim. Leave the circulation text unchanged pending an explicit editorial decision, and attach this counterexample as a correction note with the exact map convention stated.
