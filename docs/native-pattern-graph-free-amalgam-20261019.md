# Genuine function-language free amalgamation agrees with the OLD equality-pattern language

**19 October 2026 — English proof and adversarial audit, before Lean.**

The checked native/U-closed dictionary identifies function-closed
exact subsets with U-substructures of a tagged relation language.
The map-level lemma (#427) preserves all induced ambient domain and
output records under FULL native embeddings. The independent
canonical-tag lemma (#428) proves that adding complete-root
fresh tags preserves a FREE amalgam of OLD function-pattern
relational structures.

We now prove the decisive missing first half:

  Genuine full native FUNCTION free amalgamation
       ⇒ FULL free amalgamation in the OLD
          equality-pattern domain-and-output language.

Combined with #428, the canonical tagged U-closed source
diagram of any genuine native functional attachment is a
relational free amalgam on the EXACT same vertices.

## Main proof

Take a FULL genuine native free amalgam of relation/function
structures
\[
 C = E *_{H} F
\]
with four FULL attaching maps. For a primitive function
symbol \(G\) of arity \(a\), the OLD language has a domain
relation and an output-graph relation for every equality
pattern \(r:\mathrm{Fin}(a)\twoheadrightarrow\mathrm{Fin}(m)\).
Each such OLD relation has a root tuple enumerating the
\(m\) distinct input vertices, not all \(a\) argument
positions.

We must prove that every positive OLD relation tuple in C
comes wholly from E or wholly from F, with full reflection
under the corresponding side embedding. Original relation
symbols already satisfy the native \`rel_iff\` free-amalgam
axiom.

For a domain relation on an injective root enumeration
\(x:\mathrm{Fin}(m)\to C\), a witness to the nonempty
native fibre \(G_C(x\circ r)\) gives an actual output y.
The native full \`func_iff\` free-amalgam axiom places
the entire input tuple and y in one side, say E:
\[
 x\circ r = i_E\circ a,\quad y=i_E(b),\quad
 b\in G_E(a).
\]
Since \(r\) is SURJECTIVE, every distinct root vertex
x(j) appears among these input coordinates. Hence there
is a tuple \(w:\mathrm{Fin}(m)\to E\) satisfying
\(x=i_E\circ w\) and \(a=w\circ r\). The injectivity
of x implies w is injective; its function fibre
contains b. Thus the complete domain relation occurs
on w in E.

For an output-graph relation tuple t, the same
\`func_iff\` splits its native output incidence.
The distinct input prefix factors as w via the
surjective r, while the last output coordinate is
the corresponding side output b. Hence
\(t=i_E\circ\mathrm{funcTuple}(w,b)\),
and the OLD output-graph relation occurs on that
side tuple.

The argument is symmetric for F. Conversely, any
positive OLD relation of either source side maps into
the full target via its FULL native function embedding;
domain nonemptiness and output incidences are preserved.
Since the side maps already preserve and reflect
relations and full function fibres, we have a full
relational free-amalgam diagram of OLD pattern graphs,
not merely a one-sided homomorphism.

## Reusable root lifting lemma

For ANY injection \(i:E\hookrightarrow C\),
surjective equality-pattern map r, root x and
argument tuple a satisfying \(x\circ r=i\circ a\),
there exists the UNIQUE tuple w of source root
vertices with \(x=i\circ w\) and \(a=w\circ r\).

Pick one argument position for each root coordinate
using surjectivity of r, and use injectivity of i to
check independence of the chosen position. The proof
has no function semantics and handles zero-length
domains where a surjective map to an empty root exists.

This combinatorial helper can be reused throughout
the faithful functional/U-closed proof comparison.

## Adversarial referee audit

* **Surjectivity of r is essential.** An unused root
  vertex x(j) could lie outside the chosen source
  side. Merely having a map from input positions to
  root vertices is insufficient.
* **Full function free amalgam is essential.** A
  relation-only free amalgam plus arbitrary
  cross-side native outputs can have an old
  domain/output tuple spanning the two sides.
* **Full source-side embeddings are essential**
  for the reverse direction and for reflection of
  domains on input tuples inside one side.
* **Repeated input variables:** the same root
  vertex may occur many times among original
  arguments. The exact surjection/injective-root
  factorization correctly preserves all repetitions.
* **Empty arities/nullaries:** the generic OLD
  domain/output relation cases remain meaningful;
  the *fresh positive-root U-rules* still exclude
  nullaries, which are handled separately in
  the closure dictionary.
* **Genuinely multivalued functions:** the proof
  picks one output at a time and does not assume
  singleton fibres or reduce to a Boolean
  nonempty-domain record.
* **No closure hull/rank inflation:** root tuples
  and all side witnesses are on the EXACT original
  source carrier.
* **Result does not finish TARGET completion:** source
  free amalgamation in tagged presentation is
  compatible with the already verified corrected
  2019 induction, but an arbitrary strict B-tree
  TARGET root completion still needs the actual
  history-dependent predecessor/relative
  synchronization. The K2 parity and arbitrary-stage
  C5 counterexamples remain genuine.

## Lean acceptance

Prove a reusable
\`Structure.surjectiveInputRoot_factor\`.
Then prove
\`Structure.IsFreeAmalgam.patternGraph\`
by old symbol cases, using native
\`hFree.rel_iff\` and \`hFree.func_iff\`.
The latter gives the input/output side decomposition;
the root-factor helper recovers a full injective
equality-pattern root tuple in the selected side.

Combine with the checked generic #428 fresh-tagged
free-amalgam lemma to obtain the direct canonical
tagged full function-language free-amalgam theorem.
Run full umbrella build plus named axiom audits.
Only genuine SOURCE gluing geometry is claimed;
the published manuscript remains unchanged.
