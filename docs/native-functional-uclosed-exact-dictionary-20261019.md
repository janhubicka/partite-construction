# Exact native functional closure is the 2019 U-substructure condition

**19 October 2026 — English proof and adversarial audit before Lean.**

This addresses the guiding observation that the genuine-function
iterated partite construction and the corrected relational
U-closed construction are two presentations of the **same closure
geometry**. The purpose is to give a kernel-checked, exact
dictionary, not another conditional strict target B-tree theorem.

The already checked \`PartialFunctionPatternGraph2019\`,
\`PatternClosureTags2019\`, \`PatternClosureCanonical2019\`,
\`PatternCompleteRootExtraction2019\` and
\`WeakPatternDomainBridge2019\` provide the canonical
relational encoding of genuine partial set-valued functions:
one equality-pattern domain and output graph relation for
each primitive function, with a fresh closure relation for
each FULL positive-root pattern.

## I. Exact theorem for arbitrary multivalued functions

Let L be a function/relation language with **positive
function arities**; let A be a FINITE genuine L-structure,
with arbitrary (possibly multivalued) function fibres.
Let E be its canonical tagged pattern expansion

    E = patternTagExpansion(A.patternGraph)

and let U=L.patternClosureRules be the **already defined
2019 closure description** on this exact relational
language. For ANY vertex subset S⊆A, without assuming
it is closed, we claim the equivalence

\[
    A.\mathrm{IsClosed}(S)
      \quad\Longleftrightarrow\quad
    \mathrm{IsUSubstructure}(\mathcal U,E,S).
\]

The right-hand side is Definition 2.22 of All Those
Ramsey Classes: *every genuine tagged closure tuple
whose designated input root is contained in S has
its ENTIRE tuple in S*. Both sides refer to the
literal exact vertex set S, not to its generated hull.
The theorem does **not** assume singleton-valuedness,
transversal output parts, or target-domain reflection.

### Forward direction

Take any fresh tag \(\tau_{q}\) of E, associated to
a positive FULL old input root pattern q, and any
tagged output tuple \(t\). Its old output-graph
incidence means exactly that the last vertex y of t
belongs to the actual ambient native function fibre
F_A(x), where the root prefix enumerates distinct
argument vertices (and the equality-pattern argMap
records repeated inputs). If all root vertices of t
lie in S, then each primitive argument x_i lies in S.
Native function-closedness of S forces y∈S.
All remaining tuple coordinates were root coordinates
and were already in S. This proves the U-substructure
closure implication for every rule.

### Reverse direction

Fix F, arbitrary native argument tuple x whose
entries lie in S, and an actual y∈F_A(x).
Use the already checked exact equality-pattern
factorization: x=e∘r with e:Fin m→A injective,
r:Fin arity→Fin m surjective, and range(e)=range(x).
Since the function arity is positive, m>0.

The OLD equality-pattern domain relation is active
on e, witnessed by y, and its output graph relation
holds on the tuple (e,y). Extract the COMPLETE FULL
induced OLD root pattern q from this active domain.
The canonical tagged expansion contains the fresh
closure tuple \(\tau_q(e,y)\), whose designated root
is precisely e. Since r is onto, each root vertex
e(j) is some original argument x(i), so e(j)∈S.

Apply the U-substructure condition to this exact
tagged tuple. Its LAST vertex is y, hence y∈S.
This holds for every original output of every F
and gives native function-closedness of S.

## II. Exact induced U-closedness dictionary for singleton functions

If A is also SINGLETON-VALUED, the already certified
\`patternTagExpansion_isUClosed\` says that E is
genuinely U-CLOSED. Thus the checked 2019 Lemma
2.23(1), \`IsUClosed.induce_iff_USubstructure\`,
gives immediately

\[
 A.\mathrm{IsClosed}(S)
    \quad\Longleftrightarrow\quad
 \mathrm{IsUClosed}(\mathcal U,E|S).
\]

This is the exact native-function ⇔ U-closed-induced
comparison that the iterated Appendix A proof needs.
It holds on the **same vertices S** and its induced
tagged data retains the original ambient active
domain relation even when the native weak restriction
on S has lost all outputs.

That final distinction is essential. The already
checked \`WeakPatternDomainBridge2019\` proves:
* original output-graph tuples restrict exactly
  with native weak source fibre incidences;
* an ambient domain relation can remain active
  after native weak restriction becomes undefined;
* when S is genuinely closed, the two domain
  records agree.

Hence the general weak induction carries the induced
AMBIENT tagged pattern data, not a freshly recomputed
domain relation. That is exactly how the U-closed
construction treats weak induced tests.

## III. Independent adversarial audit

1. **Multi-output functions:** In Section I, each
   ambient value y yields its own tagged tuple; the
   U-substructure condition requires ALL outputs
   remain inside S. A single nonempty-domain bit is
   insufficient and is not used. The singleton
   hypothesis enters ONLY Section II for U-closedness
   of the whole canonical tagged structure.
2. **Repeated inputs:** The distinct-root equality
   pattern e∘r uses surjective r, avoiding any
   erroneous assumption that the original input
   tuple is injective. If r is not surjective, an
   unrelated root vertex need not be in S; its
   surjectivity is critical.
3. **Nullaries:** The literal 2019 closure-description
   rules REQUIRE a positive root. The equivalence
   stated here therefore assumes every primitive
   function has positive arity. Nullary symbols
   require the separately checked canonical nullary
   root and must not be silently covered here.
4. **U-closed target:** A general multivalued A may
   yield multiple tagged outputs for a single root
   and need NOT be U-closed. The correct general
   claim is only the relative substructure
   equivalence of Section I, not the stronger
   induced U-closedness equivalence of Section II.
5. **Weak versus ambient domain:** A unary F(a)={b}
   with S={a} is not closed. The ambient domain tag
   remains present in E|S even though the recomputed
   native weak function fibre is empty. Replacing
   E|S by the freshly decoded native weak pattern
   would give a FALSE dictionary.
6. **No generated closure/rank inflation:** All tagged
   domain and graph relations are tuples on the
   original exact carrier. Constructed U-closure
   hulls, if used elsewhere, do not enter either
   side of the theorem.
7. **No automatic target root compatibility:**
   Equivalence of the SOURCE geometry by itself
   does not construct a common STRICT full-functional
   B-tree completion for arbitrary HJ histories.
   The verified C5 and marked-edge parity audits
   still prohibit declaring the unrestricted
   maximal-mixed strict target theorem proved.
8. **Actual native HJ power and full attachments:**
   Those operations already exist as genuine
   function-language systems. The next proof
   should transport this exact tagged closure
   dictionary through their FULL attaching maps
   and compare the corrected 2019 weak-test
   induction step-by-step; no alternative
   relational Ramsey construction is authorized.

## Lean verification plan

Prove:
1. \`Structure.isClosed_iff_taggedPattern_isUSubstructure\`
   for all finite positive-arity genuine function structures,
   allowing multiple values.
2. \`Structure.isClosed_iff_taggedPatternInduce_isUClosed\`
   with singleton-valuedness, using the checked
   canonical-U-closed theorem and 2019 Lemma 2.23(1).
3. A named axiom audit for both statements.

This is the missing **structural equivalence bridge**.
It does not certify the complete native n-pass theorem
or alter the frozen survey text.
