# Local EHN domain reflection is sufficient for closed projected images

**18 October 2026. English mathematical proof and adversarial audit before Lean.**

The native functional iterated Appendix A construction retains genuine
set-valued functions with transversal output fibres in the actual
partite systems. The previous unary result used the globally FULL
nature of unary EHN maps to infer that projected closed side tests
remain closed. For arbitrary arity that global FULL claim is false
(even for two disjoint copies of a binary-operation B).

There is a more precise, purely LOCAL sufficient hypothesis.

## 1. Exact original-partial/EHN image-closure theorem

Let p:C→D be an EHN/original-2019 partial-function
homomorphism-embedding, preserving positive relations/functions
globally and entire function fibres whenever the SOURCE operation
on an input tuple is defined. Let S⊆C be genuinely function-CLOSED
under every set-valued operation.

Define **local domain reflection on S** to mean:

  for every function symbol F and every input tuple x∈S^arity(F),
  if F_D(p x) has any value, then F_C(x) has a value.

This imposes NOTHING on source tuples outside S and no
global total-fibre homomorphism law.

**Theorem:** Under this local reflection condition, the
LITERAL image p[S] is function-closed in D.

### Proof

Take arbitrary d_i∈p[S] and y∈F_D(d). For each i choose
an actual x_i∈S with p(x_i)=d_i; repeated inputs and
nullaries are covered. The projected target fibre
F_D(p x) is nonempty because it contains y.
By local reflection F_C(x) is nonempty. The already
kernel-verified EHN source-defined fibre exactness then says

             p[F_C(x)] = F_D(p x).

Choose an actual z∈F_C(x) with p(z)=y. Since S is
function-closed and every x_i∈S, we have z∈S.
Therefore y∈p[S]. No generated closure, rank inflation,
global injectivity, or target-domain reflection on other
source tuples was used.

This is valid for **arbitrary function arities** and
**genuinely multivalued** fibres; part transversality is
not required for the image-closure implication itself.

## 2. Relation to the exact weak/U-closed correspondence

In a genuine partite System B over D, the condition says
there are NO **PHANTOM** control outputs at an input tuple
of S: a target-defined operation over projected inputs
with a completely source-undefined fibre.

The already checked \`System.ProjectedUndefinedAtPart\`
provides one output-part witness for such a failure.
A test may still omit actual source output values when
it is NONCLOSED. Those are the separate missing-source
slots identified and transported in PRs #410–#413.

On a genuinely CLOSED source S, missing control
outputs can ONLY arise from local source-domain failure.
This theorem shows that removing that particular failure
is sufficient for the projected test to be closed.
It does NOT imply a common strict target root completion
in the maximal mixed Hales–Jewett history case.

## 3. Adversarial audits

* **The converse is FALSE.** A literal image p[S] may
  be closed even if local domain reflection fails:
  take two full copies of a binary-operation B,
  let S be their entire disjoint union (closed), and
  let p forget the copy index. Then p[S]=B is
  closed, but cross-copy source inputs may be undefined
  although their projected B-inputs are defined.
  Thus the theorem is only one-way.
* **Global source-defined EHN is not enough.** The same
  counterexample shows that a closed source S can
  project to a NONCLOSED subset if the target has an
  operation value at projected S inputs outside p[S].
  The local reflection hypothesis cannot be dropped.
* **Local reflection is strictly weaker than global
  full-fibre surjectivity**, since it is checked only
  on tested tuples whose arguments lie in S. Any
  arbitrary source tuple outside S remains irrelevant.
* **Nullaries:** the argument works with an empty input
  tuple. A target-defined nullary value requires
  source-definedness by local reflection before
  fibre exactness applies. No empty-root exemption.
* **Multivalued functions:** one defined source value
  triggers EHN equality of the ENTIRE projected source
  output set with the entire target output set.
  The proof does not assume singleton fibres.
* **Induction size:** the projected image is exactly
  p[S] and has ≤|S| vertices. There is no closure
  hull or generated-support replacement.
* **No universal strict B-tree existence:** even when
  image closure holds, independent relative target
  completions may have incompatible root histories
  (K2 parity / arbitrary-stage C5 objections).
  Those remain the true unresolved hard case.

## 4. Lean API / acceptance

Define a local no-phantom predicate on an exact subset S
of a real \`Structure\`, with projection p to D.
Prove:

1. a FULL function homomorphism automatically satisfies
   this local predicate, by whole-fibre equality;
2. an EHN projection with local no-phantom property sends
   every genuinely CLOSED S to a CLOSED LITERAL image p[S],
   with no restriction on operation arities or cardinalities;
3. connect the new predicate to the per-output-part
   \`ProjectedUndefinedAtPart\` record on genuine partite
   \`System\` objects (optional but useful for the
   native Picture repair).

Print all theorem axioms and run the complete project CI.
Do not promote the full iterated strict functional sparsening
theorem or change the frozen published manuscript text.

## 5. Exact and uniform strict history pullback from closed predecessors

The verified stage-relative \`AtMostClosedWithPart\` invariant asks for
strict FULL-functional B-tree weak-history completions of every exact
CLOSED finite control test of size ≤n, with all actual ambient full A-copy
intersections and arbitrary histories in one FIXED original P.

Let q:C→D be EHN, with stage projections p_C=p_D∘q, and let A be
irreducible. Fix a genuinely closed exact finite S⊆C of size ≤n
satisfying \`NoPhantomOn C D q S\`. The image q[S] is CLOSED by
Section 1, and its literal cardinal is at most n.

Therefore an \`AtMostClosedWithPart(A,Base,D,p_D,n)\` witness on
the exact q[S] pulls back, using the already verified commuting-parts
EHN theorem, to a strict genuine full-functional Base-tree witness
on the ORIGINAL S. The target still protects all full ambient A-copy
intersections and arbitrary projected histories of p_C:S→P.

This is formalized as
\`AtMostClosedWithPart.exact_pullback_ehn_of_noPhantom\`.
Quantifying the same **visible** local NoPhantomOn assumption over
all closed S of rank≤n gives a uniform predecessor-transfer theorem,
\`AtMostClosedWithPart.pullback_ehn_of_noPhantomOnClosed\`.

Crucially the uniform premise is FALSE for arbitrary all-arity native
EHN stages (cross-copy binary undefined input counterexample). It is
automatic in the unary setting and may be verified on selected
actual Hales–Jewett histories individually in the general case.
No unconditional full functional Picture rank increment or common
strict target root-profile existence is asserted.
