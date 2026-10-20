# Partial-function projections through the singleton U-closed presentation: the cross-part coherence bit

**19 October 2026 — English proof and independent adversarial audit**

The user-observed equivalence between the functional iterated
partite construction and the verified U-closed construction is
correct for SOURCE closure, full embeddings and genuine free
amalgams. PRs #426–434 formalize that exact vertex presentation.

There is ONE indispensable semantic distinction when translating
the original-2019 PARTIAL-HOMOMORPHISM projections: an original
multivalued primitive operation has ONE definedness condition
("some output part is active"), while its singleton split uses
SEPARATE partial functions (F,q), one for every output part q.

Consequently blindly replacing every original partial
homomorphism-embedding by independent partial maps for the
split symbols is insufficient to recover the original map.
We must retain a simple cross-output-part coherence condition.

## The genuine original-2019 convention

Let B be a transversal native partite System over P, let D
be its functional control on P, and p=B.part. Use partial
set-valued operations where an empty fibre is UNDEFINED.

An original partial homomorphism p:B→D preserves all
relations and, for each original F and x with F_B(x)≠∅,
must satisfy the WHOLE-FIBRE equality

     p[F_B(x)] = F_D(px).

At inputs with empty F_B(x), the target fibre may be
defined. This is the checked original-2019/EHN
source-defined convention, and must remain so.

## Direction A: original partial maps split correctly

Let B^P and D^P denote the canonical singleton-output-part
presentations, D^P formed from transversal(D).

Suppose p:B→D is an original partial homomorphism.
Fix any split symbol (F,q) with a nonempty source q-fibre.
Then the ORIGINAL F_B(x) is nonempty, so whole-fibre
equality applies. Restrict both sides of that equality
to the part q. Since p=B.part, we get

       p[F_B^q(x)] = F_D^q(px).

This establishes an original partial homomorphism
B^P→D^P, including all positive function incidences,
without asserting domain reflection at source-undefined
inputs. No singleton-original restriction is needed.

## Reverse direction: preserve cross-part activity

Define \`DefinedOutputPartCoverage B D\` to mean:
whenever the ORIGINAL source fibre F_B(x) is nonempty,
every output part q required by the CONTROL
F_D(px) is realized by SOME original source output
y∈F_B(x) with part(y)=q.

If the split projection is an original partial
homomorphism and this coverage condition holds,
then the ORIGINAL projection is original partial.

Proof: for y∈F_B(x), take q=part(y). The split
(F,q)-fibre is defined, hence the split
partial-homomorphism equality sends p(y) into
F_D^q(px), proving forward inclusion of
p[F_B(x)] in F_D(px). Conversely, every
q∈F_D(px) is lifted by DefinedOutputPartCoverage.
The two inclusions give full ORIGINAL fibre
equality on every defined original input.
The original relations are unchanged by the split.

**Crucially the converse without coverage is FALSE.**

Consider unary F, source vertices x,a with
part(x)=p, part(a)=q, and original source
F_B(x)={a}, while the target control
F_D(p)={q,r} for distinct output parts q,r.
The source (F,q)-fibre is defined and maps
onto the control (F,q)-fibre; source
(F,r)-fibre is undefined, so its independent
2019 partial-map condition is vacuous.
Hence all split partial conditions can hold,
although original whole-fibre equality fails
because the extra required r-output is not
realized by any source F-output.

This is a semantic counterexample, not an
obstruction to the FULL source dictionary.
The correct EHN projection excludes this
case whenever the ORIGINAL source operation
is defined: verified EHN fibre exactness
gives precisely DefinedOutputPartCoverage.

## Relation to the verified weak/U-closed programme

1. **Original native EHN map ⇒ split original-partial map**.
   Use the checked equivalence
   \`originalPartialHE_iff_EHN\` and Direction A.
2. **Evolving source stages:** the fixed part carrier P
   makes every singleton label q meaningful across
   the genuine Hales–Jewett power and full attachments.
3. **Weak tests:** the induced AMBIENT full-root tags
   retain which original input fibres are defined
   before restricting outputs. Do not replace this
   by the weaker per-(F,q) source-definedness bits
   after weak restriction.
4. **No automatic EHN HE after splitting:** Direction A
   proves the original-partial homomorphism law, not
   full embedding on every split-irreducible test.
   The latter requires separate irreducibility
   comparison in the U-closed dictionary.
5. **The corrected 2019 profile construction** uses
   shared root-profile tags exactly to restore
   compatibility of definedness and completions.
   We should transfer THAT invariant rather than
   make separate unrelated strict-tree completions
   for arbitrary nonclosed weak source roots.

## Lean acceptance

Prove
- \`System.definedOutputPartCoverage\`;
- \`System.originalPartial_projection_split\`;
- \`System.originalPartial_projection_iff_split_and_coverage\`;
- \`System.definedOutputPartCoverage_of_EHN\`.

All operate in the actual native function language,
for arbitrary arity, multivalued outputs and nullaries,
without closure-hull/rank inflation.
Audit named Lean axioms and full umbrella build.

Do not claim the unconditional full native iterated
n-pass theorem until the actual finite HJ
attachment-list history/target-root step is constructed.

## Further kernel interface: weak EHN projection transports without domain reflection

Every original native weak partite map \(p=B.part\) is a weak
homomorphism of all per-output-part singleton fibres:
a witnessed native F-output y in part q projects
to a witnessed (F,q)-output in the split control.
The relation symbols are unchanged. Thus
\`System.weak_projection_split\` and
\`System.weaklyPartite_splitProjectionWeak\`
give this unconditional GLOBAL WEAK map for arbitrary
arity/multivalued functions.

Neither declaration asserts FULL target-fibre equality
at source-undefined inputs or the separate EHN
full-on-irreducibles condition in the split language.
The latter requires the actual irreducible-test
dictionary, not an unjustified equivalence of
independent split partial domains.
