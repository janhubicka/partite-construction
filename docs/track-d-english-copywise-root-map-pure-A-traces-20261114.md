# Track D — English first: source A-copywise root retraction suffices on pure tests

**14 November 2026.** Supplement to the English-first exact pure-copy
trace theorem in PR #664. This is a source-side positive criterion;
the frozen Nešetřil programme survey Appendix A and old collaborator
TODOs remain untouched.

## The lemma

Take a genuine FULL relation/function-language free source amalgam

    Whole = Left *_Root Right

with full embeddings iL, iR, sL, sR. Let S⊆Whole be an EXACT weak
tested set lying entirely in the right source side, in the literal
sense that every tested vertex is iR(b) for some b∈Right.

We need not have an EHN retraction r:Left→Right. Assume only a
plain vertex map r:Left→Right satisfying:

1. it fixes the true function-closed gluing root *pointwise*:
   r(sL(d))=sR(d) for all d∈Root;
2. it is **A-copywise full**:
   for each genuine FULL embedding gamma:A↪Left there is a
   genuine FULL embedding gamma_R:A↪Right such that
   gamma_R(a)=r(gamma(a)) for ALL a∈A.

No preservation of arbitrary source relations, no function-fibre
equalities, no global injectivity, and no condition on r at
arbitrary irreducible sources other than the chosen A copies is
required. In particular this is strictly weaker than demanding
that r be EHN (although every EHN r has this property if A is
irreducible).

**Conclusion.** Every FULL left-side A-copy gamma has a FULL
right-side A-copy gamma_R agreeing on all its actual tested
positions:

    iR(gamma_R(a)) = iL(gamma(a))
    whenever iL(gamma(a))∈S.

### Complete proof

Fix gamma and its full image gamma_R under r. For a tested
vertex iL(gamma(a))∈S, purity of S gives some b∈Right with

    iL(gamma(a)) = iR(b).

The **actual source free-amalgam overlap axiom** supplies d∈Root
with gamma(a)=sL(d) and b=sR(d). By the root-fixing and
A-copywise properties,

    gamma_R(a) = r(gamma(a))
               = r(sL(d))
               = sR(d)
               = b.

Applying iR gives the desired exact vertex equality. No weak
test is closed, and no unverified root-isolation or generation
statement is used.

The checked PR #664 theorem then transfers every old-side
target FULL A-copy certificate to Whole, conditional only on
the existence of the old weak map and its tested pointwise
agreement. This is the exact pure-copied-side A-copy protection
required for the weaker history-free strict functional invariant.

## Why this is useful—and what is still open

The known single HJ parameter-coordinate map r is genuinely EHN,
so it automatically satisfies this weaker copywise criterion.
For several lines with no common parameter coordinate, a
global EHN r may be impossible even though it could still
be possible to preserve each A-copy separately. This identifies
a potentially easier source combinatorial goal for the actual
ordered HJ finite line family.

**Crucial limitation:** the theorem does not construct r or
gamma_R for arbitrary earlier lines. Pairwise HJ intersection
control alone does not imply that partial A-index maps extend to
FULL A embeddings. A proper trace H⊂A can fail to extend to
an automorphism of A, so replacing A-copywise fullness by mere
matching of control parts would be wrong. Nor is the map r
required or shown to preserve the full source structure.

The actual unrestricted native n-pass theorem still requires
this new source condition, or a different weak-trace profile,
at the maximal projected-image pure stage. No additional
generator rank is charged; no Option(Set) defined-empty mask
is conflated with source-undefined empty fibres.

## Lean gate

Prove `IsFreeAmalgam.crossSideFullATraces_of_copywise_root_map`
in the true function language and a corollary using the checked
`pureRight_ambientACopies_of_crossSideTraces`. Verify the
elementary EHN→A-copywise sufficient condition.
Use root-level named `#print axioms` checks; keep draft until
exact-head complete Lean/axiom/source gates pass.
