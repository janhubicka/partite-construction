# Track D — English proof FIRST: exact weak functional mixed gluing without projected-history diaries

**12 November 2026.** This is an independent proposed replacement of
the overstrong strict functional *history-preserving* induction invariant.
The original numbered Nešetřil programme survey Appendix A and all
collaborator TODOs remain frozen.

## 1. Proposed weaker invariant

For a genuine full relation/set-valued-function source C, a finite
weak vertex set S⊆C, an irreducible source A and irreducible Base=B,
define an **ordinary strict ambient weak-tree certificate**:

  (i) a genuine full-functional strict tree T of B-copies;
  (ii) an `IsAmbientRelativeWeakHE C S T f` on the EXACT weak set S;
  (iii) for every FULL embedding e:A↪C there is a FULL target
        embedding eT:A↪T, contained in an irreducible B constituent,
        with eT(a)=f(e(a)) whenever the true source vertex e(a)
        lies in S.

This is `SetAmbientRelativeWeakTreeWitness A Base C part S []`,
with an **EMPTY** projected-history list. It asks neither for a
global target part labelling nor an exact `ProtectedAMark` on
unoccupied positions. For genuinely function-closed S, its weak
map converts to an original-2019 source-defined partial HE of the
FULL induced S.

The `AtMostNoHistory n` condition means this certificate exists
for EVERY literal finite S with |S|≤n. This candidate is strictly
weaker than the previously studied `AtMost n` condition requiring
certificates for arbitrary finite projected histories.

## 2. Mixed weak-test gluing theorem: NO closedness of S

Let `Whole=Left *_Root Right` be a genuine FULL native
functional free amalgam and fix an arbitrary literal weak vertex
set S⊆Whole. The two exact side weak sets are

    S_L = i_L^{-1}[S],    S_R = i_R^{-1}[S].

Let `pWhole:Whole→D`, `pL:Left→D`, `pR:Right→D` be the true
original-control part maps, with `pWhole∘i_L=pL` and similarly
for the right. The side maps pL and pR are EHN projections
(source-defined, not total-fibre).

Fix a FULL control placement α:A↪D and suppose every actual
common-root vertex projects inside α(A), i.e. for every r∈Root
there exists a∈A with `pWhole(i_L(s_L(r)))=α(a)`.
This is automatic for the actual native selected A-support cut.

Assume the control D has ordinary strict **ambient weak-tree**
certificates, with *empty histories*, on the EXACT projected
side weak images

    I_L = pL[S_L],   I_R = pR[S_R].

No closedness of I_L,I_R or of the occupied A subsets is requested.

Extract each control certificate
`(T_i,g_i,hWeak_i,hCopies_i)` and use the selected FULL
α-copy certificate to choose a **FULL target A mark**
`m_i:A↪T_i`, contained in an irreducible B-piece, with

    m_i(a)=g_i(α(a))  whenever α(a)∈I_i.

This occupied relation is all that is needed for alignment on the
source overlap. Note carefully: the ordinary certificate does NOT
promise `g_i(z)≠m_i(a)` if z∈I_i but z≠α(a).

Next pull each exact control weak map `g_i:I_i→T_i`
back along the actual EHN side map p_i on the exact weak
source S_i. The VERIFIED
`IsAmbientRelativeWeakHE.pullback_ehn_exact` gives
`f_i:S_i→T_i` satisfying the genuine ambient-relative
set-valued function law; the VERIFIED
`SetAmbientRelativeWeakTreeWitness.pullback_ehn`
also supplies ambient-full-A-copy intersection certificates
for these side maps, assuming A irreducible. Neither pullback
adds any source vertices or reflects source-undefined function
domains.

For any common root r whose vertex belongs to the exact S,
choose a∈A with `α(a)=pWhole(i_L(s_L(r)))`. The side
projection identities and the occupied mark equations give

    f_L(s_L(r))=m_L(a),   f_R(s_R(r))=m_R(a).

Now form the FULL FUNCTIONAL target free amalgam

    T = T_L *_{A} T_R

over the two full **TARGET** embeddings m_L and m_R. The true
`FreeAmalgam.treeAmalgam` theorem makes T a strict tree
of B-copies, since each A mark lies in an irreducible
constituent target B-copy.

Compose side weak maps with the full target embeddings
`j_L,j_R`. Their values agree on every ACTUAL common source
root vertex that occurs in S, by the full target amalgam overlap
equations above. The VERIFIED
`IsFreeAmalgam.ambientRelativeWeakHE_glue`
constructs one ambient-relative weak HE `f:S→T`;
it respects every surviving source function incidence and the
ENTIRE set-valued fibre when all ambient outputs survive in S.
The source weak test S itself need NOT be function-closed.

Finally the VERIFIED
`IsFreeAmalgam.ambientACopyIntersections_glue` transfers the
two side ambient A-copy certificates to the whole source:
irreducibility of A forces each genuine full ambient A-copy
into one FULL source side. Compose its target embedding with
the full target-side inclusion to obtain the required full A
constituent in T.

Thus the weaker `AtMostNoHistory` witness is preserved
by this genuinely mixed weak step. We deliberately choose
`history=[]` and need no cross-side history kernel condition.

## 3. Why this is a potentially iterable replacement

Under a rank-m `AtMostNoHistory` predecessor on D, a truly
mixed exact weak S of |S|≤m+1 has both side TESTED subsets of
size ≤m; hence the two exact projected side images each have
at most m vertices, so the lemma applies without any
generator-rank inflation. Pure old-copy tests inherit the
old stage's rank-(m+1) certificate, and pure coordinate-power
tests admit an ambient-relative weak one-copy strict Base-tree
witness via the verified EHN power projection A→B; all
actual full ambient A-copies are protected by irreducibility.

If each pure case, the exact mixed cardinal drop, and the
finite ordered Hales–Jewett attachment trace are packaged
with the above no-history mixed-gluing lemma, one full
native functional Hales–Jewett pass would raise
`AtMostNoHistory m` to `AtMostNoHistory (m+1)`
without a colliding-root or nonclosed-boundary exception.
One can then attempt n passes without projected histories.

**This last whole-pass implication is a NEW PROOF TARGET**,
not a claimed theorem until every pure-step, trace and
Ramsey/class bridge compiles in Lean. In particular the
existing verified history-preserving partial-step theorem
cannot be re-labelled to obtain this result automatically.

## 4. Adversarial boundaries

A. **Not the old strong history invariant.** The free target
gluing may identify a source vertex at control label u on
the left with a vertex at a different label v on the
right through an UNoccupied target A-mark position.
The absolute and ambient-relative weak HE permits that,
but `SetRespectsProjectedHistory` fails. Hence the proof
does not establish the strong printed TODO property or
fix a globally protected α mark. Do NOT smuggle the
no-wrong-hit forward implication into a hypothesis.

B. **No closedness inflation.** The exact S,S_L,S_R and I_L,I_R
are literal weak vertex sets; never replace them with
a function-generated closure and charge its larger vertex
cardinality to the same m.

C. **Correct source function notion.** We retain the 2019
original-partial set-valued convention (all nonempty
source-defined fibres mapped onto target fibres, missing
source domains unconstrained). `Option(Set)` defined-empty
applications remain a separate genuine partial-language
dictionary issue.

D. **Full source cut only.** The gluing theorem concerns a
genuine full functional free-amalgam attachment, not
arbitrary overlapping HJ parameter lines considered
as two free source sides. In a finite ordered Picture
one attaches lines successively to a distinguished
power core, so every individual step has a genuine
binary full free cut.

E. **A irreducible and B-piece containment.** We need the
actual source A irreducibility in order to localize
ambient full A-copies in the source free amalgam;
the target A-copy marks must be full and lie in
irreducible B constituents (supplied by the predecessor).

## 5. Formalization order

1. Prove the **one mixed weak-step** theorem using verified
   exact weak pullback/glue APIs and full control A marks.
   Do not include history preservation in its statement.
2. Define `AtMostNoHistory` and prove side-image cardinal
   transfer for each mixed test at rank m+1.
3. Prove the pure-copy and pure-power cases with the
   **same** ambient-A-copy intersection interface; audit
   finite HJ trace and the full Ramsey-arrow/class
   invariant.
4. Only after complete umbrella CI and named permitted
   axiom checks, claim a full strict native n-pass
   theorem. The separate stronger history-preserving
   invariant may remain false/unnecessary.
