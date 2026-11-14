# F2 legal-native closure under arbitrary full free amalgams

14 November 2026, added to stacked Track C legal-roundtrip draft #670.

The theorem \`IsLegalDomainEmpty.ofFreeAmalgam\` proves direct
preservation of the two Dom/Empty/fibre coherence equations under
a genuine native \`Structure.IsFreeAmalgam\` of arbitrary FULL
root and legal side structures.

The key exact reasoning uses BOTH fields of native freeness:
- \`rel_iff\` localizes active Dom and Empty input tuples
  wholly to a side, including a genuinely defined-empty
  tuple with no function output occurrence.
- \`func_iff\` localizes every nonempty function incidence.
  Full side embeddings preserve the ENTIRE value sets,
  so a side's empty fibre cannot gain opposite-side outputs
  on a shared root.

The theorem imposes no irreducibility of the common root
and no vertex hull. The remaining native loose-tree induction
needs isomorphism invariance at the copy constructor
(the base→copy embedding is surjective). The other missing
F4 gate is transfer of original Option(Set) irreducibility
to this faithful native encoding; plain collapse is false
by the independently recorded mixed defined-empty regression.

Direct named axiom check. Parent #665 and this stacked
module must pass exact-head CI before any merge/green marker.
