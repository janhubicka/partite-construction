# Track D — EHN reflection defects need two distinct source inputs

**12 November 2026.** Research/Lean validation note; original numbered
Nešetřil programme survey Appendix A remains frozen. Do not revive
collaborator TODOs or green-mark the unrestricted strict functional
n-pass theorem.

## Actual mathematical conclusion

For any original tuple `xs:I→C` take its FULL native function-closed
hull `H` and a proper FULL free decomposition `H=H_L*_{H_0}H_R`.
The previously verified generator crossing lemma produces an original
tuple coordinate absent from the left side and another absent from the
right. The new lemma proves those coordinates **cannot denote the
same source vertex**: otherwise the free-amalgam cover puts that
vertex on at least one side, contradicting the respective omission.
Thus there are distinct original input vertices `xs(i)≠xs(j)`.

Combining with merged PR #589's original-source-hull decomposition of
a relation reflection failure or a target-defined/source-undefined
function input gives concrete OLD relation/function defect witnesses
requiring **at least two distinct source input vertices**. There is
no source finiteness assumption, no source-undefined/output-extra
confusion, and repeated inputs do not artificially raise the bound.

Hence if every OLD relation and function has arity at most one, ANY
VERTEX-INJECTIVE EHN map is a FULL native embedding. Zero-ary
relation/function symbols are included; such a reflection defect
could not carry two distinct source input vertices. The global EHN
map need not be vertex-injective in general.

## Sharp limit

The result bounds the size of a single original *primitive input* in
each non-collision defect. It does NOT prove a full (arbitrary) root
with more than one generator has two surplus exterior generators,
reduce the generator rank of an entire maximal Hales–Jewett test, or
construct the common history-compatible strict B-tree completion.
The hard mixed case in higher arities remains genuinely open.

Candidate module `EHNDefectMinimumTwoInputs.lean`; four named axiom
checks. DRAFT until exact-head full Lean build and allowed-axiom
inventory pass; no `sorry`, `admit` or new axiom declarations.
