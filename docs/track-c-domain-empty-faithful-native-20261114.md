# Track C / Appendix A — faithful native Dom/Empty encoding

14 November 2026. One additional candidate Lean module for English
proof F1 and F3 of
\`appendix-a-track-c-english-cover-pullback-proof-20261113.md\`.

New native language has the SAME original function symbols, plus
separate input relations Dom_F and Empty_F. The canonical encoding
of A : PartialSetStructure L V has:
- undefined (none): native value ∅; Dom false; Empty false;
- defined empty (some ∅): native value ∅; Dom true; Empty true;
- defined nonempty (some U): native value U; Dom true; Empty false.

Two full embedding dictionaries preserve the **same vertex map**.
The EHN positive map theorem uses **exact nonempty-fibre EHN**
transport for nonempty defined source values and the extra
positive Empty relation for defined-empty source values.
Undefined source inputs need NOT map to undefined target inputs.

**No theorem yet** that arbitrary native structures are legal,
that legal objects are closed under the particular native loose
free-amalgam B-cover pass, or that all full native Ramsey
arrows transfer to the original Option(Set) category.
These are the remaining F2/class-closure/arrow gates.

The three new declarations have named axiom checks.
No admissions or manuscript changes; draft until exact-head CI.
