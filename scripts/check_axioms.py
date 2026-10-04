"""Accept only Lean's usual logical axioms in the audited theorem closure.

Usage: check_axioms.py LOG [AUDIT_SOURCE ...]
The default source remains CheckAxioms.lean for backwards compatibility.
"""
import pathlib
import re
import sys

text = pathlib.Path(sys.argv[1]).read_text()
sources = sys.argv[2:] or ["CheckAxioms.lean"]
expected = set()
for source in sources:
    expected.update(re.findall(r"^#print axioms (\S+)", pathlib.Path(source).read_text(), re.M))
found = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
    found[name] = {a.strip() for a in axioms.split(",") if a.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    found[name] = set()
assert set(found) == expected, f"Missing or unexpected audit results: {expected ^ set(found)}"
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in found.items():
    assert axioms <= allowed, f"Unexpected axioms in {name}: {axioms - allowed}"
print(f"Checked {len(found)} declarations; only the standard logical axioms occur.")
