from pathlib import Path
import importlib.util
p=Path(__file__).resolve().parents[1]/"scripts/lean_source_scan.py"
spec=importlib.util.spec_from_file_location("source_scan",p)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
assert "sorry" not in m.code_only('/- outer /- sorry -/ axiom -/\ntheorem t : True := by trivial')
assert "sorry" not in m.code_only('def text := "sorry" -- axiom\n')
assert "sorry" in m.code_only('theorem t : False := by sorry')
assert m.code_only('/- a\nb -/\nx').count('\n')==2
try:
    m.code_only('/- unterminated')
except ValueError:
    pass
else:
    raise AssertionError("Unterminated comments must fail closed")
print("Lean source scanner tests passed")
