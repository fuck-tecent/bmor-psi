import json
import sys
from pathlib import Path
gaps = json.loads(Path("research/gaps.json").read_text(encoding="utf-8"))["gaps"]
problems = json.loads(Path("research/problems.json").read_text(encoding="utf-8"))
gaps.extend(gap for problem in problems.values() for gap in problem['gaps'])
# The imports field grants proof permissions. Statements still use Mathlib alone.
endpoint = next(g["statement"] for g in gaps if g["id"] == "L-goldbach-binary-pointwise-positivity")
lines = [Path("research/strong-goldbach.lean").read_text(encoding="utf-8"),
         Path("research/check-statement-scope.lean").read_text(encoding="utf-8"),
         f"example : StrongGoldbach ↔ ({endpoint}) := strongGoldbach_iff_primeMass",
         "set_option autoImplicit false"]
for gap in gaps:
    lines.extend(("", "-- " + gap["id"], "#check_statement_scope (" + gap["statement"] + ")", "example : Prop := (" + gap["statement"] + ")"))
(Path(sys.argv[1])).write_text("\n".join(lines) + "\n", encoding="utf-8")
print(f"Type-checking {len(gaps)} propositions")
