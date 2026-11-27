"""Concatenate the H2Dev modules into one Lean file.

usage: python concat.py <H2Dev dir> <out file> <mode> [existence module name]
  mode = fullenv : first line `import Mathlib`, keeps the local copy gg (pre-flight of name clashes)
  mode = submit  : first line is the step's import, gg replaced by Erdos1160.g, OMA.solution appended
The existence module defaults to ExistStmt (the stub); pass Existence once it is proved.
"""
import re
import sys

src, out, mode = sys.argv[1], sys.argv[2], sys.argv[3]
exist = sys.argv[4] if len(sys.argv) > 4 else "ExistStmt"
ORDER = ["NF", "Comm", "Code", "Lie", "Strict", "Count", "Rigidity", exist, "Main"]
STEP_IMPORT = "import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1"
TARGET = "OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1.H2"

mathlib_imports, bodies = [], []
for name in ORDER:
    text = open(f"{src}/{name}.lean", encoding="utf-8").read()
    for line in text.splitlines():
        m = re.match(r"\s*import\s+(\S+)", line)
        if m and m.group(1).startswith("Mathlib") and m.group(1) not in mathlib_imports:
            mathlib_imports.append(m.group(1))
    body = "\n".join(l for l in text.splitlines() if not re.match(r"\s*import\s", l))
    bodies.append(f"-- ===== {name} =====\n{body.strip()}\n")
code = "\n\n".join(bodies)

if mode == "fullenv":
    head = "import Mathlib\n"
elif mode == "submit":
    head = STEP_IMPORT + "\n" + "".join(f"import {i}\n" for i in mathlib_imports)
    # use the upstream definition instead of the local copy
    code = re.sub(r"/-- A verbatim local copy[^\n]*\n(?:[^\n]*\n)*?noncomputable def gg \(n : ℕ\) : ℕ :=\n(?:  [^\n]*\n)+", "", code)
    code = re.sub(r"\bunfold gg\b", "unfold Erdos1160.g", code)
    code = re.sub(r"\bgg\b(?!_)", "Erdos1160.g", code)
    code += f"\n\ntheorem OMA.solution : {TARGET} := ⟨84, OMA.SimsLite.gg_three_pow⟩\n"
else:
    raise SystemExit("mode must be fullenv or submit")

header = ("-- Step Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H2.R1.H2 (H2 of reduction ...R3.H1.R1.H2.R1)\n"
          "-- Credit: @FarzanAhmedHossain\n"
          "-- Sims-lite: log_p g(p^m) <= (2/25) m^3 + O(m^2), hence g(3^a)^12 <= 3^(a^3 + 84 (a+1)^2).\n")
full = head + "\n" + header + "\n" + code
if '"' in full:
    raise SystemExit("double quote found")
open(out, "w", encoding="utf-8", newline="\n").write(full)
print(out, len(full.splitlines()), "lines")
