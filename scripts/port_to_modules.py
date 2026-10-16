#!/usr/bin/env python3
"""Mechanical module-system pass for Lean 4 sources (Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2).

applies_to: Lean 4 source files that start with a block of plain `import` lines and contain no
`module` header (the pre-module-system layout of openai/math fd4aeeb2 EuclideanRamsey, and of this
package's own AlgebraicPlusThree sources before the port). Anything else is refused, not guessed at.

For each file given on the command line (idempotence: a file that already has `module` is skipped):
  1. an optional modification notice (`--notice-oai`) is put first, as a plain comment, which
     Palomar allows before the header;
  2. `module` is inserted before the imports;
  3. each `import X` becomes `public import X`, with the pre-port module names rewritten
     (`Rope.SixPoint` -> `AlgebraicPlusThree.SixPoint`, and so on; see RENAMES);
  4. `@[expose] public section` is inserted after the imports, so every declaration stays visible
     downstream and every definition keeps its body visible, as before the module system.
Statements and proofs are not touched. Writes LF.

The files are rewritten in place. Replay of the OpenAI part (REPRODUCE.md section 5,
docs/PORT-LOG.md section 4): download the 28 upstream files listed in NOTICE into a scratch
directory, run
    python3 scripts/port_to_modules.py --notice-oai <scratch directory>/*.lean
and compare the scratch directory with OAI/Combinatorics/EuclideanRamsey/ by diff -r.
"""
import re
import sys
from pathlib import Path

RENAMES = {
    "Rope.SixPointAlgebra": "AlgebraicPlusThree.SixPointAlgebra",
    "Rope.SixPointCircle": "AlgebraicPlusThree.SixPointCircle",
    "Rope.SixPoint": "AlgebraicPlusThree.SixPoint",
    "Rope.AlgPlusThreeAlgebra": "AlgebraicPlusThree.AlgPlusThreeAlgebra",
    "Rope.AlgPlusThreeCore": "AlgebraicPlusThree.AlgPlusThreeCore",
    "Rope.AlgPlusThree": "AlgebraicPlusThree.AlgPlusThree",
    "Rope.MathlibBridge": "AlgebraicPlusThree.MathlibBridge",
    "Rope.MathlibStatement": "AlgebraicPlusThree.MathlibStatement",
}

NOTICE_OAI = """/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/{name};
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`). No other line was
changed; see docs/PORT-LOG.md.
-/
"""


def port(path: Path, notice: bool) -> str:
    text = path.read_text(encoding="utf-8")
    lines = text.split("\n")
    if any(line.strip() == "module" for line in lines[:40]):
        return "skip (already a module)"
    i = 0
    imports = []
    while i < len(lines) and (lines[i].startswith("import ") or lines[i].strip() == ""):
        if lines[i].startswith("import "):
            mod = lines[i][len("import "):].strip()
            imports.append(RENAMES.get(mod, mod))
        i += 1
    if not imports:
        raise SystemExit(f"{path}: no leading import block; refusing")
    rest = lines[i:]
    if any(re.match(r"^\s*import\s", line) for line in rest):
        raise SystemExit(f"{path}: an import after the leading block; refusing")
    out = []
    if notice:
        out.extend(NOTICE_OAI.format(name=path.name).rstrip("\n").split("\n"))
    out.append("module")
    out.append("")
    out.extend(f"public import {m}" for m in imports)
    out.append("")
    out.append("@[expose] public section")
    out.append("")
    out.extend(rest)
    path.write_bytes("\n".join(out).encode("utf-8"))
    return f"ported ({len(imports)} imports)"


def main() -> int:
    args = sys.argv[1:]
    notice = False
    if args and args[0] == "--notice-oai":
        notice, args = True, args[1:]
    for name in args:
        print(f"{name}: {port(Path(name), notice)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
