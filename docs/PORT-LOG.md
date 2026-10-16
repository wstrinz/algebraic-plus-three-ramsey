# Port log: Theorem B(b) and OpenAI's EuclideanRamsey closure, Lean v4.35.0-rc2

**Pins.**
- Source of this project's Lean files: rope AV5 of spherical-ramsey v1.1.0
  (github.com/wstrinz/spherical-ramsey, commit `09f88943111035c1764169cfd96bde7340aff687`,
  `ropes/av5/Rope/`; doi:10.5281/zenodo.23396387).
- OpenAI: openai/math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, the 28 modules of
  `OAI.Combinatorics.EuclideanRamsey.Main`'s import closure (listed in `NOTICE`).
- From: Lean v4.34.1 / Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` (OpenAI's pin).
- To: Lean **v4.35.0-rc2** / Mathlib **`065356127b1dc0016f66b7283ce0ce2c4055aa55`** (Mathlib tag
  `v4.35.0-rc2`, the PalomarTemplate pin). All nine Lake packages are pinned to full SHAs in
  `lake-manifest.json`.

Why: Palomar requires every `.lean` file to use the Lean module system and a toolchain of at least
v4.35.0-rc2, and its judge is the toolchain's own `lake comparator`.

## 1. OpenAI's files: header-only changes

These are the same 28 ported files as in mobius-ramsey (byte-identical to them). Below their
headers they are byte-identical to the rope's vendored copies, which are byte-identical to
upstream. `python3 scripts/port_to_modules.py --notice-oai OAI/Combinatorics/EuclideanRamsey/*.lean`,
run once on the upstream files, made in each file:

| Change | Lines per file | Why |
|---|---|---|
| Apache-2.0 modification notice, a plain comment before `module` | +8 | Apache-2.0 §4(b); Palomar allows ordinary comments before the header |
| `module` before the imports | +1 | every file must use the module system |
| `import X` → `public import X` | ±1 per import (each OpenAI file has one) | dependants see the imported declarations |
| `@[expose] public section` after the imports | +1 | every declaration stays public and every definition keeps its body visible downstream: the pre-module behaviour |
| blank lines around those | +2 | layout |

**No other line changed.** `REPRODUCE.md` §5 replays this against upstream.

## 2. This project's files (`AlgebraicPlusThree/`)

Copied from the rope's `Rope/` directory, then:

1. **Renamed** (and their imports rewritten by `scripts/port_to_modules.py`):

   | Before (rope AV5) | Module now |
   |---|---|
   | `Rope.SixPointAlgebra` | `AlgebraicPlusThree.SixPointAlgebra` |
   | `Rope.SixPointCircle` | `AlgebraicPlusThree.SixPointCircle` |
   | `Rope.SixPoint` | `AlgebraicPlusThree.SixPoint` |
   | `Rope.AlgPlusThreeAlgebra` | `AlgebraicPlusThree.AlgPlusThreeAlgebra` |
   | `Rope.AlgPlusThreeCore` | `AlgebraicPlusThree.AlgPlusThreeCore` |
   | `Rope.AlgPlusThree` | `AlgebraicPlusThree.AlgPlusThree` |
   | `Rope.MathlibBridge` | `AlgebraicPlusThree.MathlibBridge` |
   | `Rope.MathlibStatement` | `AlgebraicPlusThree.MathlibStatement` |

   The rope's root module `Rope.lean` (two imports and a comment) is replaced by `Solution.lean`.
2. **Namespace.** The namespace of the bridge and of the Mathlib-form statements is renamed
   `SphericalRamsey` → `AlgebraicPlusThree` (the `namespace`/`end` lines of `MathlibBridge.lean` and
   `MathlibStatement.lean`, four lines). The main theorem keeps its name,
   `OAI.EuclideanRamsey.ramsey_alg_plus_three`.
3. **Ported** to the module system by the same header pass as OpenAI's files (without the Apache
   notice: `module`, `public import`, `@[expose] public section`).
4. **Comments and docstrings** were edited to describe this package: references to the rope's
   other files and to the originating release's paths now name spherical-ramsey v1.1.0, the
   docstrings of the six-point theorem credit JD-Jones-ASES's prior work, and
   `SixPointCircle.lean` states its Apache-2.0 licence.
5. **New:** `AlgebraicPlusThree/Axioms.lean`, six `#print axioms` commands (the two advertised
   theorems, the satisfiability witness, the bridge, and the six-point theorem).

**No statement or proof line changed.** Checked mechanically: with comments, blank lines and the
header lines (`module`, `import`/`public import`, `@[expose] public section`) removed, each of the
eight files equals the rope's file line for line, after renaming `SphericalRamsey` to
`AlgebraicPlusThree` in the rope's four namespace lines (809 code lines in all).

## 3. New files

| File | What |
|---|---|
| `Challenge.lean` | Mathlib-only statement surface: OpenAI's `Space`, `Congruent`, `Ramsey` verbatim from `Model.lean`; the two advertised statements with `sorry`, identical to the rope's Comparator challenges `AV5Challenge/Main.lean` and `AV5Challenge/Mathlib.lean` (checked by `scripts/check_statements.py`; the rope's third challenge statement, the satisfiability witness, is proved here but not advertised) |
| `Solution.lean` | `public import AlgebraicPlusThree.AlgPlusThree` and `AlgebraicPlusThree.MathlibStatement` |
| `comparator.json` | the two theorems, no definition holes, the three standard axioms, `enable_nanoda` |
| `tests/controls/` | five negative controls (four challenge or solution files generated from `Challenge.lean` by `scripts/make_controls.py`, each with one edit; the fifth uses `Challenge.lean` as its own solution) and their runner |
| `scripts/port_to_modules.py` | the header pass above (mobius-ramsey's script with this package's renames) |
| `scripts/check_statements.py` | the statement comparison against the originating release |
| `scripts/check-lean-sources.py`, `scripts/verify-comparator.sh` | PalomarTemplate `2891de4c`, unmodified |

The rope's other files are not carried over: its own `REPRODUCE` (stock Comparator, Landlock),
its Comparator configs and controls (replaced by `comparator.json` and `tests/controls/`), its
`MANIFEST`, and its two challenges for OpenAI's own theorems (`classification`,
`ramsey_cospherical`), whose modules (`Spherical.lean` and its imports) are outside the import
closure needed here.

## 4. Build at the new pin

All modules built at the new pin on the first attempt, on a fresh GitHub runner: no proof edits
for the Lean and Mathlib drift `v4.34.1 / d13f23b7 → v4.35.0-rc2 / 065356127b`, no errors, and no
warnings other than the three intended `declaration uses 'sorry'` warnings of `Challenge.lean`.
`REPRODUCE.md` has the measured times.
