# Reproducing the checks

Everything below runs from the repository root. Network access is needed for the Lean toolchain,
for step 3 (Lake's dependency repositories and the Mathlib cache), and for steps 2 and 6 (files
from GitHub at pinned commits). Steps 1 to 5 are the Lean result; step 6 checks the provenance of
OpenAI's files.

## 0. Requirements

- **Linux** with `bash`, `python3` and **bubblewrap** (`bwrap`; e.g. `sudo apt-get install
  bubblewrap`). On Ubuntu 24.04, unprivileged user namespaces may first need
  `sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0`. Check that the sandbox starts:
  `bwrap --ro-bind / / --unshare-user --unshare-net true; echo $?` should print `0`.
- **elan** (the Lean toolchain manager), with its `bin` directory on `PATH`. If it is not
  installed, use the official installer (from https://github.com/leanprover/elan):

  ```sh
  curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
  ```

  It installs into `~/.elan`. Non-login shells often miss `~/.elan/bin`, so put it on `PATH`
  explicitly in every shell you use for the steps below:

  ```sh
  export PATH="$HOME/.elan/bin:$PATH"
  ```

  `lean-toolchain` pins `leanprover/lean4:v4.35.0-rc2`; elan installs it on first use. That
  toolchain bundles everything the judge needs: `lake comparator`, `leanexport`, `leanchecker`,
  `nanoda_bin` and `con-ron`.
- **Disk and memory:** about 8 GB of disk (mostly Mathlib's prebuilt files) and about **16 GB of
  RAM**.

## 1. Source rules (Palomar)

```sh
python3 scripts/check-lean-sources.py; echo "exit $?"
```

Expected: no output, `exit 0`. Every `.lean` file uses the module system and is under 10,000
lines.

## 2. The statements are those of the originating release

```sh
python3 scripts/check_statements.py; echo "exit $?"
```

This downloads the Comparator challenges of rope AV5 from spherical-ramsey v1.1.0 (commit
`09f88943111035c1764169cfd96bde7340aff687`) and compares OpenAI's three definitions and the two
theorem statements with `Challenge.lean`, whitespace-insensitively. Expected:

```
SAME      abbrev Space
SAME      def Congruent
SAME      def Ramsey
SAME      theorem ramsey_alg_plus_three (rope AV5 AV5Challenge/Main.lean)
SAME      theorem ramsey_alg_plus_three_mathlib (rope AV5 AV5Challenge/Mathlib.lean)
ALL SAME
exit 0
```

## 3. Mathlib cache and build

`lake exe cache get` needs network access. On a fresh checkout Lake first git-clones, from
GitHub, every dependency pinned in `lake-manifest.json` (mathlib, plausible, LeanSearchClient,
importGraph, proofwidgets, aesop, Qq, batteries, Cli), and may build Mathlib's `cache`
executable; only then does it download and decompress the prebuilt Mathlib files (about 5 GB).

```sh
lake exe cache get
lake build 2>&1 | tee build.log
grep "depends on axioms" build.log
```

Expected: `Build completed successfully`, and every `depends on axioms` line ends with
`[propext, Classical.choice, Quot.sound]`. Among them:

```
'OAI.EuclideanRamsey.ramsey_alg_plus_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'AlgebraicPlusThree.ramsey_alg_plus_three_mathlib' depends on axioms: [propext, Classical.choice, Quot.sound]
'AlgebraicPlusThree.ramsey_alg_plus_three_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'AlgebraicPlusThree.oai_congruent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AlgebraicPlusThree.oai_ramsey_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'OAI.EuclideanRamsey.circle_ramsey_of_le_six' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Expected warnings** (not errors): two `declaration uses 'sorry'` warnings for
`Challenge.lean`. That file is the statement-only challenge, and its `sorry`s are the intended
holes. Linter warnings, if any, are not errors.

## 4. The judge: Comparator with three kernels, sandboxed

```sh
bash scripts/verify-comparator.sh; echo "exit $?"
```

This is PalomarTemplate's script, unmodified. It writes a temporary copy of `comparator.json`
with the toolchain's NanoDa and con-ron registered as external kernels, as the Palomar registry
does, and runs `lake comparator` in its bubblewrap sandbox. Expected, at the end:

```
Your solution is okay!
exit 0
```

before which con-ron, NanoDa and the Lean kernel each report acceptance of the exported
declarations.

## 5. Negative controls

```sh
bash tests/controls/run-controls.sh; echo "exit $?"
```

Expected: five lines, then `exit 0`:

```
REFUSED as expected: sorry-solution (exit 1): Illegal axiom detected: 'sorryAx'
REFUSED as expected: axiom-solution (exit 1): Illegal axiom detected: 'OAI.EuclideanRamsey.cheat'
REFUSED as expected: redef-ramsey (exit 1): Const does not match between challenge and target 'OAI.EuclideanRamsey.Ramsey'
REFUSED as expected: card-four (exit 1): Challenge and solution theorem statement do not match: 'OAI.EuclideanRamsey.ramsey_alg_plus_three'
REFUSED as expected: weaker-mathlib (exit 1): Challenge and solution theorem statement do not match: 'AlgebraicPlusThree.ramsey_alg_plus_three_mathlib'
```

`lake comparator` ignores `lake -f`, so the script appends the `Controls` library
(`tests/controls/Controls/`) to `lakefile.toml` while it runs and restores the file on exit. The
control files are generated from `Challenge.lean` by `python3 scripts/make_controls.py`, each with
exactly one edit (see the comment at the top of each).

## 6. Provenance of OpenAI's files

This downloads the 28 upstream files from openai/math at `fd4aeeb2`, re-applies the header-only
port with `scripts/port_to_modules.py`, and compares the result with
`OAI/Combinatorics/EuclideanRamsey/` (also `docs/PORT-LOG.md` §1). Start in the repository root.
The work happens in a fresh scratch directory, because `port_to_modules.py` rewrites the files it
is given in place.

```sh
REPO="$PWD"                      # the repository root
R=fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
SCRATCH="$(mktemp -d)"           # scratch directory for the upstream files
cd "$SCRATCH"
for f in AdicLifting ColoringCompactness Congruence CornerGroup CorrectionPaths DerivedFractions \
         DifferentialSplitting Discretization FiniteEuclidean GramCompletion Hessian LatticeMoments \
         Main Model NormalCost OrbitAveraging PathFractions PathSynchronization PathWords \
         RationalConvolution SignedRows SmoothingKernel SmoothingMatrix StencilConvolution \
         TensorDescent TensorNecessity TensorPresentation UltrafilterStrings; do
  curl -sSfLO "https://raw.githubusercontent.com/openai/math/$R/lean/OAI/Combinatorics/EuclideanRamsey/$f.lean"
done
python3 "$REPO/scripts/port_to_modules.py" --notice-oai "$SCRATCH"/*.lean
diff -r "$SCRATCH" "$REPO/OAI/Combinatorics/EuclideanRamsey" && echo "no differences"
cd "$REPO"
```

Expected: 28 lines `...: ported (1 imports)`, then `no differences`.

## Windows without a sandbox

`bwrap` does not exist on Windows. The same check runs unsandboxed, which `lake comparator` reports
as "not trustworthy" (the sandbox protects the judge from hostile code; it does not change the
verdict). On Windows the kernel executables need the `.exe` suffix: copy `comparator.json`, drop
`enable_nanoda`, add

```json
"external_kernels": {"nanoda": ["<prefix>/bin/nanoda_bin.exe"], "con-ron": ["<prefix>/bin/con-ron.exe"]}
```

with `<prefix>` from `lean --print-prefix`, and run
`lake comparator --config <that file> --inadvisably-no-sandbox`. The controls run the same way
with `bash tests/controls/run-controls.sh --no-sandbox` (Git Bash). This package has not been run
on Windows.

## Measured times

On a fresh GitHub-hosted runner (`ubuntu-latest`), from a cold start (2026-10-15):

| Step | Time |
|---|---|
| toolchain install and `lake exe cache get` | 3.3 min |
| `lake build` (OpenAI's 28 modules build one after another) | 4.8 min |
| `scripts/verify-comparator.sh` (export, three kernels; con-ron accepts about 62,100 declarations) | 6.4 min |
| `tests/controls/run-controls.sh` (five controls) | 6.7 min |

On a loaded desktop machine a similar package (mobius-ramsey) took 8.5 to 32 minutes to build
and 8 to 34 minutes for the Comparator steps; allow more if other Lean builds run at the same
time.
