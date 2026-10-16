#!/usr/bin/env python3
"""Regenerate tests/controls/Controls/*.lean from Challenge.lean, each with exactly one edit.

applies_to: this repository's Challenge.lean (the advertised statements of Theorem B(b)). Each
edit must match exactly once, or the script stops. Run from the repository root:
    python3 scripts/make_controls.py
"""
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
HEADER_END = "@[expose] public section\n"

STATEMENT_MAIN = "    (T : Finset (Fin s)) (hT : T.card ≤ 3) (halg : ∀ i ∉ T, ∀ j, IsAlgebraic ℚ (a i j)) :\n    Ramsey a := by\n  sorry"
STATEMENT_MATHLIB = "    (T : Finset (Fin s)) (hT : T.card ≤ 3) (halg : ∀ i ∉ T, ∀ j, IsAlgebraic ℚ (a i j)) :\n    ∀ r : ℕ, 2 ≤ r"

CONTROLS = {
    "RedefRamsey": (
        "OpenAI's Ramsey redefined with 3 ≤ r in place of 2 ≤ r",
        [("  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧\n    ∀ c : Space D",
          "  ∀ r : ℕ, 3 ≤ r → ∃ D : ℕ, 1 ≤ D ∧\n    ∀ c : Space D")],
    ),
    "CardFour": (
        "Theorem B(b) with four arbitrary points (hT : T.card ≤ 4): a stronger claim, false by Pálvölgyi's Theorem A.3 (not checked here)",
        [(STATEMENT_MAIN, STATEMENT_MAIN.replace("T.card ≤ 3", "T.card ≤ 4"))],
    ),
    "WeakerMathlib": (
        "the Mathlib-vocabulary statement with an extra hypothesis (hs : 7 ≤ s): a weaker claim, true but not the advertised one",
        [(STATEMENT_MATHLIB, STATEMENT_MATHLIB.replace(
            "(halg : ∀ i ∉ T, ∀ j, IsAlgebraic ℚ (a i j)) :",
            "(halg : ∀ i ∉ T, ∀ j, IsAlgebraic ℚ (a i j)) (hs : 7 ≤ s) :"))],
    ),
    "AxiomSolution": (
        "a solution that proves the two statements from a new axiom `cheat : False`",
        [("      Congruent a b ∧ ∃ k : Fin r, ∀ i, c (b i) = k\n\n",
          "      Congruent a b ∧ ∃ k : Fin r, ∀ i, c (b i) = k\n\naxiom cheat : False\n\n"),
         ("    Ramsey a := by\n  sorry", "    Ramsey a := by\n  exact cheat.elim"),
         ("        Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k := by\n  sorry",
          "        Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k := by\n  exact OAI.EuclideanRamsey.cheat.elim")],
    ),
}

out_dir = ROOT / "tests" / "controls" / "Controls"
out_dir.mkdir(parents=True, exist_ok=True)
for name, (what, edits) in CONTROLS.items():
    text = challenge
    for old, new in edits:
        count = text.count(old)
        if count != 1:
            raise SystemExit(f"{name}: edit matches {count} times: {old[:50]!r}")
        text = text.replace(old, new)
    banner = (f"\n/-! NEGATIVE CONTROL ({what}). Comparator must refuse this "
              + ("solution" if name == "AxiomSolution" else "challenge") + ". -/\n")
    i = text.index(HEADER_END) + len(HEADER_END)
    text = text[:i] + banner + text[i:]
    (out_dir / f"{name}.lean").write_bytes(text.encode("utf-8"))
    print(f"wrote tests/controls/Controls/{name}.lean")
