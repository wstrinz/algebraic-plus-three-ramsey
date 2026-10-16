#!/usr/bin/env python3
"""Compare the statements in Challenge.lean with the originating release's Comparator challenges.

applies_to: this repository's Challenge.lean, against rope AV5 of spherical-ramsey v1.1.0
(github.com/wstrinz/spherical-ramsey, commit 09f88943111035c1764169cfd96bde7340aff687,
ropes/av5/AV5Challenge/Main.lean and Mathlib.lean), where the same theorems were first checked by
Comparator (Lean v4.34.1, before the module-system port). Compared: the text of OpenAI's three
definitions (`Space`, `Congruent`, `Ramsey`), and each theorem's statement from `theorem` to
`:= by`, with runs of whitespace collapsed to one space. The only permitted difference is the
namespace of the Mathlib-vocabulary statements (`SphericalRamsey` there, `AlgebraicPlusThree` here),
which is not part of the compared text.

Usage, from the repository root (network access to raw.githubusercontent.com):
    python3 scripts/check_statements.py
or, with local copies of the two rope files:
    python3 scripts/check_statements.py <Main.lean> <Mathlib.lean>
Exit 0 iff everything matches.
"""
import pathlib
import re
import sys
import urllib.request

COMMIT = "09f88943111035c1764169cfd96bde7340aff687"
BASE = f"https://raw.githubusercontent.com/wstrinz/spherical-ramsey/{COMMIT}/ropes/av5/AV5Challenge/"
ROOT = pathlib.Path(__file__).resolve().parent.parent

THEOREMS = {
    "ramsey_alg_plus_three": "Main",
    "ramsey_alg_plus_three_mathlib": "Mathlib",
}
DEFINITIONS = ["abbrev Space", "def Congruent", "def Ramsey"]


def read(source: str) -> str:
    if source.startswith("https://"):
        with urllib.request.urlopen(source, timeout=60) as response:
            return response.read().decode("utf-8")
    return pathlib.Path(source).read_text(encoding="utf-8")


def squash(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def theorem(text: str, name: str) -> str:
    match = re.search(r"^theorem " + re.escape(name) + r"\b(.*?):= by", text, re.S | re.M)
    if not match:
        raise SystemExit(f"theorem {name} not found")
    return squash("theorem " + name + match.group(1))


def definition(text: str, head: str) -> str:
    match = re.search(r"^" + re.escape(head) + r"\b.*?(?=\n\n|\nend |\ntheorem |\ndef |\nabbrev )", text,
                      re.S | re.M)
    if not match:
        raise SystemExit(f"{head} not found")
    return squash(match.group(0))


def main() -> int:
    sys.stdout.reconfigure(encoding="utf-8")
    args = sys.argv[1:]
    sources = {"Main": args[0], "Mathlib": args[1]} if len(args) == 2 else \
        {"Main": BASE + "Main.lean", "Mathlib": BASE + "Mathlib.lean"}
    rope = {key: read(value) for key, value in sources.items()}
    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    failed = 0
    for head in DEFINITIONS:
        ok = definition(challenge, head) == definition(rope["Main"], head)
        print(("SAME      " if ok else "DIFFERENT ") + head)
        failed |= not ok
    for name, where in THEOREMS.items():
        ours, theirs = theorem(challenge, name), theorem(rope[where], name)
        ok = ours == theirs
        print(("SAME      " if ok else "DIFFERENT ") + f"theorem {name} (rope AV5 AV5Challenge/{where}.lean)")
        if not ok:
            print("  here: " + ours + "\n  rope: " + theirs)
        failed |= not ok
    print("ALL SAME" if not failed else "MISMATCH")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
