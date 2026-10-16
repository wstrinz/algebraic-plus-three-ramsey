# Authorship, AI use and review

## Human author

**Will Strinz** is the sole human author and the person responsible for this repository. He
directed the work, made the decisions recorded here (scope, licence, what to release), and is
accountable for the release. He is not an expert in Euclidean Ramsey theory. He reviewed the
originating note (spherical-ramsey, which contains the hand proof of Theorem B(b)) before its
release, not line by line: an owner's review, not expert review.

## AI contributions, by name

| Contributor | What it did |
|---|---|
| Claude Opus 5.5 (Anthropic), in claude.ai | The exploratory conversation in which most of spherical-ramsey's claims, and the first versions of several of its certificate scripts, first appeared; the task description that started the project |
| **Claude Opus 5.5** (Anthropic), in Claude Code | Coordination of the work; the Lean proofs (`AlgebraicPlusThree/`, written for spherical-ramsey as rope AV5); the exact certificate script for the rational case (in spherical-ramsey); the port of this development to the Lean module system and this package (statements, controls, CI, documentation); the reviews listed below as AI reviews |
| **Claude Sonnet 5.5** (Anthropic), in Claude Code | The prior-work and novelty searches made for spherical-ramsey; a fresh reproduction of rope AV5 (with the rest of spherical-ramsey) from its README and REPRODUCE alone |

The agents worked in Claude Code. Every machine check reported in this repository was run by
these agents, on GitHub-hosted runners; the author did not re-run them.

## Foundation

**OpenAI's result 172**, *A classification of finite Euclidean Ramsey configurations*, and its
complete Lean proof (github.com/openai/math, commit `fd4aeeb2`), is the foundation of this work.
The proof here builds an explicit certificate for OpenAI's field criterion and concludes with
OpenAI's proved sufficiency theorem, whose 28 files are included (Apache-2.0; see `NOTICE`). The
six-point case is prior work of JD-Jones-ASES (six-concyclic-lean, root commit `0703d7d`); see
`README.md`, Credit.

## Review: who checked what

| Check | By | Kind |
|---|---|---|
| Lean proofs at Lean v4.35.0-rc2: kernel checking, axioms, statement and definition match against `Challenge.lean`, refusal of five negative controls | Lean, NanoDa and con-ron kernels through `lake comparator`, on a fresh GitHub runner (`.github/workflows/verify.yml`) | machine |
| The same statements and proofs at Lean v4.34.1, before the module-system port (rope AV5 of spherical-ramsey) | stock Comparator (Lean kernel, Landlock sandbox) on a fresh GitHub runner: all ten checks as expected | machine |
| Statements in `Challenge.lean` against the originating release's Comparator challenges | `scripts/check_statements.py`, in CI | machine (text comparison) |
| Fidelity of rope AV5's statements (`docs/FIDELITY.md` here, carried over), by an agent that did not build the rope | Claude Opus 5.5, read-only | AI review: faithful, fixes to the fidelity note only, all applied |
| Fresh reproduction of rope AV5 from its README alone, by an agent that did not build it | Claude Sonnet 5.5 | AI reproduction: reproduced (exit 0, all ten checks as expected); its friction notes were fixed in the documentation |
| The module-system port and this package (statements, controls, documentation) | the Claude Opus 5.5 agent that assembled it; then a further Claude Opus 5.5 agent that did not build it, read-only | AI review: statements identical to the rope's; documentation fixes applied |
| The originating note, including the hand proof of Theorem B(b) | Claude agents; the author reviewed it before release, not line by line | AI review; owner's review, not expert review |
| Novelty of Theorem B(b) | Claude Sonnet 5.5 (arXiv, GitHub, MathOverflow, bibliographic databases), repeated for this package on 2026-10-16 (`docs/PRIOR-WORK-SEARCH.md`) | AI search; not a literature review by an expert |

**Every review listed here is an AI review, except the author's own review of the note. No human
expert has reviewed this work.**
