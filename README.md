# algebraic-plus-three-ramsey

**Algebraic points on a circle, plus at most three arbitrary points on the same circle, form a
Euclidean Ramsey set. Proved in Lean 4.**

Registered on the Palomar registry as [PALOMAR-2026-10-16-000018](https://palomar-registry.org/entry?id=PALOMAR-2026-10-16-000018&version=1) (version 1, 2026-10-16; archived commit `fe257ec`).

A finite set of points in Euclidean space is *Ramsey* if for every number of colours `r ≥ 2`
there is a dimension `D` such that every `r`-colouring of `ℝ^D` contains a monochromatic congruent
copy of the set. OpenAI's result 172 classified the finite Ramsey configurations by a tensor
condition over their coordinate field. This repository proves, on top of OpenAI's Lean proof:

> **Theorem B(b).** Let `A` be a finite set of points on a circle in `ℝ²`, all but at most three
> of which have real algebraic coordinates. Then `A` is Ramsey.

The centre and the radius of the circle are arbitrary reals (not assumed algebraic), the number
of points is unbounded, and the at most three exceptional points are arbitrary points of the
circle (transcendental coordinates allowed). In Lean the set is an injective family
`a : Fin s → EuclideanSpace ℝ (Fin 2)`, and the exceptional points are those with indices in a
`Finset` `T` with `T.card ≤ 3`.

**Where it sits.** Some finite sets on a circle are not Ramsey: Pálvölgyi's heptagon
(arXiv:2609.23327) is a cyclic non-Ramsey set of seven points. The appendix of that paper (labelled
there as unchecked ChatGPT output) has a Theorem A.10, which shows that his derivation certificates
for non-Ramsey-ness cannot exist for a set on the circle that a Möbius map sends to algebraic
points, apart from at most three, and notes that this does not decide whether such sets are
Ramsey. Theorem B(b), with Theorem C of mobius-ramsey, settles the class that A.10 leaves
undecided: such sets are Ramsey. For the sets that are themselves algebraic apart from at most three points this is the theorem proved
here; for their Möbius images it follows with the Möbius invariance of the Ramsey property
(Theorem C, proved in Lean in the companion package
[mobius-ramsey](https://github.com/wstrinz/mobius-ramsey); that step is by hand, not formalized
here). Theorem B(b) is not of the form of the one-point and pyramid extensions of Mirabi
(arXiv:2608.11736) and Moore (arXiv:2608.09649), where the added points lie off the affine hull
of a Ramsey set: here every point lies on the circle. Three cannot be replaced by four: three
rational points and four further points, algebraically independent over them, on a circle form a
non-Ramsey set (Pálvölgyi's Theorem A.3; the originating note's circle phase diagram, Proposition
PD, written up by hand and reviewed by an AI agent; not checked here).

The deep work is OpenAI's: the proof builds an explicit certificate for their field criterion and
concludes with their proved sufficiency theorem.

## What this repository is

**A port, not a new proof, and no new mathematics beyond spherical-ramsey v1.1.0.** The result,
its hand proof and its first Lean proof come from the release
[spherical-ramsey v1.1.0](https://doi.org/10.5281/zenodo.23396387) (note, Theorem B(b)). That
release's Lean proofs are in *ropes*: self-contained Lean projects, one per result, pinned to
OpenAI's toolchain (Lean v4.34.1) and checked by Comparator. The Lean proof of Theorem B(b) is
rope AV5 there (`ropes/av5`), and it is already public.

- This repository is the same Lean code, ported to the Lean module system and Lean v4.35.0-rc2.
  The statements and proofs are unchanged except for the namespace of the Mathlib-form statements
  (`docs/PORT-LOG.md`; `scripts/check_statements.py` compares the statements with the rope's).
- It exists so that Theorem B(b) can be checked and cited on its own, outside the larger release:
  one theorem in a standalone repository at a current toolchain, with a Mathlib-only statement
  file, a Comparator configuration, negative controls, CI and registry metadata.

## The statements, verbatim

Definitions (`Challenge.lean`; `Space`, `Congruent`, `Ramsey` are OpenAI's, verbatim from their
`Model.lean`, and nothing else is defined):

```lean
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def Congruent {s d D : ℕ} (a : Fin s → Space d) (b : Fin s → Space D) : Prop :=
  ∀ i j, dist (b i) (b j) = dist (a i) (a j)

def Ramsey {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
    ∀ c : Space D → Fin r, ∃ b : Fin s → Space D,
      Congruent a b ∧ ∃ k : Fin r, ∀ i, c (b i) = k
```

The two advertised theorems (`comparator.json`):

```lean
-- namespace OAI.EuclideanRamsey: Theorem B(b) in OpenAI's vocabulary
theorem ramsey_alg_plus_three {s : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin 2))
    (ha : Function.Injective a)
    (hsph : ∃ c : EuclideanSpace ℝ (Fin 2), ∃ r : ℝ, ∀ i, a i ∈ Metric.sphere c r)
    (T : Finset (Fin s)) (hT : T.card ≤ 3) (halg : ∀ i ∉ T, ∀ j, IsAlgebraic ℚ (a i j)) :
    Ramsey a

-- namespace AlgebraicPlusThree: the same with `Ramsey` unfolded and Mathlib's `Congruent`
theorem ramsey_alg_plus_three_mathlib {s : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin 2))
    (ha : Function.Injective a)
    (hsph : ∃ (c : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), ∀ i, a i ∈ Metric.sphere c ρ)
    (T : Finset (Fin s)) (hT : T.card ≤ 3) (halg : ∀ i ∉ T, ∀ j, IsAlgebraic ℚ (a i j)) :
    ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
      ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin s → EuclideanSpace ℝ (Fin D),
        Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k
```

`Metric.sphere c r` is the circle of centre `c` and radius `r` in the Euclidean metric;
`IsAlgebraic ℚ x` says the real number `x` is algebraic. The proof also contains, and uses for at
most six points, `OAI.EuclideanRamsey.circle_ramsey_of_le_six`: any at most six distinct points
on a circle are Ramsey (prior work; see Credit). A small satisfiability witness for the
hypotheses with `T` nonempty, `AlgebraicPlusThree.ramsey_alg_plus_three_nonvacuous`, is proved in
`AlgebraicPlusThree/MathlibStatement.lean` but not advertised (see Limitations).

**How it is proved.** For at most six points, the six-point theorem. For seven or more, at least
four points are algebraic, so the centre and radius are algebraic; a translation, a rational
rotation and a scaling move the circle to the unit circle with its pole off the configuration,
keeping the algebraic points algebraic. Then `e · g₁₂₃ · (s − s')` is an explicit certificate for
OpenAI's field criterion, where `g₁₂₃` is the graph form through three points containing the
exceptional ones and `e` is the separability idempotent of the number field generated by the
algebraic parameters; OpenAI's sufficiency theorem `fieldCriterion_ramsey` concludes.

## What is checked, and how

- **Kernels and statements.** The toolchain's own `lake comparator` (Lean v4.35.0-rc2) compiles
  `Challenge.lean` (Mathlib only: the three definitions above and the two statements with
  `sorry`) and `Solution.lean` (the proofs), checks that every advertised theorem has exactly the
  challenge's statement and that every definition it mentions has exactly the challenge's body,
  checks that only `propext`, `Classical.choice` and `Quot.sound` are used, and replays the whole
  proof (including the Mathlib declarations it uses) through three independent kernels: Lean's
  own, NanoDa and con-ron. It accepts: "Your solution is okay!". `scripts/verify-comparator.sh`
  is PalomarTemplate's script, unmodified; it runs this check in a bubblewrap sandbox, as the
  Palomar registry does.
- **Negative controls.** `tests/controls/` holds five controls, each refused for its expected
  reason: the challenge as its own solution (`sorryAx`); a solution that proves the statements
  from a new axiom `cheat : False`; `Ramsey` redefined with `3 ≤ r`; Theorem B(b) with four
  arbitrary points (`T.card ≤ 4`), a stronger claim, false by Pálvölgyi's Theorem A.3 (not
  checked here); and the Mathlib form with an extra hypothesis `7 ≤ s` (a weaker claim, true, but not the advertised one).
- **Axioms.** `lake build` prints `#print axioms` for the two advertised theorems, the
  satisfiability witness, the OpenAI/Mathlib bridge and the six-point theorem:
  `[propext, Classical.choice, Quot.sound]` throughout. There is no `sorry`, `admit` or `native_decide` outside the statement-only
  `Challenge.lean`.
- **Same statements as the originating release.** `scripts/check_statements.py` compares the
  three definitions and the two theorem statements in `Challenge.lean` with the Comparator
  challenges of rope AV5 in spherical-ramsey v1.1.0 (commit `09f8894`): identical, apart from the
  namespace of the Mathlib-form statements (`SphericalRamsey` there, `AlgebraicPlusThree` here). No
  hypothesis was added or changed.
- **The trusted surface** is `Challenge.lean`: OpenAI's three definitions and the two
  statements. Read it.
- **CI.** `.github/workflows/verify.yml` runs all of the above on a fresh GitHub runner on every
  push.
- **Fidelity.** `docs/FIDELITY.md` goes through the statements item by item: Ramsey
  quantifiers, pairs, metric, distinctness, set versus tuple, embeddings, junk values, vacuity,
  edge cases and the frame dependence of "algebraic coordinates".
- **Prior-work search.** `docs/PRIOR-WORK-SEARCH.md` logs the searches for earlier statements of
  Theorem B(b), with their dates.

### Verification level, and what came before

- Here: Lean v4.35.0-rc2 / Mathlib `065356127b`, Comparator with three kernels, five negative
  controls, standard axioms, on a fresh runner.
- In the originating release (rope AV5 of spherical-ramsey, Lean v4.34.1 / Mathlib `d13f23b7`,
  the same statements and proofs before the module-system port): stock Comparator on a fresh
  runner (all ten checks as expected), a fidelity review by an AI agent that did not build the
  rope (faithful; documentation fixes only), and a fresh reproduction by another AI agent from the
  README alone (reproduced).
- This package's statements and documentation were reviewed by a further AI agent that did not
  build them (statements identical to the rope's; documentation fixes applied).
- **No human expert has reviewed this work.** See `DISCLOSURE.md`.

### Independence

**This work trusts OpenAI's Lean proof of result 172.** OpenAI's 28 Lean files (the import closure
of their `Main.lean`) are included and replayed by the kernels here, but the classification is
theirs, not re-proved; the proof here uses its sufficiency direction `fieldCriterion_ramsey` and
its definitions. The files were ported to the Lean module system by header-only changes (a
`module` line, `public import`, `@[expose] public section`, and an Apache-2.0 modification
notice); no statement or proof line changed (`docs/PORT-LOG.md`). The same port is in
mobius-ramsey.

## Credit

- **OpenAI**, *A classification of finite Euclidean Ramsey configurations* (openai/math, commit
  `fd4aeeb2`, result 172): the foundation, the definitions, the field criterion, the sufficiency
  theorem, and the Lean proof this one builds on.
- **The six-point case is prior work.** JD-Jones-ASES/six-concyclic-lean (root commit `0703d7d`)
  proved in Lean, at the level of OpenAI's field criterion, that any six concyclic points satisfy
  the criterion, by the two-triple certificate `g₁₂₃ · g₄₅₆` that `AlgebraicPlusThree/SixPoint.lean`
  also uses; its Ramsey conclusion is conditional on a hypothesis `hsuff` standing for OpenAI's
  sufficiency direction. The Lean proof here was written without consulting theirs and
  discharges that step with OpenAI's proved sufficiency theorem. With Pálvölgyi's heptagon, six is
  the largest size for which every cyclic set is Ramsey.
- **The case `T = ∅`** (algebraic coordinates) is the plane case of a prior theorem: proved at the
  criterion level in Lean by JD-Jones-ASES, in TeX by Rogerhu12/openai-math-extensions (commit
  `f8a2bb2`, with the same separability-idempotent argument), and end to end in Lean for
  configurations with full affine span by atimics/math2 (commit `8ab51fa`).
- **Pálvölgyi**, *A cyclic non-Ramsey heptagon* (arXiv:2609.23327): the heptagon, and Theorem A.10
  of its appendix (see above). By its arXiv comments and its own disclosure, the manuscript was
  written by ChatGPT; its appendix holds further ChatGPT results that he has not verified.
- **No prior statement of Theorem B(b) was found** in the prior-work searches made for
  spherical-ramsey (four sweeps, 2026-10-12/13, over arXiv, GitHub, MathOverflow and bibliographic
  databases) or in a repeat search for this package on 2026-10-16 (arXiv, GitHub, the Palomar
  registry, MathOverflow); `docs/PRIOR-WORK-SEARCH.md` has the log. These were AI searches, not a
  literature review by an expert.
- **Origin.** spherical-ramsey v1.1.0, W. Strinz, Zenodo, doi:10.5281/zenodo.23396387: the note
  (Theorem B(b)), the certificate script `certificates/cert_mobius.py` (rational case) and rope
  AV5, of which this repository is the module-system port.

## Limitations

- **The plane.** The Lean statement is for points of `EuclideanSpace ℝ (Fin 2)`. Concyclic points
  in a plane of `ℝ^d` are congruent to planar ones, and `Ramsey` is invariant under congruence, so
  the theorem covers them up to congruence; that step is by hand.
- **"Algebraic coordinates" depends on the frame.** The theorem therefore covers every set
  congruent to one meeting its hypotheses (by hand, from the congruence invariance of `Ramsey`).
- **Möbius images.** The extension to sets that a Möbius map sends to algebraic points apart from
  at most three (Pálvölgyi's A.10 class) uses Theorem C of mobius-ramsey and is by hand here.
- **Non-vacuity.** `ramsey_alg_plus_three_nonvacuous` (proved, not advertised) exhibits a small
  witness (two points, `T` nonempty). A Lean witness with seven or more points and
  transcendental points in `T` is not given; such sets exist (for example six rational points of the unit circle together with the
  point of stereographic parameter a Liouville number).
- **Review.** No human expert has reviewed this work. The proofs and checks were produced by AI
  agents; see `DISCLOSURE.md`.

## Reproduce

Full instructions, with the exact commands and expected output, are in `REPRODUCE.md`. In short,
on Linux with [elan](https://github.com/leanprover/elan) on `PATH`
(`export PATH="$HOME/.elan/bin:$PATH"`) and `bwrap` installed:

```sh
python3 scripts/check-lean-sources.py     # Palomar's source rules: exit 0
python3 scripts/check_statements.py       # statements as in the originating release: ALL SAME
lake exe cache get                        # Mathlib's prebuilt files (about 5 GB)
lake build                                # prints the axioms lines
bash scripts/verify-comparator.sh         # "Your solution is okay!"
bash tests/controls/run-controls.sh       # five "REFUSED as expected" lines
```

**Time and memory.** On a fresh GitHub-hosted runner the whole sequence took about 22 minutes
(build 5 minutes, Comparator 6, controls 7; `REPRODUCE.md` has the table). Plan on about 16 GB
of RAM. The build prints two
expected warnings, `declaration uses 'sorry'`, for the statement-only `Challenge.lean`.

## Licence and citation

This is a mixed tree. MIT (`LICENSE`) for this project's files. Apache-2.0
(`LICENSES/Apache-2.0.txt`) for OpenAI's files under `OAI/`, modified in their headers only (listed
in `NOTICE` and `docs/PORT-LOG.md`); for `AlgebraicPlusThree/SixPointCircle.lean`, which adapts
lemmas of OpenAI's circle files; and for the two unmodified PalomarTemplate scripts under
`scripts/`. `NOTICE` says which file is under which licence. Cite with `CITATION.cff`.

## Authorship

Will Strinz is the sole human author. AI agents (Claude Opus 5.5 and Claude Sonnet 5.5,
Anthropic) produced the proofs, the port, the checks and the documentation under his direction.
`DISCLOSURE.md` says who did what and which reviews were AI reviews.
