# Fidelity of the advertised statements

This file checks the two advertised statements in `Challenge.lean` against the standard list of
formalization pitfalls (pairs, metric, distinctness, embeddings, junk values, vacuity), plus Ramsey
quantifiers, set versus tuple, edge cases, frame dependence and sphericity. It is carried over
from the fidelity note of rope AV5 in spherical-ramsey v1.1.0 (the same statements, before the
module-system port), which an AI agent that did not build the rope reviewed (faithful; fixes to
the note only, applied). Only the file names, control names and namespace were changed here, and
the Möbius-image scope remark was added. Each item says how it was checked:
- **PROVED**: a Lean theorem in this package, accepted by Comparator with the standard axioms only;
- **CHECKED**: a script or a negative control in CI;
- **INFERRED**: reading the source.

The statements: `OAI.EuclideanRamsey.ramsey_alg_plus_three` (Theorem B(b) in OpenAI's vocabulary),
`AlgebraicPlusThree.ramsey_alg_plus_three_mathlib` (the same in Mathlib vocabulary). A
satisfiability witness, `AlgebraicPlusThree.ramsey_alg_plus_three_nonvacuous`, is proved in
`AlgebraicPlusThree/MathlibStatement.lean` but not advertised (see Vacuity below).

## Sources and vocabulary

- **No formal-conjectures statement exists** for Euclidean Ramsey sets (a code search of its
  default branch), so the vocabulary is OpenAI's public Comparator challenge for result 172
  (openai/math `fd4aeeb2`).
- `Challenge.lean` restates OpenAI's preamble and its definitions of `Space`, `Congruent` and
  `Ramsey`, character for character (**CHECKED**: `scripts/check_statements.py` against the
  originating release, whose own preflight compared them byte for byte with OpenAI's challenge
  files and `Model.lean`; Comparator's definition match, and the control `redef-ramsey` is
  refused).
- **Definition count.** OpenAI's vocabulary is 7 non-blank lines (3 definitions). This package
  adds **0 statement definitions**: the hypotheses use only Mathlib (`EuclideanSpace ℝ (Fin 2)`,
  `Metric.sphere`, `Finset.card`, `IsAlgebraic`). Proof-internal definitions (`hd`, `Alg`, `tp`,
  `j₁`, `j₂`, `jm`; and in the six-point case `tpar`, `ι₁`, `ι₂`, `μ`, `stereographic`, the
  certificate algebra) are in no statement.
- The Mathlib-form statement has 0 definitions. Its hypotheses are those of the OpenAI-vocabulary
  statement, verbatim except that the radius is named `ρ`; its conclusion is OpenAI's `Ramsey a`
  unfolded through `oai_ramsey_iff`, with Mathlib's `Congruent`.
- **OpenAI's `Congruent` and Mathlib's `Congruent` differ** (`dist` versus `edist`, and argument
  order). **PROVED** equivalent: `AlgebraicPlusThree.oai_congruent_iff` and `oai_ramsey_iff`
  (`AlgebraicPlusThree/MathlibBridge.lean`), and the Mathlib-form statement is derived from the
  OpenAI-vocabulary one through them.

## Hypotheses

| Hypothesis | Role | Check |
|---|---|---|
| `ha : Function.Injective a` | distinct points | INFERRED |
| `hsph : ∃ c r, ∀ i, a i ∈ Metric.sphere c r` | concyclic; centre and radius arbitrary reals (not assumed algebraic) | INFERRED. For `s ≥ 7` the proof derives that `c` and `r` are algebraic from three algebraic points (`circum_C0`, `circum_C1`, `alg_of_sq`) |
| `T : Finset (Fin s)`, `hT : T.card ≤ 3` | the exceptional indices | INFERRED; the control `card-four` (`T.card ≤ 4`) is refused (CHECKED) |
| `halg : ∀ i ∉ T, ∀ j, IsAlgebraic ℚ (a i j)` | every coordinate of every point outside `T` is algebraic over `ℚ` | INFERRED; no condition at all on the points of `T` |

No other hypothesis is used, and OpenAI's `Ramsey` is not modified. The control `weaker-mathlib`
(an extra hypothesis `7 ≤ s`) is refused (CHECKED).

## Pitfalls

| Pitfall | How it was checked |
|---|---|
| Ramsey quantifiers | `Ramsey a`: ∀ `r ≥ 2`, ∃ `D ≥ 1`, ∀ colourings `c : Space D → Fin r`, ∃ `b` with `Congruent a b` and `c ∘ b` constant. `D` depends on `r` only, and one `D` works for all colourings; colourings are arbitrary functions; congruence is at scale 1. Omitting `r ∈ {0, 1}` is harmless, and so is requiring `D ≥ 1`. "∃ D" is equivalent to "∀ D ≥ D₀", since a copy in `Space D` embeds in `Space D'`, `D' ≥ D`. Same quantifier order as Erdős, Graham, Montgomery, Rothschild, Spencer and Straus (1973). INFERRED; the definition is OpenAI's verbatim (CHECKED). |
| Ordered versus unordered pairs | `Congruent` quantifies over all ordered pairs; it is symmetric, and the diagonal gives `0 = 0`. INFERRED; PROVED for the OpenAI/Mathlib match. |
| Set versus tuple | `a` is an injective enumeration of an `s`-point set. `Ramsey` is invariant under permuting indices, and so are the hypotheses (permute `T` with them), so the theorem is about the set `range a` with at most three exceptional points. INFERRED. |
| Metric | `EuclideanSpace ℝ (Fin 2)`, the ℓ² metric; the circle is `Metric.sphere c r` in that metric. INFERRED. |
| Injectivity and distinctness | `ha`. INFERRED. |
| Faithful versus non-faithful embeddings | `Congruent` preserves every pairwise distance; a finite congruence extends to an isometric embedding of the affine hull of `range a` into `Space D`. No embedding is chosen in the statement. INFERRED. |
| `sSup` junk values | None in any statement, and no division. INFERRED. |
| ℕ subtraction and division | None: the ℕ facts are `T.card ≤ 3`, `2 ≤ r`, `1 ≤ D`. INFERRED. |
| Edge cases | `s ≤ 1`: Ramsey trivially (one point, or none). `s ≤ 6`: covered by the six-point theorem `circle_ramsey_of_le_six` whatever `T` is; every case with at most two algebraic points has `s ≤ 5`. `r < 0` in `hsph`: no point, so `s = 0`. `r = 0`: all points equal the centre, so `s ≤ 1` (`zero_radius_ramsey`). `T` may contain algebraic points; `T = ∅` is the plane case of the algebraic-coordinates theorem (prior work). INFERRED for the case analysis; each case is PROVED inside the theorem. |
| Vacuous or contradictory hypotheses | **PROVED** satisfiable with `T` nonempty (proved, not advertised): `ramsey_alg_plus_three_nonvacuous` gives `±e₀` on the unit circle with `T = {0, 1}`. That witness is small; the theorem's content beyond the algebraic and six-point cases is `s ≥ 7` with non-algebraic points in `T`, which is not exhibited in Lean (a witness is possible in principle, for example `((1 − L²)/(1 + L²), 2L/(1 + L²))` with `L` a Liouville number, transcendental by Mathlib's `Liouville.transcendental`, plus six rational points of the unit circle; not done). |
| Vacuous conclusion | `Ramsey` is not trivially true: OpenAI proves (`ramsey_cospherical`, in their `Spherical.lean`, not included here) that every injective Ramsey configuration is cospherical, and the originating release checked that theorem with stock Comparator against OpenAI's own challenge. It is also not true of all concyclic sets: Pálvölgyi's heptagon and OpenAI's nine-point example are non-Ramsey concyclic sets, with at least four non-algebraic points. INFERRED. |

## Scope remarks (not pitfalls, but easy to misread)

- **Frame dependence.** "Algebraic coordinates" depends on the frame. `Ramsey` is invariant under
  congruence, so the theorem covers every set congruent to one satisfying the hypotheses.
  INFERRED, not proved here.
- **Sphericity.** The points lie on a circle in the plane. A non-cospherical set is never Ramsey
  (OpenAI's `ramsey_cospherical`), so concyclicity is necessary in the plane, not a convenience.
- **Sharpness of "three".** Three rational points and four further points, algebraically
  independent over them, on a circle form a non-Ramsey set (Pálvölgyi's Theorem A.3; the
  originating note's Proposition PD, by hand, AI-reviewed). Not checked here.
- **Dimension.** The theorem is for the plane (`Fin 2`). Concyclic points in a plane of `ℝ^d` are
  congruent to planar ones, so it covers them up to congruence (INFERRED).
- **Möbius images.** Pálvölgyi's Theorem A.10 concerns sets that a Möbius map of the circle sends
  to algebraic points apart from at most three. Those sets are Ramsey by this theorem together with
  the Möbius invariance of the Ramsey property (Theorem C of mobius-ramsey) and a similarity to the
  unit circle; that combination is by hand, not formalized here.

## Review

The rope version of this note was self-assessed by the agent that assembled the rope, then
reviewed by an AI agent that did not build it (Claude Opus 5.5, read-only): faithful, fixes to the
note only (applied). A fresh AI agent (Claude Sonnet 5.5) reproduced the rope from its README
alone. This package's statements and documentation, including this note's port (file names,
control names and namespace, the Möbius-image remark), were reviewed by a further Claude Opus 5.5
agent that did not build them: statements identical to the rope's; documentation fixes applied.
There has been no human review.
