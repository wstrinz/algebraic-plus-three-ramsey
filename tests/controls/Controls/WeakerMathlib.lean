module

public import Mathlib

@[expose] public section

/-! NEGATIVE CONTROL (the Mathlib-vocabulary statement with an extra hypothesis (hs : 7 ≤ s): a weaker claim, true but not the advertised one). Comparator must refuse this challenge. -/

/-!
# Advertised statements: algebraic concyclic points plus at most three arbitrary points are Ramsey

Mathlib-only. The trusted surface is the three definitions below and the two theorem
statements.

* `Space`, `Congruent`, `Ramsey` are restated verbatim from OpenAI's
  `OAI/Combinatorics/EuclideanRamsey/Model.lean` (openai/math fd4aeeb2, Apache-2.0), which is also
  the text of OpenAI's own Comparator challenge for result 172. A finite configuration
  `a : Fin s → ℝ^d` is *Ramsey* if for every number of colours `r ≥ 2` there is a dimension `D`
  such that every `r`-colouring of `ℝ^D` contains a monochromatic congruent copy of `a`.
* The hypotheses of the theorems use Mathlib only: `EuclideanSpace ℝ (Fin 2)` (the Euclidean
  plane), `Metric.sphere c r` (the circle of centre `c` and radius `r`), `Finset.card` and
  `IsAlgebraic ℚ`. No further definition is introduced.

**Theorem B(b).** Finitely many distinct points on some circle in the plane (centre and radius
arbitrary reals), all of whose coordinates are algebraic over `ℚ` except at the indices in a set
`T` of at most three, form a Ramsey configuration. It is stated twice: in OpenAI's vocabulary
(`OAI.EuclideanRamsey.ramsey_alg_plus_three`) and with OpenAI's `Ramsey` unfolded into Mathlib's
`Congruent` (`AlgebraicPlusThree.ramsey_alg_plus_three_mathlib`).
-/

namespace OAI

noncomputable section
open scoped TensorProduct
namespace EuclideanRamsey

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def Congruent {s d D : ℕ} (a : Fin s → Space d) (b : Fin s → Space D) : Prop :=
  ∀ i j, dist (b i) (b j) = dist (a i) (a j)

def Ramsey {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
    ∀ c : Space D → Fin r, ∃ b : Fin s → Space D,
      Congruent a b ∧ ∃ k : Fin r, ∀ i, c (b i) = k

/-- **Theorem B(b).** Finitely many distinct concyclic points, all of whose coordinates are
real algebraic except for the points of a set `T` of at most three indices, form a Euclidean
Ramsey configuration. Neither the centre nor the radius is assumed algebraic. -/
theorem ramsey_alg_plus_three {s : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin 2))
    (ha : Function.Injective a)
    (hsph : ∃ c : EuclideanSpace ℝ (Fin 2), ∃ r : ℝ, ∀ i, a i ∈ Metric.sphere c r)
    (T : Finset (Fin s)) (hT : T.card ≤ 3) (halg : ∀ i ∉ T, ∀ j, IsAlgebraic ℚ (a i j)) :
    Ramsey a := by
  sorry

end EuclideanRamsey

end

end OAI

namespace AlgebraicPlusThree

/-- **Theorem B(b), Mathlib vocabulary.** The same, with OpenAI's `Ramsey a` unfolded and
Mathlib's `Congruent` (`edist`-based) in place of OpenAI's (`dist`-based). -/
theorem ramsey_alg_plus_three_mathlib {s : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin 2))
    (ha : Function.Injective a)
    (hsph : ∃ (c : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), ∀ i, a i ∈ Metric.sphere c ρ)
    (T : Finset (Fin s)) (hT : T.card ≤ 3) (halg : ∀ i ∉ T, ∀ j, IsAlgebraic ℚ (a i j)) (hs : 7 ≤ s) :
    ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
      ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin s → EuclideanSpace ℝ (Fin D),
        Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k := by
  sorry

end AlgebraicPlusThree
