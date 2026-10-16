module

public import AlgebraicPlusThree.AlgPlusThree
public import AlgebraicPlusThree.MathlibBridge

@[expose] public section

/-!
# Theorem B(b) in Mathlib vocabulary

`OAI.EuclideanRamsey.ramsey_alg_plus_three` restated without OpenAI's definitions: its hypotheses
are already in Mathlib vocabulary (`EuclideanSpace ℝ (Fin 2)`, `Metric.sphere`, `Finset`,
`IsAlgebraic`), and OpenAI's `Ramsey` is unfolded by `oai_ramsey_iff` into Mathlib's `Congruent`.
`ramsey_alg_plus_three_nonvacuous` exhibits a configuration meeting every hypothesis, with the
exceptional set `T` nonempty.
-/

namespace AlgebraicPlusThree

/-- **Theorem B(b), Mathlib vocabulary.** Finitely many distinct concyclic points of the plane, all of whose
coordinates are algebraic over `ℚ` except at the indices of a set `T` of at most three points, form
a Euclidean Ramsey configuration: for every number `r ≥ 2` of colours there is a dimension `D ≥ 1`
such that every `r`-colouring of `EuclideanSpace ℝ (Fin D)` has a monochromatic congruent copy.
Neither the centre nor the radius is assumed algebraic. -/
theorem ramsey_alg_plus_three_mathlib {s : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin 2))
    (ha : Function.Injective a)
    (hsph : ∃ (c : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), ∀ i, a i ∈ Metric.sphere c ρ)
    (T : Finset (Fin s)) (hT : T.card ≤ 3) (halg : ∀ i ∉ T, ∀ j, IsAlgebraic ℚ (a i j)) :
    ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
      ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin s → EuclideanSpace ℝ (Fin D),
        Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k :=
  (oai_ramsey_iff a).1 (OAI.EuclideanRamsey.ramsey_alg_plus_three a ha hsph T hT halg)

/-- The hypotheses of `ramsey_alg_plus_three_mathlib` are satisfiable with `T` nonempty: the two
points `±e₀` of the plane are distinct and lie on the unit circle about `0`, and `T = {0, 1}` (so
`halg` is vacuous). -/
theorem ramsey_alg_plus_three_nonvacuous :
    ∃ (a : Fin 2 → EuclideanSpace ℝ (Fin 2)) (T : Finset (Fin 2)), T.Nonempty ∧
      Function.Injective a ∧ (∃ (c : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), ∀ i, a i ∈ Metric.sphere c ρ) ∧
      T.card ≤ 3 ∧ ∀ i ∉ T, ∀ j, IsAlgebraic ℚ (a i j) := by
  refine ⟨![EuclideanSpace.single 0 1, EuclideanSpace.single 0 (-1)], Finset.univ,
    Finset.univ_nonempty, ?_, ⟨0, 1, ?_⟩, by simp, fun i hi => absurd (Finset.mem_univ i) hi⟩
  · intro i j hij
    have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hij
    fin_cases i <;> fin_cases j <;> first | rfl | norm_num at h0
  · intro i
    fin_cases i <;> simp

end AlgebraicPlusThree
