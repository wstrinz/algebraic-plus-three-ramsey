module

public import OAI.Combinatorics.EuclideanRamsey.Model

@[expose] public section

/-!
# OpenAI's `Congruent` and `Ramsey` in Mathlib vocabulary

The bridge of spherical-ramsey v1.1.0 (doi:10.5281/zenodo.23396387) (rope AV1, theorems `oai_congruent_iff` and
`oai_ramsey_iff`), with the same statements and proofs, here importing only OpenAI's `Model.lean`.
OpenAI's `Congruent` compares `dist (b i) (b j) = dist (a i) (a j)`; Mathlib's `Congruent` compares
`edist (a i) (a j) = edist (b i) (b j)`. They are equivalent, and so OpenAI's `Ramsey a` is the
unfolded Mathlib-vocabulary property.
-/

namespace AlgebraicPlusThree

/-- OpenAI's `Congruent` (`dist (b i) (b j) = dist (a i) (a j)`) is Mathlib's `Congruent`
(`edist (a i) (a j) = edist (b i) (b j)`). -/
theorem oai_congruent_iff {s d D : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin d))
    (b : Fin s → EuclideanSpace ℝ (Fin D)) :
    OAI.EuclideanRamsey.Congruent a b ↔ Congruent a b := by
  rw [congruent_iff_dist_eq]
  exact forall₂_congr fun _ _ => eq_comm

/-- OpenAI's `Ramsey`, unfolded into Mathlib vocabulary. -/
theorem oai_ramsey_iff {s d : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin d)) :
    OAI.EuclideanRamsey.Ramsey a ↔
      ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
        ∀ χ : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : Fin s → EuclideanSpace ℝ (Fin D),
          Congruent a b ∧ ∃ k : Fin r, ∀ i, χ (b i) = k := by
  unfold OAI.EuclideanRamsey.Ramsey
  simp only [oai_congruent_iff]

end AlgebraicPlusThree
