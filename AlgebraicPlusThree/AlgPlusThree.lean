module

public import AlgebraicPlusThree.AlgPlusThreeCore
public import AlgebraicPlusThree.SixPoint

@[expose] public section

/-!
# Algebraic concyclic points plus at most three arbitrary points are Euclidean Ramsey

Theorem B(b) of the note `note/spherical-ramsey.tex` in spherical-ramsey v1.1.0 (doi:10.5281/zenodo.23396387). Certificate
`f = e · g₁₂₃ · (s − s')`, where `g₁₂₃` is the graph form through three points that contain the arbitrary ones, and `e` is
the separability idempotent of the number field `K = ℚ(t_i : i algebraic)`, pushed from `K ⊗ K`
into `F ⊗ F` along `K.val ⊗ K.val` (`exists_sep_idem`). Composed with OpenAI's proved
`fieldCriterion_ramsey` (openai/math @ fd4aeeb2, Apache-2.0, here ported to the module system by header-only changes).

The circle need not be assumed algebraic: for `s ≥ 7` at least three points are algebraic, so the
centre (Cramer) and the radius are algebraic, and the normalization (translate, rational rotation,
scale) keeps the algebraic points algebraic. For `s ≤ 6` the statement is `circle_ramsey_of_le_six`
(`AlgebraicPlusThree.SixPoint`).
-/

namespace OAI
noncomputable section
open scoped TensorProduct
namespace EuclideanRamsey
open AlgPlusThree SixPoint

/-- **Theorem B(b).** Finitely many distinct concyclic points, all of whose coordinates are
real algebraic except for the points of a set `T` of at most three indices, form a Euclidean
Ramsey configuration. Neither the centre nor the radius is assumed algebraic. -/
theorem ramsey_alg_plus_three {s : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin 2))
    (ha : Function.Injective a)
    (hsph : ∃ c : EuclideanSpace ℝ (Fin 2), ∃ r : ℝ, ∀ i, a i ∈ Metric.sphere c r)
    (T : Finset (Fin s)) (hT : T.card ≤ 3) (halg : ∀ i ∉ T, ∀ j, IsAlgebraic ℚ (a i j)) :
    Ramsey a := by
  rcases le_or_gt s 6 with hs6 | hs7
  · exact circle_ramsey_of_le_six a hs6 ha hsph
  obtain ⟨c, r, hc⟩ := hsph
  have hc' : ∀ i, dist (a i) c = r := fun i => Metric.mem_sphere.mp (hc i)
  rcases le_or_gt r 0 with hr | hrpos
  · exact zero_radius_ramsey a c (fun i => le_antisymm (by rw [hc' i]; exact hr) dist_nonneg)
  have hrne : r ≠ 0 := hrpos.ne'
  have hcoord := circle_coordinates a c r hc'
  have hA : ∀ i ∉ T, ∀ j, a i j ∈ Alg := fun i hi j => mem_algebraicClosure_iff.mpr (halg i hi j)
  -- three algebraic points fix the circle: the centre and the radius are algebraic
  obtain ⟨U, hUT, hU⟩ := Finset.exists_subset_card_eq (s := Tᶜ) (n := 3)
    (by rw [Finset.card_compl, Fintype.card_fin]; omega)
  obtain ⟨i1, i2, i3, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp hU
  have hAU : ∀ i ∈ ({i1, i2, i3} : Finset (Fin s)), ∀ j, a i j ∈ Alg :=
    fun i hi j => hA i (Finset.mem_compl.mp (hUT hi)) j
  have x1 := hAU i1 (by simp) 0; have y1 := hAU i1 (by simp) 1
  have x2 := hAU i2 (by simp) 0; have y2 := hAU i2 (by simp) 1
  have x3 := hAU i3 (by simp) 0; have y3 := hAU i3 (by simp) 1
  have hne : ∀ i j, i ≠ j → ¬(a i 0 = a j 0 ∧ a i 1 = a j 1) := by
    rintro i j hij ⟨h0, h1⟩
    apply hij
    apply ha
    ext k
    fin_cases k
    · exact h0
    · exact h1
  have hD := circum_D_ne (hcoord i1) (hcoord i2) (hcoord i3) (hne _ _ h12) (hne _ _ h13)
    (hne _ _ h23)
  have hc0 : c 0 ∈ Alg := by
    rw [circum_C0 (hcoord i1) (hcoord i2) (hcoord i3) hD]
    alg_mem
  have hc1 : c 1 ∈ Alg := by
    rw [circum_C1 (hcoord i1) (hcoord i2) (hcoord i3) hD]
    alg_mem
  have hrA : r ∈ Alg := alg_of_sq (by rw [← hcoord i1]; alg_mem)
  -- a rational rotation `z` that moves the pole off the configuration
  set X : Fin s → ℝ := fun i => a i 0 - c 0 with hX
  set Y : Fin s → ℝ := fun i => a i 1 - c 1 with hY
  let bad : Finset (Space 2) :=
    Finset.univ.image (fun i => WithLp.toLp 2 ![-X i / r, Y i / r])
  have hinjq : Function.Injective (fun q : ℚ => SixPoint.stereographic 0 1 (q : ℝ)) :=
    (stereographic_injective 0 1 one_pos).comp Rat.cast_injective
  obtain ⟨z, ⟨q, hq⟩, hzbad⟩ := (Set.infinite_range_of_injective hinjq).exists_notMem_finset bad
  have hz : dist z 0 = 1 := by rw [← hq]; exact stereographic_on_circle 0 1 q one_pos
  have hz2 : z 0 ^ 2 + z 1 ^ 2 = 1 := by
    have := circle_coordinates (fun _ : Fin 1 => z) 0 1 (fun _ => hz) 0
    simpa using this
  have hzA : ∀ k, z k ∈ Alg := by
    have hqA : (q : ℝ) ∈ Alg := SubfieldClass.ratCast_mem Alg q
    intro k
    rw [← hq]
    fin_cases k <;> simp [SixPoint.stereographic] <;> alg_mem
  let b : Fin s → Space 2 := fun i =>
    WithLp.toLp 2 ![(z 0 * X i - z 1 * Y i) / r, (z 1 * X i + z 0 * Y i) / r]
  have hb0 : ∀ i, b i 0 = (z 0 * X i - z 1 * Y i) / r := fun i => rfl
  have hb1 : ∀ i, b i 1 = (z 1 * X i + z 0 * Y i) / r := fun i => rfl
  have hsq : ∀ i, (z 0 * X i - z 1 * Y i) ^ 2 + (z 1 * X i + z 0 * Y i) ^ 2 = r ^ 2 := by
    intro i
    linear_combination (X i ^ 2 + Y i ^ 2) * hz2 + hcoord i
  have hbc : ∀ i, b i 0 ^ 2 + b i 1 ^ 2 = 1 := by
    intro i
    rw [hb0, hb1, div_pow, div_pow, ← add_div, hsq i, div_self (pow_ne_zero 2 hrne)]
  have hpole : ∀ i, 1 + b i 0 ≠ 0 := by
    intro i h
    rw [hb0] at h
    have e1 : z 0 * X i - z 1 * Y i = -r := by field_simp at h; linarith
    have e2 : z 1 * X i + z 0 * Y i = 0 := by
      have := hsq i
      rw [e1] at this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linear_combination this)
    apply hzbad
    simp only [bad, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨i, ?_⟩
    have hci : X i ^ 2 + Y i ^ 2 = r ^ 2 := hcoord i
    ext k
    fin_cases k
    · show -X i / r = z 0
      have h0 : r * (z 0 * r + X i) = 0 := by
        linear_combination X i * e1 + Y i * e2 - z 0 * hci
      have h0' := (mul_eq_zero.mp h0).resolve_left hrne
      rw [div_eq_iff hrne]
      linarith
    · show Y i / r = z 1
      have h1 : r * (z 1 * r - Y i) = 0 := by
        linear_combination (-Y i) * e1 + X i * e2 - z 1 * hci
      have h1' := (mul_eq_zero.mp h1).resolve_left hrne
      rw [div_eq_iff hrne]
      linarith
  have hdist : ∀ i j, dist (a i) (a j) = r * dist (b i) (b j) := by
    intro i j
    have h1 : dist (a i) (a j) ^ 2 = (r * dist (b i) (b j)) ^ 2 := by
      rw [mul_pow, dist_sq_two, dist_sq_two, hb0, hb0, hb1, hb1]
      simp only [hX, hY]
      field_simp
      linear_combination (-((a i 0 - a j 0) ^ 2 + (a i 1 - a j 1) ^ 2)) * hz2
    exact (pow_left_inj₀ dist_nonneg (mul_nonneg hrpos.le dist_nonneg) two_ne_zero).mp h1
  have hbinj : Function.Injective b := by
    intro i j h
    apply ha
    have := hdist i j
    rw [h, dist_self, mul_zero] at this
    exact dist_eq_zero.mp this
  -- three indices `w` containing `T`
  obtain ⟨T', hTT', -, hT'⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ T) hT
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  let eT : T' ≃ Fin 3 := Finset.equivFinOfCardEq hT'
  let w : Fin 3 → Fin s := fun k => (eT.symm k).val
  have hw : Function.Injective w := fun k l h => eT.symm.injective (Subtype.ext h)
  have hbA : ∀ i, i ∉ Set.range w → ∀ j, b i j ∈ Alg := by
    intro i hi j
    have hiT : i ∉ T := fun hiT => hi ⟨eT ⟨i, hTT' hiT⟩, by simp [w]⟩
    have hXi : X i ∈ Alg := sub_mem (hA i hiT 0) hc0
    have hYi : Y i ∈ Alg := sub_mem (hA i hiT 1) hc1
    have z0 := hzA 0
    have z1 := hzA 1
    fin_cases j
    · show b i 0 ∈ Alg
      rw [hb0]; alg_mem
    · show b i 1 ∈ Alg
      rw [hb1]; alg_mem
  exact ramsey_of_scaled hrpos hdist (fieldCriterion_ramsey b (by omega) (by norm_num) hbinj
    (fieldCriterion_alg3 hbc hpole hbinj w hw hbA))

end EuclideanRamsey
end
end OAI

#print axioms OAI.EuclideanRamsey.ramsey_alg_plus_three
