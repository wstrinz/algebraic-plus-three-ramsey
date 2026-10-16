module

public import AlgebraicPlusThree.SixPointAlgebra
public import AlgebraicPlusThree.SixPointCircle
public import OAI.Combinatorics.EuclideanRamsey.Main

@[expose] public section

/-!
# Any at most six distinct points on a circle are Euclidean Ramsey

This is prior work: the two-triple certificate `g₁₂₃ · g₄₅₆` and the six-point criterion are
JD-Jones-ASES's (github.com/JD-Jones-ASES/six-concyclic-lean, root commit 0703d7d), whose Ramsey
conclusion is conditional on a hypothesis `hsuff` standing for OpenAI's sufficiency direction.
The Lean proof here was written without consulting theirs, and discharges that step with OpenAI's
proved `fieldCriterion_ramsey`. Graph-form certificate (the note `note/spherical-ramsey.tex` in
spherical-ramsey v1.1.0 (doi:10.5281/zenodo.23396387), graph forms and Theorem B(a);
`certificates/cert_mobius.py` there) composed with
OpenAI's proved sufficiency direction `fieldCriterion_ramsey` (openai/math @ fd4aeeb2,
`lean/OAI/Combinatorics/EuclideanRamsey`, Apache-2.0, ported to the module system by header-only
changes). OAI's definitions
(`Ramsey`, `FieldCriterion`, `augmented`, `multiply`, `Coeff`) are used directly.
The generic ring algebra (`Pcert`, evaluation, diagonal) is in `AlgebraicPlusThree.SixPointAlgebra`.
-/

namespace OAI
noncomputable section
open scoped TensorProduct
namespace EuclideanRamsey
namespace SixPoint

/-! ## 2. The unit-circle case in OAI's coordinates -/

section Field

variable (b : Fin 6 → Space 2)

/-- Stereographic parameter from the pole `(-1, 0)`. -/
def tpar (i : Fin 6) : Coeff b := coordinate b i 1 / (1 + coordinate b i 0)

theorem stereo_field {K : Type*} [Field K] [CharZero K] (X Y : K) (h1 : X ^ 2 + Y ^ 2 = 1)
    (h2 : 1 + X ≠ 0) :
    1 + (Y / (1 + X)) ^ 2 ≠ 0 ∧
      (1 - (Y / (1 + X)) ^ 2) * (1 + (Y / (1 + X)) ^ 2)⁻¹ = X ∧
      2 * (Y / (1 + X)) * (1 + (Y / (1 + X)) ^ 2)⁻¹ = Y := by
  have ht : 1 + (Y / (1 + X)) ^ 2 = 2 / (1 + X) := by
    field_simp
    linear_combination h1
  rw [ht]
  refine ⟨div_ne_zero two_ne_zero h2, ?_, ?_⟩
  · field_simp
    linear_combination (-1) * h1
  · field_simp

variable {b}

theorem coord_facts (hb : ∀ i, b i 0 ^ 2 + b i 1 ^ 2 = 1) (hp : ∀ i, 1 + b i 0 ≠ 0) (i : Fin 6) :
    coordinate b i 0 ^ 2 + coordinate b i 1 ^ 2 = 1 ∧ 1 + coordinate b i 0 ≠ 0 := by
  constructor
  · apply Subtype.ext
    simpa [coordinate] using hb i
  · intro h
    apply hp i
    have := congrArg (fun z : Coeff b => (z : ℝ)) h
    simpa [coordinate] using this

/-- OAI's tensor ring maps: `ι₁ x = x ⊗ 1`, `ι₂ y = 1 ⊗ y`, `μ = multiply`. -/
def ι₁ : Coeff b →+* TensorRing b := Algebra.TensorProduct.includeLeftRingHom
def ι₂ : Coeff b →+* TensorRing b := (Algebra.TensorProduct.includeRight).toRingHom
def μ : TensorRing b →+* Coeff b := (multiply b).toRingHom

theorem μ_ι₁ (z : Coeff b) : μ (ι₁ z) = z := by
  simp [μ, ι₁, multiply, Algebra.TensorProduct.lmul'_apply_tmul]
theorem μ_ι₂ (z : Coeff b) : μ (ι₂ z) = z := by
  simp [μ, ι₂, multiply, Algebra.TensorProduct.lmul'_apply_tmul]

theorem fieldCriterion_six (hb : ∀ i, b i 0 ^ 2 + b i 1 ^ 2 = 1) (hp : ∀ i, 1 + b i 0 ≠ 0)
    (hinj : Function.Injective b) : FieldCriterion b := by
  set t : Fin 6 → Coeff b := tpar b with ht_def
  have hst := fun i => stereo_field _ _ (coord_facts hb hp i).1 (coord_facts hb hp i).2
  -- the parametrization recovers OAI's augmented coordinates
  have haug : ∀ i α, pv (t i) ((1 + t i ^ 2)⁻¹) α = augmented b i α := by
    intro i α
    rcases α with _ | j
    · simp only [pv, augmented]
      exact mul_inv_cancel₀ (hst i).1
    · fin_cases j
      · simpa [pv, augmented, ht_def, tpar] using (hst i).2.1
      · simpa [pv, augmented, ht_def, tpar] using (hst i).2.2
  -- distinct points have distinct parameters
  have htinj : Function.Injective t := by
    intro i j hij
    apply hinj
    have h0 := haug i (some 0)
    have h1 := haug i (some 1)
    rw [hij, haug j (some 0)] at h0
    rw [hij, haug j (some 1)] at h1
    have e0 : b i 0 = b j 0 := congrArg Subtype.val h0.symm
    have e1 : b i 1 = b j 1 := congrArg Subtype.val h1.symm
    ext k
    fin_cases k
    · exact e0
    · exact e1
  have hne : ∀ i j : Fin 6, i ≠ j → t i - t j ≠ 0 := fun i j h =>
    sub_ne_zero.mpr (fun e => h (htinj e))
  have hk : kap t ≠ 0 := by
    rw [kap, det3_vandermonde, det3_vandermonde]
    simp only [tri1, tri2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) <;>
      exact hne _ _ (by decide)
  set c : Coeff b := -2 * kap t with hc_def
  have hc : c ≠ 0 := mul_ne_zero (by norm_num) hk
  refine ⟨fun α β => ι₁ c⁻¹ * Pcert (fun k => ι₁ (t k)) (fun k => ι₂ (t k)) α β, ?_, ?_⟩
  · intro i
    have hl : ∀ α, augmented b i α ⊗ₜ[ℚ] (1 : Coeff b)
        = pv (ι₁ (t i)) (ι₁ ((1 + t i ^ 2)⁻¹)) α := by
      intro α
      rw [← haug i α]
      exact map_pv (R := Coeff b) (S := TensorRing b) ι₁ _ _ α
    have hr : ∀ β, (1 : Coeff b) ⊗ₜ[ℚ] augmented b i β
        = pv (ι₂ (t i)) (ι₂ ((1 + t i ^ 2)⁻¹)) β := by
      intro β
      rw [← haug i β]
      exact map_pv (R := Coeff b) (S := TensorRing b) ι₂ _ _ β
    simp only [hl, hr, Pcert]
    rw [eval_Pm_Mco]
    have hv := gprod_vanish (fun k => ι₁ (t k)) (fun k => ι₂ (t k)) i
    rw [hv, mul_zero]
  · intro j j'
    have hm := Pcert_mult (R := TensorRing b) (S := Coeff b) (fun k => ι₁ (t k))
      (fun k => ι₂ (t k)) t μ (fun k => μ_ι₁ _) (fun k => μ_ι₂ _) j j'
    calc multiply b (ι₁ c⁻¹ * Pcert (fun k => ι₁ (t k)) (fun k => ι₂ (t k)) (some j) (some j'))
        = μ (ι₁ c⁻¹) * μ (Pcert (fun k => ι₁ (t k)) (fun k => ι₂ (t k)) (some j) (some j')) :=
          map_mul (multiply b) _ _
      _ = c⁻¹ * (if j = j' then c else 0) := by rw [μ_ι₁, hm]
      _ = if j = j' then 1 else 0 := by
          split_ifs
          · exact inv_mul_cancel₀ hc
          · exact mul_zero _

end Field

/-! ## 3. Normalization and assembly -/

/-- Ramsey transfers along a similarity. -/
theorem ramsey_of_scaled {s d e : ℕ} {a : Fin s → Space d} {b : Fin s → Space e} {k : ℝ}
    (hk : 0 < k) (h : ∀ i j, dist (a i) (a j) = k * dist (b i) (b j)) (hb : Ramsey b) :
    Ramsey a := by
  intro n hn
  obtain ⟨D, hD, H⟩ := hb n hn
  refine ⟨D, hD, fun col => ?_⟩
  obtain ⟨b', hb', m, hm⟩ := H (fun x => col (k • x))
  refine ⟨fun i => k • b' i, fun i j => ?_, m, hm⟩
  rw [dist_smul₀, hb' i j, h i j, Real.norm_eq_abs, abs_of_pos hk]

theorem dist_sq_two (p q : Space 2) : dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
    Real.dist_eq, sq_abs, sq_abs]

/-- Six distinct points on a circle are Ramsey. -/
theorem six_circle_ramsey (a : Fin 6 → Space 2) (ha : Function.Injective a) (c : Space 2) (r : ℝ)
    (hc : ∀ i, dist (a i) c = r) : Ramsey a := by
  have hr : 0 ≤ r := hc 0 ▸ dist_nonneg
  rcases hr.eq_or_lt with hr0 | hrpos
  · exact zero_radius_ramsey a c (by simpa [← hr0] using hc)
  have hrne : r ≠ 0 := hrpos.ne'
  have hcoord := circle_coordinates a c r hc
  set X : Fin 6 → ℝ := fun i => a i 0 - c 0 with hX
  set Y : Fin 6 → ℝ := fun i => a i 1 - c 1 with hY
  -- choose a rotation `z` that moves the pole off the configuration
  let bad : Finset (Space 2) :=
    Finset.univ.image (fun i => WithLp.toLp 2 ![-X i / r, Y i / r])
  obtain ⟨z, hz, hzbad⟩ := (circle_infinite 0 1 one_pos).exists_notMem_finset bad
  have hz2 : z 0 ^ 2 + z 1 ^ 2 = 1 := by
    have := circle_coordinates (fun _ : Fin 1 => z) 0 1 (fun _ => hz) 0
    simpa using this
  let b : Fin 6 → Space 2 := fun i =>
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
    exact (pow_left_inj₀ dist_nonneg (mul_nonneg hr dist_nonneg) two_ne_zero).mp h1
  have hbinj : Function.Injective b := by
    intro i j h
    apply ha
    have := hdist i j
    rw [h, dist_self, mul_zero] at this
    exact dist_eq_zero.mp this
  exact ramsey_of_scaled hrpos hdist
    (fieldCriterion_ramsey b (by norm_num) (by norm_num) hbinj (fieldCriterion_six hbc hpole hbinj))

end SixPoint

/-- **Theorem B(a)** (prior work; see the module doc). Any at most six distinct points on a circle form a Euclidean Ramsey configuration.
Fewer than six points: extend to six on the same circle and restrict. -/
theorem circle_ramsey_of_le_six {s : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin 2))
    (hs : s ≤ 6) (ha : Function.Injective a)
    (hsph : ∃ c : EuclideanSpace ℝ (Fin 2), ∃ r : ℝ, ∀ i, a i ∈ Metric.sphere c r) :
    Ramsey a := by
  obtain ⟨c, r, hc⟩ := hsph
  have hc' : ∀ i, dist (a i) c = r := fun i => Metric.mem_sphere.mp (hc i)
  rcases (le_or_gt r 0) with hr | hrpos
  · refine SixPoint.zero_radius_ramsey a c (fun i => le_antisymm ?_ dist_nonneg)
    rw [hc' i]; exact hr
  obtain ⟨b, hb, hbc, f, hf⟩ := SixPoint.extend_to_six a hs ha c r hrpos hc'
  have hramsey := SixPoint.ramsey_restrict b f (SixPoint.six_circle_ramsey b hb c r hbc)
  have he : b ∘ f = a := funext hf
  rwa [he] at hramsey

end EuclideanRamsey
end
end OAI

#print axioms OAI.EuclideanRamsey.circle_ramsey_of_le_six
