module

public import AlgebraicPlusThree.SixPointAlgebra
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Generic algebra for Theorem B(b): the certificate `f = g₁₂₃ · (s − s')`, and the circumcentre

Light-import companion of `AlgebraicPlusThree.AlgPlusThree`. The ring identities are proved once over an
arbitrary `CommRing R` and transported by ring homomorphisms, reusing `AlgebraicPlusThree.SixPointAlgebra`
(`gco`, `Mco`, `Pm`, `Kc`, `det3`, `eval_Pm_Mco`).
-/

namespace OAI
noncomputable section
namespace EuclideanRamsey
namespace AlgPlusThree
open SixPoint

section Algebra

variable {R : Type*} [CommRing R]

/-- The diagonal `(1,1)`-form `s − s'` (coefficient `hd i j` of `s^i s'^j`). -/
def hd : Fin 2 → Fin 2 → R := ![![0, -1], ![1, 0]]

theorem gfun_hd (x y : R) : gfun hd x y = x - y := by
  simp [gfun, hd]; ring

/-- If `e` kills `y − x`, the factor `s − s'` kills the evaluation at `(x, y)`. -/
theorem vanish_of_kill (E e K G x y : R) (h : (y - x) * e = 0) :
    E * e * K * (G * gfun hd x y) = 0 := by
  rw [gfun_hd, show E * e * K * (G * (x - y)) = -(E * K * G) * ((y - x) * e) by ring, h,
    mul_zero]

/-- `vanish_of_kill` as a rewrite rule (avoids instance unification in `TensorRing`). -/
theorem kill_eq (E e K G x y : R) :
    E * e * K * (G * gfun hd x y) = -(E * K * G) * ((y - x) * e) := by
  rw [gfun_hd]; ring

/-- The diagonal: `m(g₁₂₃ · (s − s')) = −V (s − s')²`, so the spatial block of `P` is `2V · I`. -/
theorem P3_diag (t : Fin 3 → R) (j j' : Fin 2) :
    Pm (Mco (gco t t) hd) (some j) (some j') = if j = j' then 2 * det3 (t * t) t 1 else 0 := by
  fin_cases j <;> fin_cases j' <;>
    simp [Pm, Mco, gco, det3, hd, Kc, Fin.sum_univ_three] <;> ring

section Hom

variable {S : Type*} [CommRing S]

theorem map_hd (φ : R →+* S) (i j : Fin 2) : φ (hd i j) = hd i j := by
  fin_cases i <;> fin_cases j <;> simp [hd]

theorem P3_mult (x y : Fin 3 → R) (t : Fin 3 → S) (φ : R →+* S) (hx : ∀ k, φ (x k) = t k)
    (hy : ∀ k, φ (y k) = t k) (j j' : Fin 2) :
    φ (Pm (Mco (gco x y) hd) (some j) (some j')) = if j = j' then 2 * det3 (t * t) t 1 else 0 := by
  have ex : φ ∘ x = t := funext hx
  have ey : φ ∘ y = t := funext hy
  simp only [Pm, map_sum, map_mul, map_Kc φ, map_Mco φ, map_gco φ, map_hd φ, ex, ey]
  exact P3_diag t j j'

end Hom

end Algebra

/-! ## Three distinct concyclic points: non-collinear, and the circumcentre by Cramer -/

section Circum

variable {X1 Y1 X2 Y2 X3 Y3 C0 C1 R : ℝ}

theorem noncol_aux {u0 u1 v0 v1 w0 w1 : ℝ} (E2 : 2 * (w0 * u0 + w1 * u1) + (u0 ^ 2 + u1 ^ 2) = 0)
    (E3 : 2 * (w0 * v0 + w1 * v1) + (v0 ^ 2 + v1 ^ 2) = 0) (hD : u0 * v1 - u1 * v0 = 0)
    (hu : ¬(u0 = 0 ∧ u1 = 0)) (hv : ¬(v0 = 0 ∧ v1 = 0)) (huv : ¬(u0 = v0 ∧ u1 = v1)) : False := by
  obtain ⟨n, hn_def⟩ : ∃ n, n = u0 ^ 2 + u1 ^ 2 := ⟨_, rfl⟩
  obtain ⟨k, hk_def⟩ : ∃ k, k = u0 * v0 + u1 * v1 := ⟨_, rfl⟩
  have hv0 : n * v0 = k * u0 := by linear_combination (-u1) * hD + v0 * hn_def - u0 * hk_def
  have hv1 : n * v1 = k * u1 := by linear_combination u0 * hD + v1 * hn_def - u1 * hk_def
  have hmain : n * k * (k - n) = 0 := by
    rw [hn_def, hk_def]
    linear_combination (u0 ^ 2 + u1 ^ 2) ^ 2 * E3 - (u0 ^ 2 + u1 ^ 2) * (u0 * v0 + u1 * v1) * E2
      - (2 * (u0 ^ 2 + u1 ^ 2) * (u0 * w1 - u1 * w0) + (u0 * v1 - u1 * v0) * (u0 ^ 2 + u1 ^ 2)) * hD
  by_cases hn : n = 0
  · exact hu ⟨by nlinarith [sq_nonneg u0, sq_nonneg u1], by nlinarith [sq_nonneg u0, sq_nonneg u1]⟩
  rcases mul_eq_zero.mp hmain with hk | hk
  · rcases mul_eq_zero.mp hk with hk | hk
    · exact hn hk
    · rw [hk, zero_mul] at hv0 hv1
      exact hv ⟨(mul_eq_zero.mp hv0).resolve_left hn, (mul_eq_zero.mp hv1).resolve_left hn⟩
  · rw [sub_eq_zero.mp hk] at hv0 hv1
    exact huv ⟨(mul_left_cancel₀ hn hv0).symm, (mul_left_cancel₀ hn hv1).symm⟩

theorem circum_D_ne (h1 : (X1 - C0) ^ 2 + (Y1 - C1) ^ 2 = R)
    (h2 : (X2 - C0) ^ 2 + (Y2 - C1) ^ 2 = R) (h3 : (X3 - C0) ^ 2 + (Y3 - C1) ^ 2 = R)
    (h12 : ¬(X1 = X2 ∧ Y1 = Y2)) (h13 : ¬(X1 = X3 ∧ Y1 = Y3)) (h23 : ¬(X2 = X3 ∧ Y2 = Y3)) :
    (X2 - X1) * (Y3 - Y1) - (Y2 - Y1) * (X3 - X1) ≠ 0 := fun hD =>
  noncol_aux (w0 := X1 - C0) (w1 := Y1 - C1) (by linear_combination h2 - h1)
    (by linear_combination h3 - h1) hD
    (fun h => h12 ⟨by linarith [h.1], by linarith [h.2]⟩)
    (fun h => h13 ⟨by linarith [h.1], by linarith [h.2]⟩)
    (fun h => h23 ⟨by linarith [h.1], by linarith [h.2]⟩)

theorem circum_C0 (h1 : (X1 - C0) ^ 2 + (Y1 - C1) ^ 2 = R)
    (h2 : (X2 - C0) ^ 2 + (Y2 - C1) ^ 2 = R) (h3 : (X3 - C0) ^ 2 + (Y3 - C1) ^ 2 = R)
    (hD : (X2 - X1) * (Y3 - Y1) - (Y2 - Y1) * (X3 - X1) ≠ 0) :
    C0 = ((X2 ^ 2 + Y2 ^ 2 - X1 ^ 2 - Y1 ^ 2) * (Y3 - Y1)
      - (X3 ^ 2 + Y3 ^ 2 - X1 ^ 2 - Y1 ^ 2) * (Y2 - Y1))
      / (2 * ((X2 - X1) * (Y3 - Y1) - (Y2 - Y1) * (X3 - X1))) := by
  rw [eq_div_iff (mul_ne_zero two_ne_zero hD)]
  linear_combination (-(Y3 - Y1)) * (h2 - h1) + (Y2 - Y1) * (h3 - h1)

theorem circum_C1 (h1 : (X1 - C0) ^ 2 + (Y1 - C1) ^ 2 = R)
    (h2 : (X2 - C0) ^ 2 + (Y2 - C1) ^ 2 = R) (h3 : (X3 - C0) ^ 2 + (Y3 - C1) ^ 2 = R)
    (hD : (X2 - X1) * (Y3 - Y1) - (Y2 - Y1) * (X3 - X1) ≠ 0) :
    C1 = ((X2 - X1) * (X3 ^ 2 + Y3 ^ 2 - X1 ^ 2 - Y1 ^ 2)
      - (X3 - X1) * (X2 ^ 2 + Y2 ^ 2 - X1 ^ 2 - Y1 ^ 2))
      / (2 * ((X2 - X1) * (Y3 - Y1) - (Y2 - Y1) * (X3 - X1))) := by
  rw [eq_div_iff (mul_ne_zero two_ne_zero hD)]
  linear_combination (-(X2 - X1)) * (h3 - h1) + (X3 - X1) * (h2 - h1)

end Circum

end AlgPlusThree
end EuclideanRamsey
end
end OAI
