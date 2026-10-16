module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Option

@[expose] public section

namespace OAI
noncomputable section
namespace EuclideanRamsey
namespace SixPoint

/-! ## 1. Generic algebra over a commutative ring -/

section Algebra

variable {R : Type*} [CommRing R]

/-- Determinant of the `3 × 3` matrix with columns `a`, `b`, `c`. -/
def det3 (a b c : Fin 3 → R) : R :=
  a 0 * (b 1 * c 2 - b 2 * c 1) - b 0 * (a 1 * c 2 - a 2 * c 1) + c 0 * (a 1 * b 2 - a 2 * b 1)

/-- Coefficients (`g i j` of `s^i s'^j`) of the graph form
`det [[s s', s, s', 1], [x_a y_a, x_a, y_a, 1]_{a = 0,1,2}]`. -/
def gco (x y : Fin 3 → R) : Fin 2 → Fin 2 → R :=
  ![![-det3 (x * y) x y, det3 (x * y) x 1], ![-det3 (x * y) y 1, det3 x y 1]]

/-- Evaluation of a `(1,1)`-form. -/
def gfun (g : Fin 2 → Fin 2 → R) (s s' : R) : R :=
  g 0 0 + g 0 1 * s' + g 1 0 * s + g 1 1 * s * s'

theorem gfun_gco_self (x y : Fin 3 → R) (a : Fin 3) : gfun (gco x y) (x a) (y a) = 0 := by
  fin_cases a <;> simp [gfun, gco, det3] <;> ring

/-- Coefficient matrix (`M a b` of `s^a s'^b`) of the product of two `(1,1)`-forms. -/
def Mco (g h : Fin 2 → Fin 2 → R) : Fin 3 → Fin 3 → R :=
  ![![g 0 0 * h 0 0, g 0 0 * h 0 1 + g 0 1 * h 0 0, g 0 1 * h 0 1],
    ![g 0 0 * h 1 0 + g 1 0 * h 0 0,
      g 0 0 * h 1 1 + g 1 1 * h 0 0 + g 1 0 * h 0 1 + g 0 1 * h 1 0,
      g 0 1 * h 1 1 + g 1 1 * h 0 1],
    ![g 1 0 * h 1 0, g 1 0 * h 1 1 + g 1 1 * h 1 0, g 1 1 * h 1 1]]

/-- Columns of `K = 2 C⁻¹`, OAI-indexed (`none` = affine coordinate). -/
def Kc : Option (Fin 2) → Fin 3 → R
  | none => ![1, 0, 1]
  | some j => ![![1, 0, -1], ![0, 1, 0]] j

/-- `P = Kᵀ M K`. -/
def Pm (M : Fin 3 → Fin 3 → R) : Matrix (Option (Fin 2)) (Option (Fin 2)) R :=
  fun α β => ∑ a, ∑ b, Kc α a * M a b * Kc β b

/-- The augmented circle point `(1, (1-z²)/(1+z²), 2z/(1+z²))`, written with `u = (1+z²)⁻¹`. -/
def pv (z u : R) : Option (Fin 2) → R
  | none => (1 + z ^ 2) * u
  | some j => ![(1 - z ^ 2) * u, 2 * z * u] j

theorem eval_Pm_Mco (g h : Fin 2 → Fin 2 → R) (z z' u u' e : R) :
    ∑ α, ∑ β, pv z u α * (e * Pm (Mco g h) α β) * pv z' u' β
      = e * (4 * u * u') * (gfun g z z' * gfun h z z') := by
  simp [Fintype.sum_option, Fin.sum_univ_two, Fin.sum_univ_three, Pm, Kc, pv, Mco, gfun]
  ring

/-- First and second triple of a six-tuple. -/
def tri1 (x : Fin 6 → R) : Fin 3 → R := ![x 0, x 1, x 2]
def tri2 (x : Fin 6 → R) : Fin 3 → R := ![x 3, x 4, x 5]

/-- The certificate: `f = g₁₂₃ · g₄₅₆`, `P = Kᵀ M K`. -/
def Pcert (x y : Fin 6 → R) : Matrix (Option (Fin 2)) (Option (Fin 2)) R :=
  Pm (Mco (gco (tri1 x) (tri1 y)) (gco (tri2 x) (tri2 y)))

theorem gprod_vanish (x y : Fin 6 → R) (i : Fin 6) :
    gfun (gco (tri1 x) (tri1 y)) (x i) (y i) * gfun (gco (tri2 x) (tri2 y)) (x i) (y i) = 0 := by
  fin_cases i
  · exact mul_eq_zero_of_left (gfun_gco_self (tri1 x) (tri1 y) 0) _
  · exact mul_eq_zero_of_left (gfun_gco_self (tri1 x) (tri1 y) 1) _
  · exact mul_eq_zero_of_left (gfun_gco_self (tri1 x) (tri1 y) 2) _
  · exact mul_eq_zero_of_right _ (gfun_gco_self (tri2 x) (tri2 y) 0)
  · exact mul_eq_zero_of_right _ (gfun_gco_self (tri2 x) (tri2 y) 1)
  · exact mul_eq_zero_of_right _ (gfun_gco_self (tri2 x) (tri2 y) 2)

/-- `κ = V(t₁,t₂,t₃) V(t₄,t₅,t₆)`. -/
def kap (t : Fin 6 → R) : R :=
  det3 (tri1 t * tri1 t) (tri1 t) 1 * det3 (tri2 t * tri2 t) (tri2 t) 1

theorem det3_vandermonde (t : Fin 3 → R) :
    det3 (t * t) t 1 = (t 0 - t 1) * (t 0 - t 2) * (t 1 - t 2) := by
  simp [det3]; ring

/-- The diagonal: `m(P)` restricted to the spatial block is `-2κ · I`. -/
theorem Pcert_diag (t : Fin 6 → R) (j j' : Fin 2) :
    Pcert t t (some j) (some j') = if j = j' then -2 * kap t else 0 := by
  fin_cases j <;> fin_cases j' <;>
    simp [Pcert, Pm, Mco, gco, det3, tri1, tri2, Kc, kap, Fin.sum_univ_three] <;> ring

section Hom

variable {S : Type*} [CommRing S]

theorem map_pv (φ : R →+* S) (z u : R) (α : Option (Fin 2)) : φ (pv z u α) = pv (φ z) (φ u) α := by
  rcases α with _ | j
  · simp [pv]
  · fin_cases j <;> simp [pv, map_ofNat]

theorem map_Kc (φ : R →+* S) (α : Option (Fin 2)) (a : Fin 3) : φ (Kc α a) = Kc α a := by
  rcases α with _ | j
  · fin_cases a <;> simp [Kc]
  · fin_cases j <;> fin_cases a <;> simp [Kc]

theorem map_det3 (φ : R →+* S) (a b c : Fin 3 → R) : φ (det3 a b c) = det3 (φ ∘ a) (φ ∘ b) (φ ∘ c) := by
  simp [det3]

theorem map_gco (φ : R →+* S) (x y : Fin 3 → R) (i j : Fin 2) :
    φ (gco x y i j) = gco (φ ∘ x) (φ ∘ y) i j := by
  have hxy : φ ∘ (x * y) = (φ ∘ x) * (φ ∘ y) := by ext k; simp
  have h1 : φ ∘ (1 : Fin 3 → R) = 1 := by ext k; simp
  fin_cases i <;> fin_cases j <;> simp [gco, map_det3 φ, hxy, h1]

theorem map_Mco (φ : R →+* S) (g h : Fin 2 → Fin 2 → R) (a b : Fin 3) :
    φ (Mco g h a b) = Mco (fun i j => φ (g i j)) (fun i j => φ (h i j)) a b := by
  fin_cases a <;> fin_cases b <;> simp [Mco]

theorem map_Pcert (φ : R →+* S) (x y : Fin 6 → R) (α β : Option (Fin 2)) :
    φ (Pcert x y α β) = Pcert (φ ∘ x) (φ ∘ y) α β := by
  have h1 : ∀ z : Fin 6 → R, φ ∘ tri1 z = tri1 (φ ∘ z) := by
    intro z; ext k; fin_cases k <;> rfl
  have h2 : ∀ z : Fin 6 → R, φ ∘ tri2 z = tri2 (φ ∘ z) := by
    intro z; ext k; fin_cases k <;> rfl
  simp only [Pcert, Pm, map_sum, map_mul, map_Kc φ, map_Mco φ, map_gco φ, h1, h2]

/-- The multiplied certificate: if `φ` sends both coordinate families to `t`, the spatial block
of `φ P` is `-2κ(t) · I`. -/
theorem Pcert_mult (x y : Fin 6 → R) (t : Fin 6 → S) (φ : R →+* S) (hx : ∀ k, φ (x k) = t k)
    (hy : ∀ k, φ (y k) = t k) (j j' : Fin 2) :
    φ (Pcert x y (some j) (some j')) = if j = j' then -2 * kap t else 0 := by
  have ex : φ ∘ x = t := funext hx
  have ey : φ ∘ y = t := funext hy
  rw [map_Pcert, ex, ey, Pcert_diag]

end Hom

end Algebra

end SixPoint
end EuclideanRamsey
end
end OAI
