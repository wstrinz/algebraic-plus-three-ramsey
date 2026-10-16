module

public import AlgebraicPlusThree.AlgPlusThreeAlgebra
public import OAI.Combinatorics.EuclideanRamsey.Model

@[expose] public section

/-!
# Theorem B(b), core: the field criterion for unit-circle points, algebraic outside three indices

Imports OAI's `Model` only (not `Main`), so it compiles without loading OAI's proof.
The separability idempotent of `K = ℚ(t_i : i algebraic)` is pushed from `K ⊗ K` into `F ⊗ F`.
-/

namespace OAI
noncomputable section
open scoped TensorProduct
namespace EuclideanRamsey
namespace AlgPlusThree
open SixPoint

/-- The real algebraic numbers. -/
abbrev Alg : IntermediateField ℚ ℝ := algebraicClosure ℚ ℝ

/-- Membership in a subfield, by closure under the field operations. -/
macro "alg_mem" : tactic => `(tactic|
  repeat
    first
    | assumption
    | apply div_mem
    | apply add_mem
    | apply sub_mem
    | apply mul_mem
    | apply inv_mem
    | apply pow_mem
    | apply neg_mem
    | apply one_mem _
    | apply ofNat_mem _)

/-- Copy of `SixPoint.stereo_field` (kept here so this module need not import OAI `Main`). -/
theorem stereo3 {K : Type*} [Field K] [CharZero K] (X Y : K) (h1 : X ^ 2 + Y ^ 2 = 1)
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

section Core

variable {s : ℕ} {b : Fin s → Space 2}

/-- Stereographic parameter from the pole `(-1, 0)`. -/
def tp (b : Fin s → Space 2) (i : Fin s) : Coeff b := coordinate b i 1 / (1 + coordinate b i 0)

def j₁ : Coeff b →+* TensorRing b := Algebra.TensorProduct.includeLeftRingHom
def j₂ : Coeff b →+* TensorRing b := (Algebra.TensorProduct.includeRight).toRingHom
def jm : TensorRing b →+* Coeff b := (multiply b).toRingHom

theorem jm_j₁ (z : Coeff b) : jm (j₁ z) = z := by
  simp [jm, j₁, multiply, Algebra.TensorProduct.lmul'_apply_tmul]
theorem jm_j₂ (z : Coeff b) : jm (j₂ z) = z := by
  simp [jm, j₂, multiply, Algebra.TensorProduct.lmul'_apply_tmul]

/-- As `SixPoint.coord_facts`, for any number of points. -/
theorem coord_facts3 (hb : ∀ i, b i 0 ^ 2 + b i 1 ^ 2 = 1) (hp : ∀ i, 1 + b i 0 ≠ 0) (i : Fin s) :
    coordinate b i 0 ^ 2 + coordinate b i 1 ^ 2 = 1 ∧ 1 + coordinate b i 0 ≠ 0 := by
  constructor
  · apply Subtype.ext
    simpa [coordinate] using hb i
  · intro h
    apply hp i
    have := congrArg (fun z : Coeff b => (z : ℝ)) h
    simpa [coordinate] using this

/-- **The subtle point.** For finitely many algebraic elements `S` of `F = Coeff b`, the
separability idempotent of `K = ℚ(S)` lives in `K ⊗ K`; its image under `K.val ⊗ K.val` in
`F ⊗ F` still has `m(e) = 1` (`m` commutes with the map) and kills `1 ⊗ x − x ⊗ 1` for `x ∈ S`. -/
theorem exists_sep_idem (S : Set (Coeff b)) [Finite S] (hS : ∀ x ∈ S, (x : ℝ) ∈ Alg) :
    ∃ e : TensorRing b, multiply b e = 1 ∧ ∀ x ∈ S, (j₂ x - j₁ x) * e = 0 := by
  let K := IntermediateField.adjoin ℚ S
  have : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin (fun x hx =>
    (IntermediateField.isAlgebraic_iff.mpr (mem_algebraicClosure_iff.mp (hS x hx))).isIntegral)
  have : Algebra.FormallyUnramified ℚ K := Algebra.FormallyUnramified.of_isSeparable ℚ K
  obtain ⟨e₀, he₀, he₁⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := ℚ) (S := K)).mp inferInstance
  let φ : K ⊗[ℚ] K →ₐ[ℚ] TensorRing b := Algebra.TensorProduct.map K.val K.val
  refine ⟨φ e₀, ?_, fun x hx => ?_⟩
  · have hc : ∀ z : K ⊗[ℚ] K, multiply b (φ z) = K.val (Algebra.TensorProduct.lmul' ℚ z) := by
      intro z
      induction z with
      | tmul x y => simp [φ, multiply, Algebra.TensorProduct.lmul'_apply_tmul]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [hc, he₁, map_one]
  · have := congrArg φ (he₀ ⟨x, IntermediateField.subset_adjoin ℚ S hx⟩)
    simpa [φ, j₁, j₂, Algebra.TensorProduct.map_tmul] using this

/-- The field criterion for unit-circle points off the pole, all algebraic except those indexed
by the three distinct indices `w`. -/
theorem fieldCriterion_alg3 (hb : ∀ i, b i 0 ^ 2 + b i 1 ^ 2 = 1) (hp : ∀ i, 1 + b i 0 ≠ 0)
    (hinj : Function.Injective b) (w : Fin 3 → Fin s) (hw : Function.Injective w)
    (halg : ∀ i, i ∉ Set.range w → ∀ j, b i j ∈ Alg) : FieldCriterion b := by
  set t : Fin s → Coeff b := tp b with ht_def
  have hst := fun i => stereo3 _ _ (coord_facts3 hb hp i).1 (coord_facts3 hb hp i).2
  have haug : ∀ i α, pv (t i) ((1 + t i ^ 2)⁻¹) α = augmented b i α := by
    intro i α
    rcases α with _ | j
    · simp only [pv, augmented]
      exact mul_inv_cancel₀ (hst i).1
    · fin_cases j
      · simpa [pv, augmented, ht_def, tp] using (hst i).2.1
      · simpa [pv, augmented, ht_def, tp] using (hst i).2.2
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
  -- the separability idempotent of `ℚ(t_i : i ∉ w)`
  have : Finite (Set.range fun i : {i // i ∉ Set.range w} => t i) := Set.finite_range _
  obtain ⟨e, he1, he⟩ := exists_sep_idem (Set.range fun i : {i // i ∉ Set.range w} => t i) (by
    rintro _ ⟨⟨i, hi⟩, rfl⟩
    have h0 := halg i hi 0
    have h1 := halg i hi 1
    have : ((t i : Coeff b) : ℝ) = b i 1 / (1 + b i 0) := by simp [ht_def, tp, coordinate]
    rw [this]
    alg_mem)
  have hk : det3 ((fun k => t (w k)) * (fun k => t (w k))) (fun k => t (w k)) 1 ≠ 0 := by
    rw [det3_vandermonde]
    have hne : ∀ k l : Fin 3, k ≠ l → t (w k) - t (w l) ≠ 0 := fun k l h =>
      sub_ne_zero.mpr (fun e => h (hw (htinj e)))
    exact mul_ne_zero (mul_ne_zero (hne 0 1 (by decide)) (hne 0 2 (by decide)))
      (hne 1 2 (by decide))
  obtain ⟨c, hc_def⟩ : ∃ c : Coeff b,
      c = 2 * det3 ((fun k => t (w k)) * (fun k => t (w k))) (fun k => t (w k)) 1 := ⟨_, rfl⟩
  have hc : c ≠ 0 := by rw [hc_def]; exact mul_ne_zero two_ne_zero hk
  refine ⟨fun α β => j₁ c⁻¹ * e *
    Pm (Mco (gco (fun k => j₁ (t (w k))) (fun k => j₂ (t (w k)))) hd) α β, ?_, ?_⟩
  · intro i
    have hl : ∀ α, augmented b i α ⊗ₜ[ℚ] (1 : Coeff b)
        = pv (j₁ (t i)) (j₁ ((1 + t i ^ 2)⁻¹)) α := by
      intro α
      rw [← haug i α]
      exact map_pv (R := Coeff b) (S := TensorRing b) j₁ _ _ α
    have hr : ∀ β, (1 : Coeff b) ⊗ₜ[ℚ] augmented b i β
        = pv (j₂ (t i)) (j₂ ((1 + t i ^ 2)⁻¹)) β := by
      intro β
      rw [← haug i β]
      exact map_pv (R := Coeff b) (S := TensorRing b) j₂ _ _ β
    simp only [hl, hr]
    rw [eval_Pm_Mco]
    by_cases hi : i ∈ Set.range w
    · obtain ⟨a, rfl⟩ := hi
      have hv : gfun (gco (fun k => j₁ (t (w k))) (fun k => j₂ (t (w k))))
          (j₁ (t (w a))) (j₂ (t (w a))) = 0 := gfun_gco_self _ _ a
      rw [hv, zero_mul, mul_zero]
    · rw [kill_eq (R := TensorRing b), he _ ⟨⟨i, hi⟩, rfl⟩, mul_zero]
  · intro j j'
    have hm := P3_mult (R := TensorRing b) (S := Coeff b) (fun k => j₁ (t (w k)))
      (fun k => j₂ (t (w k))) (fun k => t (w k)) jm (fun k => jm_j₁ _) (fun k => jm_j₂ _) j j'
    rw [← hc_def] at hm
    have he1' : jm e = 1 := he1
    show jm (j₁ c⁻¹ * e * Pm (Mco (gco (fun k => j₁ (t (w k))) (fun k => j₂ (t (w k)))) hd)
      (some j) (some j')) = _
    rw [map_mul, map_mul, jm_j₁, he1', hm]
    split_ifs
    · rw [mul_one, inv_mul_cancel₀ hc]
    · rw [mul_zero]

end Core

theorem alg_of_sq {x : ℝ} (h : x ^ 2 ∈ Alg) : x ∈ Alg :=
  mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow two_pos (mem_algebraicClosure_iff.mp h))

end AlgPlusThree
end EuclideanRamsey
end
end OAI
