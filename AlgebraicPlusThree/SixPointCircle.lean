module

public import OAI.Combinatorics.EuclideanRamsey.Model

@[expose] public section

/-!
# Circle helpers for the six-point case (adapted from OpenAI's EuclideanRamsey circle files)

Every lemma here adapts a lemma of openai/math @ fd4aeeb2,
`lean/OAI/Combinatorics/EuclideanRamsey/CircleGeometry.lean` and `CircleExtension.lean`
(Apache-2.0, Copyright OpenAI). Modification: copied into namespace `OAI.EuclideanRamsey.SixPoint`
(the development build did not include those modules), and `extend_to_five` generalized to
`extend_to_six` (the target size 5 replaced by 6). This file is under the Apache License 2.0; it is listed in `NOTICE`.
-/

namespace OAI
noncomputable section
namespace EuclideanRamsey.SixPoint

/-- Adapts `CircleConsequence.ramsey_restrict` (CircleGeometry.lean). -/
theorem ramsey_restrict {s t d : ℕ} (a : Fin t → Space d)
    (f : Fin s → Fin t) (ha : Ramsey a) : Ramsey (a ∘ f) := by
  intro r hr
  obtain ⟨D, hD, h⟩ := ha r hr
  refine ⟨D, hD, ?_⟩
  intro c
  obtain ⟨b, hb, k, hk⟩ := h c
  exact ⟨b ∘ f, fun i j => hb (f i) (f j), k, fun i => hk (f i)⟩

/-- Adapts `CircleConsequence.zero_radius_ramsey` (CircleGeometry.lean). -/
theorem zero_radius_ramsey {s : ℕ} (a : Fin s → Space 2)
    (c : Space 2) (h : ∀ i, dist (a i) c = 0) : Ramsey a := by
  intro r hr
  refine ⟨1, by omega, ?_⟩
  intro coloring
  refine ⟨fun _ => 0, ?_, coloring 0, fun _ => rfl⟩
  intro i j
  have hi : a i = c := dist_eq_zero.mp (h i)
  have hj : a j = c := dist_eq_zero.mp (h j)
  simp [hi, hj]

/-- Adapts `CircleConsequence.circle_coordinates` (CircleGeometry.lean). -/
theorem circle_coordinates {s : ℕ} (a : Fin s → Space 2)
    (c : Space 2) (r : ℝ) (hc : ∀ i, dist (a i) c = r) :
    ∀ i, (a i 0-c 0)^2 + (a i 1-c 1)^2 = r^2 := by
  intro i
  have h := congrArg (fun x : ℝ => x^2) (hc i)
  simpa [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs] using h

/-- Adapts `CircleConsequence.stereographic` (CircleExtension.lean). -/
def stereographic (c : Space 2) (r t : ℝ) : Space 2 :=
  c + r • WithLp.toLp 2 ![(1-t^2)/(1+t^2), (2*t)/(1+t^2)]

/-- Adapts `CircleConsequence.stereographic_recover` (CircleExtension.lean). -/
theorem stereographic_recover (t : ℝ) :
    ((2*t)/(1+t^2)) / (1 + (1-t^2)/(1+t^2)) = t := by
  have hd : 1+t^2 ≠ 0 := by positivity
  have he : 1 + (1-t^2)/(1+t^2) = 2/(1+t^2) := by field_simp; ring
  rw [he, div_div]
  field_simp

/-- Adapts `CircleConsequence.stereographic_injective` (CircleExtension.lean). -/
theorem stereographic_injective (c : Space 2) (r : ℝ) (hr : 0 < r) :
    Function.Injective (stereographic c r) := by
  intro t u h
  have h₀ := congrArg (fun p : Space 2 => p 0) h
  have h₁ := congrArg (fun p : Space 2 => p 1) h
  have hx : (1-t^2)/(1+t^2) = (1-u^2)/(1+u^2) := by
    apply mul_left_cancel₀ (ne_of_gt hr)
    apply add_left_cancel (a := c 0)
    simpa only [stereographic, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply,
      Matrix.cons_val_zero, smul_eq_mul] using h₀
  have hy : (2*t)/(1+t^2) = (2*u)/(1+u^2) := by
    apply mul_left_cancel₀ (ne_of_gt hr)
    apply add_left_cancel (a := c 1)
    simpa only [stereographic, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply,
      Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul] using h₁
  calc
    t = ((2*t)/(1+t^2)) / (1 + (1-t^2)/(1+t^2)) := (stereographic_recover t).symm
    _ = ((2*u)/(1+u^2)) / (1 + (1-u^2)/(1+u^2)) := by rw [hx, hy]
    _ = u := stereographic_recover u

/-- Adapts `CircleConsequence.stereographic_on_circle` (CircleExtension.lean). -/
theorem stereographic_on_circle (c : Space 2) (r t : ℝ) (hr : 0 < r) :
    dist (stereographic c r t) c = r := by
  have hd : 1+t^2 ≠ 0 := by positivity
  have hs : ((1-t^2)/(1+t^2))^2 + ((2*t)/(1+t^2))^2 = 1 := by
    field_simp
    ring
  have he : dist (stereographic c r t) c ^ 2 = r^2 := by
    simp only [dist_eq_norm, stereographic, add_sub_cancel_left]
    rw [norm_smul, mul_pow]
    simp only [Real.norm_eq_abs, sq_abs, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, sq_abs]
    rw [hs, mul_one]
  have hn : 0 ≤ dist (stereographic c r t) c := dist_nonneg
  nlinarith

/-- Adapts `CircleConsequence.circle_infinite` (CircleExtension.lean). -/
theorem circle_infinite (c : Space 2) (r : ℝ) (hr : 0 < r) :
    {p : Space 2 | dist p c = r}.Infinite := by
  apply (Set.infinite_range_of_injective (stereographic_injective c r hr)).mono
  rintro p ⟨t, rfl⟩
  exact stereographic_on_circle c r t hr

/-- Adapts `CircleConsequence.extend_to_five` (CircleExtension.lean), with 5 replaced by 6. -/
theorem extend_to_six {s : ℕ} (a : Fin s → Space 2)
    (hs : s ≤ 6) (ha : Function.Injective a)
    (c : Space 2) (r : ℝ) (hr : 0 < r)
    (hc : ∀ i, dist (a i) c = r) :
    ∃ b : Fin 6 → Space 2, Function.Injective b ∧
      (∀ j, dist (b j) c = r) ∧ ∃ f : Fin s → Fin 6, ∀ i, b (f i) = a i := by
  classical
  let S : Finset (Space 2) := Finset.univ.image a
  have hS : S.card = s := by simp [S, Finset.card_image_of_injective _ ha]
  have hSc : ∀ p ∈ S, dist p c = r := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact hc i
  obtain ⟨T, hTc, hT⟩ := (circle_infinite c r hr).exists_subset_card_eq 6
  have hST : 6 ≤ (S ∪ T).card := by
    rw [← hT]
    exact Finset.card_le_card Finset.subset_union_right
  obtain ⟨U, hSU, hUst, hU⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_union_left : S ⊆ S ∪ T) (by omega : S.card ≤ 6) hST
  let e : U ≃ Fin 6 := Finset.equivFinOfCardEq hU
  let b : Fin 6 → Space 2 := fun j => (e.symm j).val
  refine ⟨b, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  · intro j
    have hj : b j ∈ S ∪ T := hUst (e.symm j).property
    rcases Finset.mem_union.mp hj with hj | hj
    · exact hSc _ hj
    · exact hTc hj
  · let f : Fin s → Fin 6 := fun i => e ⟨a i, hSU (by simp [S])⟩
    refine ⟨f, ?_⟩
    intro i
    simp [b, f]

end EuclideanRamsey.SixPoint
end
end OAI
