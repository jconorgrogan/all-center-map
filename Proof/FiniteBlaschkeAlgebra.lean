import Mathlib.Analysis.Complex.CanonicalDecomposition

/-!
# Finite Blaschke boundary and center algebra

Mathlib supplies individual canonical factors but not their canonical
decomposition.  This file proves the deterministic finite-product properties
needed by the Dirichlet-L minimum-modulus step.
-/

namespace FiniteBlaschkeAlgebra

open Complex Set Metric
open scoped BigOperators

noncomputable section

def shiftedCanonicalFactor (c : ℂ) (R : ℝ) (ρ z : ℂ) : ℂ :=
  Complex.canonicalFactor R (ρ - c) (z - c)

def finiteBlaschkeProduct
    (c : ℂ) (R : ℝ) (F : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) : ℂ :=
  ∏ ρ ∈ F, (shiftedCanonicalFactor c R ρ z) ^ m ρ

theorem norm_shiftedCanonicalFactor_eq_one_on_sphere
    {c ρ z : ℂ} {R : ℝ}
    (hρ : ρ ∈ Metric.ball c R) (hz : z ∈ Metric.sphere c R) :
    ‖shiftedCanonicalFactor c R ρ z‖ = 1 := by
  have hρ' : ρ - c ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hρ
  have hz' : z - c ∈ Metric.sphere (0 : ℂ) R := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hz
  exact Complex.norm_canonicalFactor_eval_circle_eq_one hρ' hz'

/-- A finite product of translated canonical factors has unit norm on the
outer circle. -/
theorem norm_finiteBlaschkeProduct_eq_one_on_sphere
    {c z : ℂ} {R : ℝ} {F : Finset ℂ} {m : ℂ → ℕ}
    (hF : ∀ ρ ∈ F, ρ ∈ Metric.ball c R)
    (hz : z ∈ Metric.sphere c R) :
    ‖finiteBlaschkeProduct c R F m z‖ = 1 := by
  simp only [finiteBlaschkeProduct, norm_prod, norm_pow]
  apply Finset.prod_eq_one
  intro ρ hρ
  rw [norm_shiftedCanonicalFactor_eq_one_on_sphere (hF ρ hρ) hz, one_pow]

/-- Multiplying by the finite Blaschke product preserves the numerator norm
on the outer circle exactly. -/
theorem norm_mul_finiteBlaschkeProduct_eq_on_sphere
    (f : ℂ → ℂ) {c z : ℂ} {R : ℝ} {F : Finset ℂ} {m : ℂ → ℕ}
    (hF : ∀ ρ ∈ F, ρ ∈ Metric.ball c R)
    (hz : z ∈ Metric.sphere c R) :
    ‖f z * finiteBlaschkeProduct c R F m z‖ = ‖f z‖ := by
  rw [norm_mul, norm_finiteBlaschkeProduct_eq_one_on_sphere hF hz, mul_one]

theorem norm_shiftedCanonicalFactor_center
    {c ρ : ℂ} {R : ℝ} (hR : 0 < R) (hρc : ρ ≠ c) :
    ‖shiftedCanonicalFactor c R ρ c‖ = R / ‖ρ - c‖ := by
  have hw : ρ - c ≠ 0 := sub_ne_zero.mpr hρc
  unfold shiftedCanonicalFactor
  rw [Complex.canonicalFactor_apply]
  simp only [sub_self, mul_zero, sub_zero, zero_sub]
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hR, norm_neg, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR]
  field_simp

/-- At the disk center every canonical factor belonging to a noncentral
interior zero has norm at least one. -/
theorem one_le_norm_shiftedCanonicalFactor_center
    {c ρ : ℂ} {R : ℝ} (hR : 0 < R)
    (hρ : ρ ∈ Metric.ball c R) (hρc : ρ ≠ c) :
    1 ≤ ‖shiftedCanonicalFactor c R ρ c‖ := by
  rw [norm_shiftedCanonicalFactor_center hR hρc]
  have hnorm : ‖ρ - c‖ < R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hρ
  exact (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr hρc))).2 hnorm.le

/-- The finite Blaschke product can only increase norm at a zero-free disk
center. -/
theorem one_le_norm_finiteBlaschkeProduct_center
    {c : ℂ} {R : ℝ} {F : Finset ℂ} {m : ℂ → ℕ}
    (hR : 0 < R)
    (hF : ∀ ρ ∈ F, ρ ∈ Metric.ball c R)
    (hc : c ∉ F) :
    1 ≤ ‖finiteBlaschkeProduct c R F m c‖ := by
  simp only [finiteBlaschkeProduct, norm_prod, norm_pow]
  exact Finset.one_le_prod (fun ρ hρ =>
    one_le_pow₀ (one_le_norm_shiftedCanonicalFactor_center hR
      (hF ρ hρ) (fun h => hc (h ▸ hρ))))

theorem norm_le_norm_mul_finiteBlaschkeProduct_center
    (f : ℂ → ℂ) {c : ℂ} {R : ℝ} {F : Finset ℂ} {m : ℂ → ℕ}
    (hR : 0 < R)
    (hF : ∀ ρ ∈ F, ρ ∈ Metric.ball c R)
    (hc : c ∉ F) :
    ‖f c‖ ≤ ‖f c * finiteBlaschkeProduct c R F m c‖ := by
  rw [norm_mul]
  exact le_mul_of_one_le_right (norm_nonneg _) <|
    one_le_norm_finiteBlaschkeProduct_center hR hF hc

end

end FiniteBlaschkeAlgebra
