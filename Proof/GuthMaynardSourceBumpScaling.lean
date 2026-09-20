import GuthMaynardJIterationBumpWeld
import GuthMaynardJIterationPoisson

/-!
# Exact scaling of the source plateau bump

The medium-frequency ell restriction needs a plateau radius growing by a
subpower of `T`.  The underlying `ContDiffBump` has a fixed shape, so its
Fourier constants grow only linearly with the radius.  This module proves that
fact from the literal definition instead of treating the radius-dependent
Schwartz seminorm as an opaque constant.
-/

open scoped Real FourierTransform ContDiff
open MeasureTheory Metric

noncomputable section
namespace GuthMaynardJIteration

/-- The radius-`R` bump is the radius-one bump under the exact dilation
`x ↦ x/R`. -/
theorem sourceBump_eq_unit_dilation
    (R : ℝ) (hR : 0 < R) (x : ℝ) :
    sourceBump R hR x = sourceBump 1 zero_lt_one (x / R) := by
  have hratio : R⁻¹ * (R * 2) = (2 : ℝ) := by field_simp
  simp [sourceBump, ContDiffBump.apply, div_eq_mul_inv, mul_comm, hratio]

/-- Exact Fourier dilation identity for the source bump. -/
theorem fourier_sourceBump_eq_radius_mul_unit
    (R : ℝ) (hR : 0 < R) (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ => (sourceBump R hR x : ℂ)) xi =
      (R : ℂ) * FourierTransform.fourier
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) (R * xi) := by
  have hfun : (fun x : ℝ => (sourceBump R hR x : ℂ)) =
      (fun x : ℝ => (sourceBump 1 zero_lt_one (R⁻¹ * x) : ℂ)) := by
    funext x
    congr 1
    rw [sourceBump_eq_unit_dilation]
    congr 1
    field_simp
  rw [hfun, fourier_dilation
    (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
    (inv_ne_zero hR.ne') xi]
  simp [abs_of_pos hR, Complex.real_smul, mul_comm]

/-- Radius-uniform decay: for `R ≥ 1`, every Fourier envelope costs only the
linear factor `R` relative to the fixed radius-one bump. -/
theorem sourceBump_fourier_decay_scaled
    {R : ℝ} (hR : 0 < R) (hRone : 1 ≤ R) (q : ℕ) (xi : ℝ) :
    ‖FourierTransform.fourier
        (fun x : ℝ => (sourceBump R hR x : ℂ)) xi‖ ≤
      (R * sourceBumpFourierConstant 1 zero_lt_one q) /
        (1 + |xi|) ^ q := by
  have hC : 0 ≤ sourceBumpFourierConstant 1 zero_lt_one q :=
    sourceBumpFourierConstant_nonneg 1 zero_lt_one q
  have habs : |xi| ≤ |R * xi| := by
    rw [abs_mul, abs_of_pos hR]
    nlinarith [abs_nonneg xi]
  have hden : (1 + |xi|) ^ q ≤ (1 + |R * xi|) ^ q := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) q
  have hdiv : sourceBumpFourierConstant 1 zero_lt_one q /
        (1 + |R * xi|) ^ q ≤
      sourceBumpFourierConstant 1 zero_lt_one q / (1 + |xi|) ^ q := by
    exact div_le_div_of_nonneg_left hC (by positivity) hden
  rw [fourier_sourceBump_eq_radius_mul_unit R hR xi, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  calc
    R * ‖FourierTransform.fourier
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) (R * xi)‖ ≤
      R * (sourceBumpFourierConstant 1 zero_lt_one q /
        (1 + |R * xi|) ^ q) := by
          exact mul_le_mul_of_nonneg_left
            (sourceBump_fourier_decay 1 zero_lt_one q (R * xi)) hR.le
    _ ≤ R * (sourceBumpFourierConstant 1 zero_lt_one q /
        (1 + |xi|) ^ q) := mul_le_mul_of_nonneg_left hdiv hR.le
    _ = (R * sourceBumpFourierConstant 1 zero_lt_one q) /
        (1 + |xi|) ^ q := by ring

/-- Source regularity package for a variable radius, with every Fourier
constant exposed as a linear radius loss. -/
theorem sourceBump_scaled_fourier_package
    {R : ℝ} (hR : 0 < R) (hRone : 1 ≤ R) (q : ℕ) :
    0 ≤ R * sourceBumpFourierConstant 1 zero_lt_one (q + 2) ∧
    0 ≤ R * sourceBumpFourierConstant 1 zero_lt_one 0 ∧
    (∀ xi, ‖FourierTransform.fourier
      (fun x : ℝ => (sourceBump R hR x : ℂ)) xi‖ ≤
        (R * sourceBumpFourierConstant 1 zero_lt_one 2) /
          (1 + |xi|) ^ 2) ∧
    (∀ xi, ‖FourierTransform.fourier
      (fun x : ℝ => (sourceBump R hR x : ℂ)) xi‖ ≤
        (R * sourceBumpFourierConstant 1 zero_lt_one (q + 2)) /
          (1 + |xi|) ^ (q + 2)) ∧
    (∀ xi, ‖FourierTransform.fourier
      (fun x : ℝ => (sourceBump R hR x : ℂ)) xi‖ ≤
        R * sourceBumpFourierConstant 1 zero_lt_one 0) := by
  refine ⟨mul_nonneg hR.le
      (sourceBumpFourierConstant_nonneg 1 zero_lt_one (q + 2)),
    mul_nonneg hR.le
      (sourceBumpFourierConstant_nonneg 1 zero_lt_one 0),
    sourceBump_fourier_decay_scaled hR hRone 2,
    sourceBump_fourier_decay_scaled hR hRone (q + 2), ?_⟩
  intro xi
  simpa using sourceBump_fourier_decay_scaled hR hRone 0 xi

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceBump_eq_unit_dilation
#print axioms GuthMaynardJIteration.fourier_sourceBump_eq_radius_mul_unit
#print axioms GuthMaynardJIteration.sourceBump_fourier_decay_scaled
#print axioms GuthMaynardJIteration.sourceBump_scaled_fourier_package
