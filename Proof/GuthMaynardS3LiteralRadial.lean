import GuthMaynardS3LiteralKernel

/-!
# Exact common-radial substitution behind Proposition 7.1

The two successive positive dilations have Jacobian r². No absolute value,
nonzero-frequency restriction, or N factor is discarded in this identity.
-/

namespace GuthMaynardS3LiteralRadial

open MeasureTheory
open scoped BigOperators
open GuthMaynardS3LiteralKernel GuthMaynardEquation55Split
open GuthMaynardRatioKernelIdentity GuthMaynardSectionThreeCutoff

noncomputable section

theorem sourceIm_cyclic (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    sourceIm N W m3 m1 m2 = sourceIm N W m1 m2 m3 := by
  unfold sourceIm
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  ring

/-- Positive one-dimensional dilation with the Jacobian inside the integral. -/
theorem integral_dilate_pos (f : ℝ → ℂ) {r : ℝ} (hr : 0<r) :
    (∫ x : ℝ,f x) = ∫ v : ℝ,(r : ℂ)*f (r*v) := by
  rw [integral_const_mul,Measure.integral_comp_mul_left]
  rw [abs_of_pos (inv_pos.mpr hr)]
  rw [Complex.real_smul,← mul_assoc]
  change (∫ x : ℝ,f x) = (r : ℂ)*((r⁻¹ : ℝ) : ℂ)*(∫ x : ℝ,f x)
  rw [← Complex.ofReal_mul,mul_inv_cancel₀ hr.ne']
  simp

def radialWeight (r v1 v2 : ℝ) : ℂ :=
  (r : ℂ)^2 * sectionThreeCutoff r *
    sectionThreeCutoff (r*v1) * sectionThreeCutoff (r*v2)

def radialRatioProduct (W : Finset ℝ) (v1 v2 : ℝ) : ℂ :=
  ratioDirichletKernel W v1 * ratioDirichletKernel W (v2/v1) *
    ratioDirichletKernel W (1/v2)

def radialIntegrand (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ)
    (r v1 v2 : ℝ) : ℂ :=
  Complex.exp (((-2*Real.pi*(N : ℝ)*
    ((m1 : ℝ)*v1+(m2 : ℝ)*v2+(m3 : ℝ))*r : ℝ) : ℂ)*Complex.I) *
    radialWeight r v1 v2 * radialRatioProduct W v1 v2

set_option maxHeartbeats 600000 in
/-- The exact common-radial integral, with r retained as the outer variable.
The remaining localization step is a Fubini swap followed by uniform Fourier
decay of radialWeight in r. -/
theorem sourceIm_eq_radial_integral (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    sourceIm N W m1 m2 m3 = (N : ℂ)^3 *
      ∫ r : ℝ,∫ v1 : ℝ,∫ v2 : ℝ,radialIntegrand N W m1 m2 m3 r v1 v2 := by
  rw [← sourceIm_cyclic N W m1 m2 m3,sourceIm_eq_ratio_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  by_cases hr : 0<r
  · rw [integral_dilate_pos _ hr]
    apply integral_congr_ae
    filter_upwards with v1
    rw [integral_dilate_pos _ hr,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with v2
    have hratio1 : (r*v1)/r=v1 := by field_simp
    have hratio2 : (r*v2)/(r*v1)=v2/v1 := by
      exact mul_div_mul_left v2 v1 hr.ne'
    have hratio3 : r/(r*v2)=1/v2 := by
      rw [div_mul_eq_div_div,div_self hr.ne',one_div]
    rw [hratio1,hratio2,hratio3]
    unfold radialIntegrand radialWeight radialRatioProduct
    have hphase :
      (-2*Real.pi*(N : ℝ)*((m3 : ℝ)*r+(m1 : ℝ)*(r*v1)+(m2 : ℝ)*(r*v2))) =
        -2*Real.pi*(N : ℝ)*((m1 : ℝ)*v1+(m2 : ℝ)*v2+(m3 : ℝ))*r := by ring
    rw [hphase]
    ring
  · have hz := sectionThreeCutoff_supported r (by
      intro h; have := h.1; linarith)
    simp [radialIntegrand,radialWeight,hz]

/-- The transformed bump vanishes outside the source ratio box. -/
theorem radialWeight_supported {r v1 v2 : ℝ} (h : radialWeight r v1 v2 ≠ 0) :
    r ∈ Set.Icc (1 : ℝ) 2 ∧ v1 ∈ Set.Icc (1/2 : ℝ) 2 ∧
      v2 ∈ Set.Icc (1/2 : ℝ) 2 := by
  have hr : r ∈ Set.Icc (1 : ℝ) 2 := by
    by_contra hn
    exact h (by simp [radialWeight,sectionThreeCutoff_supported r hn])
  have hv1 : r*v1 ∈ Set.Icc (1 : ℝ) 2 := by
    by_contra hn
    exact h (by simp [radialWeight,sectionThreeCutoff_supported (r*v1) hn])
  have hv2 : r*v2 ∈ Set.Icc (1 : ℝ) 2 := by
    by_contra hn
    exact h (by simp [radialWeight,sectionThreeCutoff_supported (r*v2) hn])
  have hv1pos : 0<v1 := by nlinarith [hr.1,hv1.1]
  have hv2pos : 0<v2 := by nlinarith [hr.1,hv2.1]
  exact ⟨hr,⟨by nlinarith [hr.2,hv1.1],by nlinarith [hr.1,hv1.2]⟩,
    ⟨by nlinarith [hr.2,hv2.1],by nlinarith [hr.1,hv2.2]⟩⟩

end
end GuthMaynardS3LiteralRadial

#print axioms GuthMaynardS3LiteralRadial.sourceIm_eq_radial_integral
