import GuthMaynardS3LiteralRadialDecay
import GuthMaynardS3LiteralProfile

/-! # The integrable radial kernel and exact inner Fourier coefficient -/

namespace GuthMaynardS3LiteralFubini

open MeasureTheory
open scoped BigOperators
open GuthMaynardS3LiteralRadial GuthMaynardS3LiteralRadialDecay
open GuthMaynardS3LiteralProfile GuthMaynardRatioKernelIdentity
open GuthMaynardSectionThreeCutoff

noncomputable section

def radialBox : Set ((ℝ×ℝ)×ℝ) :=
  (Set.Icc (1/2 : ℝ) 2 ×ˢ Set.Icc (1/2 : ℝ) 2) ×ˢ Set.Icc (1 : ℝ) 2

theorem radialBox_compact : IsCompact radialBox :=
  (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc

theorem radialIntegrand_continuousOn (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    ContinuousOn (fun p : (ℝ×ℝ)×ℝ => radialIntegrand N W m1 m2 m3 p.2 p.1.1 p.1.2)
      radialBox := by
  intro p hp
  have h1 : p.1.1 ≠ 0 := by have := hp.1.1.1; linarith
  have h2 : p.1.2 ≠ 0 := by have := hp.1.2.1; linarith
  have hc1 : ContinuousAt (fun q : (ℝ×ℝ)×ℝ => q.1.1) p := by fun_prop
  have hc2 : ContinuousAt (fun q : (ℝ×ℝ)×ℝ => q.1.2) p := by fun_prop
  have hR1 : ContinuousAt (fun q : (ℝ×ℝ)×ℝ => ratioDirichletKernel W q.1.1) p := (continuousAt_ratioDirichletKernel W h1).comp (f := fun q : (ℝ×ℝ)×ℝ => q.1.1) hc1
  have hR2 : ContinuousAt (fun q : (ℝ×ℝ)×ℝ => ratioDirichletKernel W (q.1.2/q.1.1)) p := (continuousAt_ratioDirichletKernel W (div_ne_zero h2 h1)).comp (f := fun q : (ℝ×ℝ)×ℝ => q.1.2/q.1.1) (hc2.div hc1 h1)
  have hR3 : ContinuousAt (fun q : (ℝ×ℝ)×ℝ => ratioDirichletKernel W (1/q.1.2)) p := (continuousAt_ratioDirichletKernel W (one_div_ne_zero h2)).comp (f := fun q : (ℝ×ℝ)×ℝ => 1/q.1.2)
    (continuousAt_const.div hc2 h2)
  have hc := sectionThreeCutoff_contDiff.continuous
  have hphase : ContinuousAt (fun q : (ℝ×ℝ)×ℝ =>
      Complex.exp (((-2*Real.pi*(N : ℝ)*
        ((m1 : ℝ)*q.1.1+(m2 : ℝ)*q.1.2+(m3 : ℝ))*q.2 : ℝ) : ℂ)*Complex.I)) p := by fun_prop
  have hweight : ContinuousAt (fun q : (ℝ×ℝ)×ℝ => radialWeight q.2 q.1.1 q.1.2) p := by
    unfold radialWeight
    fun_prop
  exact (hphase.mul hweight |>.mul ((hR1.mul hR2).mul hR3)).continuousWithinAt

theorem radialIntegrand_zero_off_box (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ)
    {p : (ℝ×ℝ)×ℝ} (hp : p ∉ radialBox) :
    radialIntegrand N W m1 m2 m3 p.2 p.1.1 p.1.2 = 0 := by
  have hz : radialWeight p.2 p.1.1 p.1.2=0 := by
    by_contra hne
    obtain ⟨hr,h1,h2⟩ := radialWeight_supported hne
    exact hp ⟨⟨h1,h2⟩,hr⟩
  simp [radialIntegrand,hz]

/-- Absolute integrability is derived from the actual compact ratio box,
so the radial/ratio Fubini swap has no integrability premise. -/
theorem integrable_radialIntegrand (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    Integrable (fun p : (ℝ×ℝ)×ℝ => radialIntegrand N W m1 m2 m3 p.2 p.1.1 p.1.2) := by
  have hi := (radialIntegrand_continuousOn N W m1 m2 m3).integrableOn_compact (μ := (volume : Measure ((ℝ×ℝ)×ℝ))) radialBox_compact
  have hh := hi.integrable_indicator radialBox_compact.measurableSet
  apply hh.congr
  filter_upwards with p
  by_cases hp : p ∈ radialBox
  · simp [hp]
  · simp [hp,radialIntegrand_zero_off_box N W m1 m2 m3 hp]

theorem radial_integral_swap (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    (∫ r : ℝ,∫ v1 : ℝ,∫ v2 : ℝ,radialIntegrand N W m1 m2 m3 r v1 v2) =
      ∫ v1 : ℝ,∫ v2 : ℝ,∫ r : ℝ,radialIntegrand N W m1 m2 m3 r v1 v2 := by
  have hi := integrable_radialIntegrand N W m1 m2 m3
  have his : Integrable (fun p : (ℝ×ℝ)×ℝ =>
      radialIntegrand N W m1 m2 m3 p.2 p.1.1 p.1.2)
      ((volume : Measure (ℝ×ℝ)).prod (volume : Measure ℝ)) := hi
  calc
    _ = ∫ r : ℝ,∫ v : ℝ×ℝ,radialIntegrand N W m1 m2 m3 r v.1 v.2 := by
      apply integral_congr_ae
      filter_upwards [his.prod_left_ae] with r hr
      exact (integral_prod _ hr).symm
    _ = ∫ v : ℝ×ℝ,∫ r : ℝ,radialIntegrand N W m1 m2 m3 r v.1 v.2 :=
      (integral_integral_swap his).symm
    _ = _ := integral_prod _ his.integral_prod_left

/-- The inner coefficient is the Fourier transform of the actual radial
weight at exactly N(m1 v1 + m2 v2 + m3). -/
theorem inner_radial_eq_fourier (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) (v1 v2 : ℝ) :
    (∫ r : ℝ,radialIntegrand N W m1 m2 m3 r v1 v2) =
      FourierTransform.fourier (fun r => radialWeight r v1 v2)
        ((N : ℝ)*((m1 : ℝ)*v1+(m2 : ℝ)*v2+(m3 : ℝ))) *
      radialRatioProduct W v1 v2 := by
  unfold radialIntegrand
  rw [integral_mul_const,Real.fourier_real_eq_integral_exp_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

/-- Exact source (7.4) followed by the radial Fourier transform. -/
theorem sourceIm_eq_inner_fourier (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    GuthMaynardEquation55Split.sourceIm N W m1 m2 m3 = (N : ℂ)^3 *
      ∫ v1 : ℝ,∫ v2 : ℝ,
        FourierTransform.fourier (fun r => radialWeight r v1 v2)
          ((N : ℝ)*((m1 : ℝ)*v1+(m2 : ℝ)*v2+(m3 : ℝ))) *
          radialRatioProduct W v1 v2 := by
  rw [sourceIm_eq_radial_integral,radial_integral_swap]
  simp_rw [inner_radial_eq_fourier]

end
end GuthMaynardS3LiteralFubini

#print axioms GuthMaynardS3LiteralFubini.sourceIm_eq_inner_fourier
