import GuthMaynardS3LiteralLocalization

/-! # Literal unbalanced-frequency exclusion in Proposition 7.1 -/

namespace GuthMaynardS3LiteralFrequencyGeometry

open MeasureTheory
open GuthMaynardS3LiteralLocalization GuthMaynardS3LiteralRadialDecay

noncomputable section

/-- On the exact ratio box, the affine strip is empty if the third
frequency exceeds the two possible cancellations and the retained width. -/
theorem localizedRatioMass_eq_zero_of_unbalanced {N : ℕ} (hN : 0<N)
    (W : Finset ℝ) (m1 m2 m3 : ℤ) {rho : ℝ}
    (h12 : |(m1 : ℝ)| ≤ |(m2 : ℝ)|)
    (hgap : 4*|(m2 : ℝ)|+rho/(N : ℝ) < |(m3 : ℝ)|) :
    localizedRatioMass N W m1 m2 m3 rho=0 := by
  have hNR : 0<(N : ℝ) := Nat.cast_pos.mpr hN
  unfold localizedRatioMass
  apply integral_eq_zero_of_ae
  have hbox : MeasurableSet ratioBox := (isCompact_Icc.prod isCompact_Icc).measurableSet
  filter_upwards [ae_restrict_mem hbox] with v hv
  apply if_neg
  intro hstrip
  have hv1 : |v.1| ≤ 2 := by rw [abs_of_nonneg (by linarith [hv.1.1])]; exact hv.1.2
  have hv2 : |v.2| ≤ 2 := by rw [abs_of_nonneg (by linarith [hv.2.1])]; exact hv.2.2
  have hfirst : |(m1 : ℝ)*v.1+(m2 : ℝ)*v.2| ≤ 4*|(m2 : ℝ)| := by
    have h1 := mul_le_mul_of_nonneg_left hv1 (abs_nonneg (m1 : ℝ))
    have h2 := mul_le_mul_of_nonneg_left hv2 (abs_nonneg (m2 : ℝ))
    have ht := abs_add_le ((m1 : ℝ)*v.1) ((m2 : ℝ)*v.2)
    rw [abs_mul,abs_mul] at ht
    nlinarith only [h1,h2,ht,h12]
  have hlin : |(m1 : ℝ)*v.1+(m2 : ℝ)*v.2+(m3 : ℝ)| ≤ rho/(N : ℝ) := by
    unfold affineFrequency at hstrip
    rw [abs_mul,abs_of_pos hNR] at hstrip
    apply (le_div_iff₀ hNR).2
    nlinarith only [hstrip]
  have ht := abs_add_le ((m1 : ℝ)*v.1+(m2 : ℝ)*v.2+(m3 : ℝ))
    (-((m1 : ℝ)*v.1+(m2 : ℝ)*v.2))
  rw [← sub_eq_add_neg,abs_neg] at ht
  have heq : (m1 : ℝ)*v.1+(m2 : ℝ)*v.2+(m3 : ℝ)-((m1 : ℝ)*v.1+(m2 : ℝ)*v.2) = (m3 : ℝ) := by ring
  rw [heq] at ht
  linarith only [ht,hfirst,hlin,hgap]

/-- The excluded sector costs only the already proved radial Fourier tail. -/
theorem norm_sourceIm_unbalanced_le_tail {N : ℕ} (hN : 0<N)
    (W : Finset ℝ) (m1 m2 m3 : ℤ) {rho : ℝ} (hrho : 0<rho) (q : ℕ)
    (h12 : |(m1 : ℝ)| ≤ |(m2 : ℝ)|)
    (hgap : 4*|(m2 : ℝ)|+rho/(N : ℝ) < |(m3 : ℝ)|) :
    ‖GuthMaynardEquation55Split.sourceIm N W m1 m2 m3‖ ≤
      (9/4 : ℝ)*(N : ℝ)^3*radialDerivativeBudget q*(W.card : ℝ)^3/rho^q := by
  have hh := norm_sourceIm_le_localized N W m1 m2 m3 hrho q
  rw [localizedRatioMass_eq_zero_of_unbalanced hN W m1 m2 m3 h12 hgap,mul_zero,zero_add] at hh
  convert hh using 1 <;> ring

end
end GuthMaynardS3LiteralFrequencyGeometry

#print axioms GuthMaynardS3LiteralFrequencyGeometry.norm_sourceIm_unbalanced_le_tail
