import GuthMaynardS3LiteralFubini

/-!
# Literal per-frequency localization in Proposition 7.1

The strip is |N(m1 v1+m2 v2+m3)|≤rho. The discarded part is bounded by
an explicit universal derivative constant times N³|W|³/rho^q. In particular,
the T^eta width needed for a power-saving tail is retained, not suppressed.
-/

namespace GuthMaynardS3LiteralLocalization

open MeasureTheory
open scoped BigOperators
open GuthMaynardS3LiteralFubini GuthMaynardS3LiteralRadial
open GuthMaynardS3LiteralRadialDecay GuthMaynardS3LiteralProfile
open GuthMaynardRatioKernelIdentity GuthMaynardHeathBrownIccIocEndpointAdapter
open GuthMaynardLemma43FourierIBP

noncomputable section

def ratioBox : Set (ℝ×ℝ) := Set.Icc (1/2 : ℝ) 2 ×ˢ Set.Icc (1/2 : ℝ) 2

def affineFrequency (N : ℕ) (m1 m2 m3 : ℤ) (v : ℝ×ℝ) : ℝ :=
  (N : ℝ)*((m1 : ℝ)*v.1+(m2 : ℝ)*v.2+(m3 : ℝ))

def localizedRatioMass (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) (rho : ℝ) : ℝ :=
  ∫ v : ℝ×ℝ in ratioBox,
    if |affineFrequency N m1 m2 m3 v| ≤ rho then ‖radialRatioProduct W v.1 v.2‖ else 0

def innerField (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) (v : ℝ×ℝ) : ℂ :=
  FourierTransform.fourier (fun r => radialWeight r v.1 v.2)
    (affineFrequency N m1 m2 m3 v) * radialRatioProduct W v.1 v.2

theorem integrable_innerField (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    Integrable (innerField N W m1 m2 m3) := by
  have hi := (integrable_radialIntegrand N W m1 m2 m3).integral_prod_left
  apply hi.congr
  filter_upwards with v
  exact inner_radial_eq_fourier N W m1 m2 m3 v.1 v.2

theorem innerField_zero_off_box (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ)
    {v : ℝ×ℝ} (hv : v ∉ ratioBox) : innerField N W m1 m2 m3 v=0 := by
  have hz : (fun r => radialWeight r v.1 v.2) = fun _ => 0 := by
    funext r
    by_contra hne
    obtain ⟨_,h1,h2⟩ := radialWeight_supported hne
    exact hv ⟨h1,h2⟩
  unfold innerField
  rw [hz,Real.fourier_real_eq_integral_exp_smul]
  simp

theorem ratioProduct_norm_le (W : Finset ℝ) (v : ℝ×ℝ) :
    ‖radialRatioProduct W v.1 v.2‖ ≤ (W.card : ℝ)^3 := by
  unfold radialRatioProduct
  rw [norm_mul,norm_mul]
  have h1 := norm_ratioDirichletKernel_le_card W v.1
  have h2 := norm_ratioDirichletKernel_le_card W (v.2/v.1)
  have h3 := norm_ratioDirichletKernel_le_card W (1/v.2)
  calc
    _ ≤ (W.card : ℝ)*(W.card : ℝ)*(W.card : ℝ) := by gcongr
    _ = _ := by ring

theorem ratioProduct_continuousOn (W : Finset ℝ) :
    ContinuousOn (fun v : ℝ×ℝ => radialRatioProduct W v.1 v.2) ratioBox := by
  intro v hv
  have h1 : v.1 ≠ 0 := by have := hv.1.1; linarith
  have h2 : v.2 ≠ 0 := by have := hv.2.1; linarith
  have hR1 : ContinuousAt (fun z : ℝ×ℝ => ratioDirichletKernel W z.1) v :=
    (continuousAt_ratioDirichletKernel W h1).comp (f := fun z : ℝ×ℝ => z.1) continuous_fst.continuousAt
  have hR2 : ContinuousAt (fun z : ℝ×ℝ => ratioDirichletKernel W (z.2/z.1)) v :=
    (continuousAt_ratioDirichletKernel W (div_ne_zero h2 h1)).comp (f := fun z : ℝ×ℝ => z.2/z.1)
      (continuous_snd.continuousAt.div continuous_fst.continuousAt h1)
  have hR3 : ContinuousAt (fun z : ℝ×ℝ => ratioDirichletKernel W (1/z.2)) v :=
    (continuousAt_ratioDirichletKernel W (one_div_ne_zero h2)).comp (f := fun z : ℝ×ℝ => 1/z.2)
      (continuousAt_const.div continuous_snd.continuousAt h2)
  exact ((hR1.mul hR2).mul hR3).continuousWithinAt

theorem radialDerivativeBudget_nonneg (q : ℕ) : 0 ≤ radialDerivativeBudget q :=
  (norm_nonneg _).trans (radialWeight_derivative_le (v1 := 0) (v2 := 0)
    (by norm_num) (by norm_num) q 0)

theorem radial_fourier_uniform {v1 v2 : ℝ} (h1 : |v1|≤2) (h2 : |v2|≤2) (xi : ℝ) :
    ‖FourierTransform.fourier (fun r => radialWeight r v1 v2) xi‖ ≤ radialDerivativeBudget 0 := by
  have hh := absPow_mul_norm_fourier_le_integral_iteratedDerivative (radialWeightSchwartz v1 v2) 0 xi
  have hb := integral_radialWeight_derivative_le h1 h2 0
  have hh' : ‖FourierTransform.fourier (fun r => radialWeight r v1 v2) xi‖ ≤
      ∫ r : ℝ,‖iteratedDeriv 0 (fun r => radialWeight r v1 v2) r‖ := by
    simpa only [pow_zero,one_mul,SchwartzMap.fourier_coe] using! hh
  exact hh'.trans hb

set_option maxHeartbeats 700000 in
/-- The localized absolute bound for each literal frequency triple. -/
theorem norm_sourceIm_le_localized (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ)
    {rho : ℝ} (hrho : 0<rho) (q : ℕ) :
    ‖GuthMaynardEquation55Split.sourceIm N W m1 m2 m3‖ ≤ (N : ℝ)^3 *
      (radialDerivativeBudget 0*localizedRatioMass N W m1 m2 m3 rho +
        (9/4 : ℝ)*radialDerivativeBudget q*(W.card : ℝ)^3/rho^q) := by
  let C0 := radialDerivativeBudget 0
  let D := radialDerivativeBudget q*(W.card : ℝ)^3/rho^q
  let g : ℝ×ℝ → ℝ := fun v => if |affineFrequency N m1 m2 m3 v| ≤ rho then
    ‖radialRatioProduct W v.1 v.2‖ else 0
  have hD : 0≤D := by dsimp [D]; exact div_nonneg (mul_nonneg (radialDerivativeBudget_nonneg q) (by positivity)) (by positivity)
  have hcond : MeasurableSet {v : ℝ×ℝ | |affineFrequency N m1 m2 m3 v| ≤ rho} := by
    apply isClosed_le _ continuous_const |>.measurableSet
    unfold affineFrequency
    fun_prop
  have hg0 : IntegrableOn (fun v : ℝ×ℝ => ‖radialRatioProduct W v.1 v.2‖) ratioBox :=
    (ratioProduct_continuousOn W).norm.integrableOn_compact (μ := volume) (isCompact_Icc.prod isCompact_Icc)
  have hg : IntegrableOn g ratioBox := hg0.indicator hcond
  have hvol : volume ratioBox = ENNReal.ofReal (9/4 : ℝ) := by
    change ((volume : Measure ℝ).prod volume)
      (Set.Icc (1/2 : ℝ) 2 ×ˢ Set.Icc (1/2 : ℝ) 2) = _
    rw [Measure.prod_prod]
    norm_num [Real.volume_Icc]
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3/2)]
    norm_num
  have hvolReal : volume.real ratioBox = (9/4 : ℝ) := by
    change (volume ratioBox).toReal = _
    rw [hvol]
    norm_num
  have hboxMeas : MeasurableSet ratioBox := (isCompact_Icc.prod isCompact_Icc).measurableSet
  have hconst : IntegrableOn (fun _ : ℝ×ℝ => D) ratioBox :=
    integrableOn_const (hs := by rw [hvol]; exact ENNReal.ofReal_ne_top)
  have hmajor : ∀ v ∈ ratioBox,‖innerField N W m1 m2 m3 v‖ ≤ C0*g v+D := by
    intro v hv
    have h1 : |v.1| ≤ 2 := by rw [abs_of_nonneg (by linarith [hv.1.1])]; exact hv.1.2
    have h2 : |v.2| ≤ 2 := by rw [abs_of_nonneg (by linarith [hv.2.1])]; exact hv.2.2
    by_cases hn : |affineFrequency N m1 m2 m3 v| ≤ rho
    · have hh := mul_le_mul_of_nonneg_right (radial_fourier_uniform h1 h2 (affineFrequency N m1 m2 m3 v))
        (norm_nonneg (radialRatioProduct W v.1 v.2))
      unfold innerField
      rw [norm_mul]
      dsimp [g]
      rw [if_pos hn]
      exact hh.trans (le_add_of_nonneg_right hD)
    · have hxi : affineFrequency N m1 m2 m3 v ≠ 0 := by
        intro hz; exact hn (by rw [hz,abs_zero]; exact hrho.le)
      have hh := radialWeight_fourier_decay h1 h2 q hxi
      have hp : rho^q ≤ |affineFrequency N m1 m2 m3 v|^q :=
        pow_le_pow_left₀ hrho.le (le_of_not_ge hn) q
      have hd := div_le_div_of_nonneg_left (radialDerivativeBudget_nonneg q) (pow_pos hrho q) hp
      have hm := mul_le_mul (hh.trans hd) (ratioProduct_norm_le W v)
        (norm_nonneg _) (div_nonneg (radialDerivativeBudget_nonneg q) (by positivity))
      unfold innerField
      rw [norm_mul]
      dsimp [g]
      rw [if_neg hn,mul_zero,zero_add]
      dsimp [D]
      convert hm using 1 <;> ring
  have hf := integrable_innerField N W m1 m2 m3
  have hrestrict : (∫ v : ℝ×ℝ,‖innerField N W m1 m2 m3 v‖) =
      ∫ v : ℝ×ℝ in ratioBox,‖innerField N W m1 m2 m3 v‖ := by
    rw [← integral_indicator (s := ratioBox) hboxMeas]
    apply integral_congr_ae
    filter_upwards with v
    by_cases hv : v∈ratioBox
    · simp [hv]
    · simp [hv,innerField_zero_off_box N W m1 m2 m3 hv]
  have hbound : ‖∫ v : ℝ×ℝ,innerField N W m1 m2 m3 v‖ ≤
      C0*localizedRatioMass N W m1 m2 m3 rho+(9/4 : ℝ)*D := by
    apply (norm_integral_le_integral_norm _).trans
    rw [hrestrict]
    calc
      _ ≤ ∫ v : ℝ×ℝ in ratioBox,C0*g v+D := by
        apply integral_mono_ae hf.norm.integrableOn ((hg.const_mul C0).add hconst)
        filter_upwards [ae_restrict_mem hboxMeas] with v hv
        exact hmajor v hv
      _ = _ := by
        rw [integral_add (hg.const_mul C0) hconst,integral_const_mul,setIntegral_const]
        rw [hvolReal]
        rfl
  rw [GuthMaynardS3LiteralFubini.sourceIm_eq_inner_fourier]
  change ‖(N : ℂ)^3 * ∫ v1 : ℝ,∫ v2 : ℝ,innerField N W m1 m2 m3 (v1,v2)‖ ≤ _
  rw [← integral_prod _ hf,norm_mul,norm_pow,Complex.norm_natCast]
  have hh := mul_le_mul_of_nonneg_left hbound (show 0≤(N : ℝ)^3 by positivity)
  dsimp [C0,D] at hh
  convert hh using 1 <;> ring

end
end GuthMaynardS3LiteralLocalization

#print axioms GuthMaynardS3LiteralLocalization.norm_sourceIm_le_localized
