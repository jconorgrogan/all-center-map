import RamachandraGammaWeightIntegrability
import JutilaLemma6GammaKernel
import RamachandraShiftedDirectParameters

/-!
# Uniform full-line Gamma mass on Ramachandra's long contour

Pointwise integrability at each real part is insufficient for the source
theorem: its constant must be uniform in the shifted strip.  This module
keeps the long line a fixed distance from the neighboring Gamma poles and
dominates its complete Mellin weight by one universal integrable function.
-/

namespace RamachandraLongGammaUniformMass

open Complex MeasureTheory
open RamachandraGammaWeightIntegrability
open MAPJutilaLemma6GammaKernel
open RamachandraTheorem6ShiftedStripSource

noncomputable section

set_option maxHeartbeats 800000

/-- Uniform fourth-order Gamma envelope when the long-line displacement
`beta=sigma+1/4` stays in `[7/10,4/5]`. -/
theorem norm_Gamma_longLine_le_invSq
    {sigma v : ℝ}
    (hbetaLo : 7 / 10 ≤ sigma + 1 / 4)
    (hbetaHi : sigma + 1 / 4 ≤ 4 / 5) :
    ‖Complex.Gamma ((-(sigma + 1 / 4) : ℝ) + (v : ℂ) * I)‖ ≤
      72 * (1 + v ^ 2)⁻¹ ^ 2 := by
  let beta : ℝ := sigma + 1 / 4
  let a : ℝ := -beta
  have hbetaPos : 0 < beta := by dsimp [beta]; linarith
  have hbetaOne : beta < 1 := by dsimp [beta]; linarith
  have haLo : -1 < a := by dsimp [a]; linarith
  have haHi : a < 0 := by dsimp [a]; linarith
  have hraw := norm_Gamma_minus_one_zero_vertical_le_inv_sq
    (a := a) (t := v) haLo haHi
  let c : ℝ := (-a) * (a + 1)
  have hcPos : 0 < c := by
    dsimp [c, a, beta]
    exact mul_pos (by linarith) (by linarith)
  have hcLower : (7 / 50 : ℝ) ≤ c := by
    dsimp [c, a, beta]
    have hright : (1 / 5 : ℝ) ≤ 1 - (sigma + 1 / 4) := by linarith
    nlinarith [mul_le_mul hbetaLo hright (by norm_num : (0 : ℝ) ≤ 1 / 5)
      (by linarith : 0 ≤ sigma + 1 / 4)]
  have hcInv : c⁻¹ ≤ 8 := by
    have hbase : (0 : ℝ) < 7 / 50 := by norm_num
    have hinv : c⁻¹ ≤ (7 / 50 : ℝ)⁻¹ :=
      (inv_le_inv₀ hcPos hbase).2 hcLower
    exact hinv.trans (by norm_num)
  have ha2pos : 0 < a + 2 := by linarith
  have ha2one : 1 ≤ a + 2 := by dsimp [a, beta]; linarith
  have ha3mem : a + 3 ∈ Set.Ici (2 : ℝ) := by
    simp only [Set.mem_Ici]
    linarith
  have hthreeMem : (3 : ℝ) ∈ Set.Ici (2 : ℝ) := by norm_num
  have hGa3 : Real.Gamma (a + 3) ≤ Real.Gamma 3 :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn ha3mem hthreeMem (by linarith)
  have hGa2 : Real.Gamma (a + 2) ≤ 2 := by
    calc
      Real.Gamma (a + 2) ≤ (a + 2) * Real.Gamma (a + 2) :=
        (le_mul_iff_one_le_left (Real.Gamma_pos_of_pos ha2pos)).2 ha2one
      _ = Real.Gamma (a + 3) := by
        rw [show a + 3 = (a + 2) + 1 by ring,
          Real.Gamma_add_one (ne_of_gt ha2pos)]
      _ ≤ Real.Gamma 3 := hGa3
      _ = 2 := by norm_num [Real.Gamma_ofNat_eq_factorial]
  have ha4mem : a + 4 ∈ Set.Ici (2 : ℝ) := by
    simp only [Set.mem_Ici]
    linarith
  have hfourMem : (4 : ℝ) ∈ Set.Ici (2 : ℝ) := by norm_num
  have hGa4 : Real.Gamma (a + 4) ≤ 6 := by
    calc
      Real.Gamma (a + 4) ≤ Real.Gamma 4 :=
        Real.Gamma_strictMonoOn_Ici.monotoneOn ha4mem hfourMem (by linarith)
      _ = 6 := by norm_num [Real.Gamma_ofNat_eq_factorial]
  have hsum0 : 0 ≤ Real.Gamma (a + 2) + Real.Gamma (a + 4) :=
    add_nonneg (Real.Gamma_pos_of_pos ha2pos).le
      (Real.Gamma_pos_of_pos (by linarith)).le
  have hconstant :
      (1 + c⁻¹) * (Real.Gamma (a + 2) + Real.Gamma (a + 4)) ≤ 72 := by
    calc
      (1 + c⁻¹) * (Real.Gamma (a + 2) + Real.Gamma (a + 4)) ≤
          9 * 8 := by
        gcongr <;> linarith
      _ = 72 := by norm_num
  change ‖Complex.Gamma ((a : ℝ) + (v : ℂ) * I)‖ ≤ _
  exact hraw.trans (mul_le_mul_of_nonneg_right hconstant (by positivity))

/-- The literal Theorem-6 strip places the long displacement in the compact
pole-free interval used above. -/
theorem longBeta_mem_uniformInterval
    {q : ℕ} [NeZero q] {T sigma : ℝ} (hT : 3 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹) :
    7 / 10 ≤ sigma + 1 / 4 ∧ sigma + 1 / 4 ≤ 4 / 5 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hR : 3 ≤ (q : ℝ) * T := by nlinarith
  have hlog : 1 < Real.log ((q : ℝ) * T) :=
    RamachandraShiftedDirectParameters.one_lt_log_of_three_le hR
  have hden : (100 : ℝ) < 100 * Real.log ((q : ℝ) * T) := by nlinarith
  have hinv : (100 * Real.log ((q : ℝ) * T))⁻¹ < (1 / 100 : ℝ) := by
    simpa [one_div] using
      (inv_lt_inv₀ (by positivity : (0 : ℝ) < 100 * Real.log ((q : ℝ) * T))
        (by norm_num : (0 : ℝ) < 100)).2 hden
  have habs : |sigma - (1 / 2 : ℝ)| < 1 / 100 := hstrip.trans_lt hinv
  constructor <;> rcases abs_lt.mp habs with ⟨hlo, hhi⟩ <;> linarith

/-- One universal integrable majorant for every long-line Gamma weight. -/
def longGammaWeightEnvelope (v : ℝ) : ℝ :=
  9216 * (1 + v ^ 2)⁻¹ +
    12 * ((1 + |v|) ^ 8 * Real.exp (-|v|))

theorem integrable_longGammaWeightEnvelope :
    Integrable longGammaWeightEnvelope := by
  exact (integrable_inv_one_add_sq.const_mul 9216).add
    (RamachandraShiftedHeadContourTails.integrable_one_add_abs_pow_eight_mul_exp_neg_abs.const_mul 12)

theorem gammaPolynomialWeight_long_le_envelope
    {q : ℕ} [NeZero q] {T sigma : ℝ} (hT : 3 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹)
    (v : ℝ) :
    gammaPolynomialWeight (-(sigma + 1 / 4)) v ≤
      longGammaWeightEnvelope v := by
  obtain ⟨hbetaLo, hbetaHi⟩ := longBeta_mem_uniformInterval hT hstrip
  by_cases hv : |v| ≤ 1
  · have hGamma := norm_Gamma_longLine_le_invSq
      (sigma := sigma) (v := v) hbetaLo hbetaHi
    have hpoly : (1 + |v|) ^ 6 ≤ (2 : ℝ) ^ 6 := by
      gcongr
      linarith
    have hinv : (1 / 2 : ℝ) ≤ (1 + v ^ 2)⁻¹ := by
      have hden : 1 + v ^ 2 ≤ (2 : ℝ) := by
        rcases abs_le.mp hv with ⟨hvLo, hvHi⟩
        nlinarith [sq_nonneg (v - 1), sq_nonneg (v + 1)]
      apply (le_inv_comm₀ (by norm_num) (by positivity)).2
      norm_num
      exact hden
    unfold gammaPolynomialWeight longGammaWeightEnvelope
    have hweight :
        ‖Complex.Gamma ((-(sigma + 1 / 4) : ℝ) + (v : ℂ) * I)‖ *
            (1 + |v|) ^ 6 ≤ 4608 := by
      calc
        _ ≤ (72 * (1 + v ^ 2)⁻¹ ^ 2) * (2 : ℝ) ^ 6 := by gcongr
        _ ≤ 72 * 1 ^ 2 * (2 : ℝ) ^ 6 := by
          have hi1 : (1 + v ^ 2)⁻¹ ≤ 1 :=
            inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg v])
          gcongr
        _ = 4608 := by norm_num
    have hfirst : 4608 ≤ 9216 * (1 + v ^ 2)⁻¹ := by nlinarith
    exact hweight.trans (hfirst.trans (le_add_of_nonneg_right (by positivity)))
  · have hv1 : 1 ≤ |v| := le_of_not_ge hv
    have hgamma :=
      RamachandraShiftedGammaPoleContour.norm_Gamma_ramachandraHorizontalStrip_le_exp
        (a := -(sigma + 1 / 4)) (t := v)
          (by linarith [hbetaHi]) (by linarith [hbetaLo]) hv1
    unfold gammaPolynomialWeight longGammaWeightEnvelope
    have htail :
        ‖Complex.Gamma ((-(sigma + 1 / 4) : ℝ) + (v : ℂ) * I)‖ *
            (1 + |v|) ^ 6 ≤
          12 * ((1 + |v|) ^ 8 * Real.exp (-|v|)) := by
      calc
        _ ≤ (12 * (1 + |v|) ^ 2 * Real.exp (-|v|)) *
            (1 + |v|) ^ 6 := mul_le_mul_of_nonneg_right hgamma (by positivity)
        _ = 12 * ((1 + |v|) ^ 8 * Real.exp (-|v|)) := by ring
    exact htail.trans (le_add_of_nonneg_left (by positivity))

/-- The full long-line Gamma mass is bounded by one source-independent real
constant. -/
theorem integral_gammaPolynomialWeight_long_le_uniformMass
    {q : ℕ} [NeZero q] {T sigma : ℝ} (hT : 3 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹) :
    (∫ v, gammaPolynomialWeight (-(sigma + 1 / 4)) v) ≤
      ∫ v, longGammaWeightEnvelope v := by
  obtain ⟨hbetaLo, hbetaHi⟩ := longBeta_mem_uniformInterval hT hstrip
  apply integral_mono
  · exact integrable_gammaPolynomialWeight
      (by linarith [hbetaHi]) (by linarith [hbetaLo])
  · exact integrable_longGammaWeightEnvelope
  · exact gammaPolynomialWeight_long_le_envelope hT hstrip

end
end RamachandraLongGammaUniformMass

#print axioms RamachandraLongGammaUniformMass.norm_Gamma_longLine_le_invSq
#print axioms RamachandraLongGammaUniformMass.integral_gammaPolynomialWeight_long_le_uniformMass
