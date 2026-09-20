import RamachandraGammaWeightIntegrability
import JutilaLemma6GammaKernel
import MertensAnalyticLeaf

/-!
# Explicit logarithmic Gamma mass on Ramachandra's short contour

The short line has real part `-1/log X` and approaches the Gamma pole at
zero.  Its full-line Mellin mass is therefore not uniformly bounded; the
correct cost is one explicit factor of `log X`.  This module certifies that
cost and nothing stronger.
-/

namespace RamachandraShortGammaPolylogMass

open Complex MeasureTheory
open RamachandraGammaWeightIntegrability
open MAPJutilaLemma6GammaKernel

noncomputable section

set_option maxHeartbeats 800000

theorem exp_sixFifths_lt_six : Real.exp (6 / 5 : ℝ) < 6 := by
  have he1 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have heFifth : Real.exp (1 / 5 : ℝ) ≤ 5 / 4 := by
    have h := MAPMertensAnalyticLeaf.exp_le_inv_one_sub
      (u := (1 / 5 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  rw [show (6 / 5 : ℝ) = 1 + 1 / 5 by norm_num, Real.exp_add]
  calc
    Real.exp 1 * Real.exp (1 / 5 : ℝ) < 3 * (5 / 4 : ℝ) :=
      mul_lt_mul he1 heFifth (Real.exp_pos _) (by norm_num)
    _ < 6 := by norm_num

theorem sixFifths_le_log_of_six_le {X : ℝ} (hX : 6 ≤ X) :
    6 / 5 ≤ Real.log X := by
  have hlog6 : (6 / 5 : ℝ) < Real.log 6 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 exp_sixFifths_lt_six
  have hXpos : 0 < X := by linarith
  have hmono : Real.log 6 ≤ Real.log X :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hXpos hX
  exact hlog6.le.trans hmono

/-- The short-line Gamma pole contributes at most one factor `log X`. -/
theorem norm_Gamma_shortLine_le_log_mul_invSq
    {X v : ℝ} (hX : 6 ≤ X) :
    ‖Complex.Gamma ((-(Real.log X)⁻¹ : ℝ) + (v : ℂ) * I)‖ ≤
      56 * Real.log X * (1 + v ^ 2)⁻¹ ^ 2 := by
  let L : ℝ := Real.log X
  let delta : ℝ := L⁻¹
  let a : ℝ := -delta
  have hL : 6 / 5 ≤ L := sixFifths_le_log_of_six_le hX
  have hLpos : 0 < L := by linarith
  have hdeltaPos : 0 < delta := by dsimp [delta]; positivity
  have hdeltaHi : delta ≤ 5 / 6 := by
    dsimp [delta]
    have := (inv_le_inv₀ hLpos (by norm_num : (0 : ℝ) < 6 / 5)).2 hL
    norm_num at this ⊢
    exact this
  have haLo : -1 < a := by dsimp [a]; linarith
  have haHi : a < 0 := by dsimp [a]; linarith
  have hraw := norm_Gamma_minus_one_zero_vertical_le_inv_sq
    (a := a) (t := v) haLo haHi
  let c : ℝ := (-a) * (a + 1)
  have hcPos : 0 < c := by
    dsimp [c, a, delta]
    apply mul_pos
    · simpa using (inv_pos.mpr hLpos)
    · have hi : L⁻¹ ≤ 5 / 6 := by simpa [delta] using hdeltaHi
      linarith
  have hcLower : (6 * L)⁻¹ ≤ c := by
    have hright : (1 / 6 : ℝ) ≤ 1 - delta := by linarith
    have hdeltaEq : delta = L⁻¹ := rfl
    dsimp [c, a]
    rw [hdeltaEq]
    have hLne : L ≠ 0 := hLpos.ne'
    calc
      (6 * L)⁻¹ = L⁻¹ * (1 / 6 : ℝ) := by field_simp
      _ ≤ L⁻¹ * (1 - L⁻¹) :=
        mul_le_mul_of_nonneg_left hright (inv_nonneg.mpr hLpos.le)
      _ = - -L⁻¹ * (-L⁻¹ + 1) := by ring
  have hcInv : c⁻¹ ≤ 6 * L := by
    have hbase : 0 < (6 * L)⁻¹ := by positivity
    have hinv : c⁻¹ ≤ ((6 * L)⁻¹)⁻¹ :=
      (inv_le_inv₀ hcPos hbase).2 hcLower
    simpa [hLpos.ne'] using hinv
  have ha2pos : 0 < a + 2 := by linarith
  have ha2one : 1 ≤ a + 2 := by dsimp [a]; linarith
  have ha3mem : a + 3 ∈ Set.Ici (2 : ℝ) := by simp; linarith
  have hGa3 : Real.Gamma (a + 3) ≤ Real.Gamma 3 :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn ha3mem
      (by norm_num : (3 : ℝ) ∈ Set.Ici 2) (by linarith)
  have hGa2 : Real.Gamma (a + 2) ≤ 2 := by
    calc
      Real.Gamma (a + 2) ≤ (a + 2) * Real.Gamma (a + 2) :=
        (le_mul_iff_one_le_left (Real.Gamma_pos_of_pos ha2pos)).2 ha2one
      _ = Real.Gamma (a + 3) := by
        rw [show a + 3 = (a + 2) + 1 by ring,
          Real.Gamma_add_one (ne_of_gt ha2pos)]
      _ ≤ Real.Gamma 3 := hGa3
      _ = 2 := by norm_num [Real.Gamma_ofNat_eq_factorial]
  have ha4mem : a + 4 ∈ Set.Ici (2 : ℝ) := by simp; linarith
  have hGa4 : Real.Gamma (a + 4) ≤ 6 := by
    calc
      Real.Gamma (a + 4) ≤ Real.Gamma 4 :=
        Real.Gamma_strictMonoOn_Ici.monotoneOn ha4mem
          (by norm_num : (4 : ℝ) ∈ Set.Ici 2) (by linarith)
      _ = 6 := by norm_num [Real.Gamma_ofNat_eq_factorial]
  have hsum0 : 0 ≤ Real.Gamma (a + 2) + Real.Gamma (a + 4) :=
    add_nonneg (Real.Gamma_pos_of_pos ha2pos).le
      (Real.Gamma_pos_of_pos (by linarith)).le
  have hconstant :
      (1 + c⁻¹) * (Real.Gamma (a + 2) + Real.Gamma (a + 4)) ≤
        56 * L := by
    calc
      _ ≤ (1 + 6 * L) * 8 := by gcongr <;> linarith
      _ ≤ 56 * L := by nlinarith
  change ‖Complex.Gamma ((a : ℝ) + (v : ℂ) * I)‖ ≤ _
  exact hraw.trans (mul_le_mul_of_nonneg_right hconstant (by positivity))

def shortGammaWeightEnvelope (v : ℝ) : ℝ :=
  7168 * (1 + v ^ 2)⁻¹ +
    12 * ((1 + |v|) ^ 8 * Real.exp (-|v|))

theorem integrable_shortGammaWeightEnvelope :
    Integrable shortGammaWeightEnvelope := by
  exact (integrable_inv_one_add_sq.const_mul 7168).add
    (RamachandraShiftedHeadContourTails.integrable_one_add_abs_pow_eight_mul_exp_neg_abs.const_mul 12)

theorem gammaPolynomialWeight_short_le_log_mul_envelope
    {X : ℝ} (hX : 6 ≤ X) (v : ℝ) :
    gammaPolynomialWeight (-(Real.log X)⁻¹) v ≤
      Real.log X * shortGammaWeightEnvelope v := by
  have hL : 1 ≤ Real.log X :=
    (by linarith [sixFifths_le_log_of_six_le hX] : 1 ≤ Real.log X)
  by_cases hv : |v| ≤ 1
  · have hGamma := norm_Gamma_shortLine_le_log_mul_invSq (X := X) (v := v) hX
    have hpoly : (1 + |v|) ^ 6 ≤ (2 : ℝ) ^ 6 := by gcongr; linarith
    have hden : 1 + v ^ 2 ≤ (2 : ℝ) := by
      rcases abs_le.mp hv with ⟨hvLo, hvHi⟩
      nlinarith [sq_nonneg (v - 1), sq_nonneg (v + 1)]
    have hinv : (1 / 2 : ℝ) ≤ (1 + v ^ 2)⁻¹ := by
      apply (le_inv_comm₀ (by norm_num) (by positivity)).2
      norm_num
      exact hden
    unfold gammaPolynomialWeight shortGammaWeightEnvelope
    have hweight :
        ‖Complex.Gamma ((-(Real.log X)⁻¹ : ℝ) + (v : ℂ) * I)‖ *
            (1 + |v|) ^ 6 ≤ 3584 * Real.log X := by
      calc
        _ ≤ (56 * Real.log X * (1 + v ^ 2)⁻¹ ^ 2) * 2 ^ 6 := by gcongr
        _ ≤ (56 * Real.log X * 1 ^ 2) * 2 ^ 6 := by
          have hi1 : (1 + v ^ 2)⁻¹ ≤ 1 :=
            inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg v])
          gcongr
        _ = 3584 * Real.log X := by ring
    have hfirst : 3584 * Real.log X ≤
        Real.log X * (7168 * (1 + v ^ 2)⁻¹) := by
      nlinarith
    calc
      _ ≤ 3584 * Real.log X := hweight
      _ ≤ Real.log X * (7168 * (1 + v ^ 2)⁻¹) := hfirst
      _ ≤ Real.log X * (7168 * (1 + v ^ 2)⁻¹ +
          12 * ((1 + |v|) ^ 8 * Real.exp (-|v|))) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (by positivity)) (by linarith)
  · have hv1 : 1 ≤ |v| := le_of_not_ge hv
    have hdelta := sixFifths_le_log_of_six_le hX
    have hgamma :=
      RamachandraShiftedGammaPoleContour.norm_Gamma_ramachandraHorizontalStrip_le_exp
        (a := -(Real.log X)⁻¹) (t := v)
          (by
            have hi : (Real.log X)⁻¹ ≤ 5 / 6 :=
              by
                have hiRaw :=
                  (inv_le_inv₀ (by linarith : 0 < Real.log X)
                    (by norm_num : (0 : ℝ) < 6 / 5)).2 hdelta
                norm_num at hiRaw ⊢
                exact hiRaw
            linarith)
          (by
            have hi : 0 < (Real.log X)⁻¹ := by positivity
            linarith) hv1
    unfold gammaPolynomialWeight shortGammaWeightEnvelope
    have htail :
        ‖Complex.Gamma ((-(Real.log X)⁻¹ : ℝ) + (v : ℂ) * I)‖ *
            (1 + |v|) ^ 6 ≤
          12 * ((1 + |v|) ^ 8 * Real.exp (-|v|)) := by
      calc
        _ ≤ (12 * (1 + |v|) ^ 2 * Real.exp (-|v|)) *
            (1 + |v|) ^ 6 := mul_le_mul_of_nonneg_right hgamma (by positivity)
        _ = 12 * ((1 + |v|) ^ 8 * Real.exp (-|v|)) := by ring
    calc
      _ ≤ 12 * ((1 + |v|) ^ 8 * Real.exp (-|v|)) := htail
      _ ≤ Real.log X *
          (12 * ((1 + |v|) ^ 8 * Real.exp (-|v|))) := by
        exact le_mul_of_one_le_left (by positivity) hL
      _ ≤ Real.log X * (7168 * (1 + v ^ 2)⁻¹ +
          12 * ((1 + |v|) ^ 8 * Real.exp (-|v|))) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (by positivity)) (by linarith)

theorem integral_gammaPolynomialWeight_short_le_polylogMass
    {X : ℝ} (hX : 6 ≤ X) :
    (∫ v, gammaPolynomialWeight (-(Real.log X)⁻¹) v) ≤
      Real.log X * ∫ v, shortGammaWeightEnvelope v := by
  have hLpos : 0 < Real.log X := by linarith [sixFifths_le_log_of_six_le hX]
  rw [← MeasureTheory.integral_const_mul]
  apply integral_mono
  · exact integrable_gammaPolynomialWeight
      (by
        have hi : (Real.log X)⁻¹ < 1 := by
          exact (inv_lt_one₀ hLpos).2
            (by linarith [sixFifths_le_log_of_six_le hX])
        linarith)
      (by
        have hi : 0 < (Real.log X)⁻¹ := by positivity
        linarith)
  · exact integrable_shortGammaWeightEnvelope.const_mul _
  · exact gammaPolynomialWeight_short_le_log_mul_envelope hX

end
end RamachandraShortGammaPolylogMass

#print axioms RamachandraShortGammaPolylogMass.norm_Gamma_shortLine_le_log_mul_invSq
#print axioms RamachandraShortGammaPolylogMass.integral_gammaPolynomialWeight_short_le_polylogMass
