import RamachandraGammaWeightIntegrability
import GammaCompactStripSharp
import RamachandraShiftedDirectParameters

/-!
# Uniform mass of the Ramachandra Gamma weight

The near contour approaches the pole of `Gamma` at zero.  This file keeps
that dependence explicit: one recurrence costs `|c|⁻¹`, and on the lower
half of `(-1,0)` a second recurrence costs `|1+c|⁻¹`.  In the source
application `c=-1/log X`; the first factor is exactly `log X`, while the
second is uniformly bounded once `X ≥ 3`.
-/

namespace RamachandraGammaWeightUniformMass

open Complex MeasureTheory
open RamachandraGammaWeightIntegrability
open RamachandraShiftedHeadContourTails

noncomputable section

private theorem exp_pi_half_le_exp_one {v : ℝ} :
    Real.exp (-(Real.pi / 2) * |v|) ≤ Real.exp (-|v|) := by
  apply Real.exp_le_exp.mpr
  have hp : 1 ≤ Real.pi / 2 := by
    have := Real.pi_gt_three
    linarith
  nlinarith [abs_nonneg v]

private theorem stripPoint_eq (a v : ℝ) :
    GammaCompactStripScratch.stripPoint a v = (a : ℂ) + (v : ℂ) * I := rfl

/-- Explicit pole-distance envelope throughout the negative unit strip. -/
theorem norm_Gamma_negative_unit_strip_le
    {c v : ℝ} (hcLo : -1 < c) (hcHi : c < 0) :
    ‖Complex.Gamma ((c : ℂ) + (v : ℂ) * I)‖ ≤
      12 * (1 + |v|) * Real.exp (-|v|) *
        (|c|⁻¹ + (|c| * |1 + c|)⁻¹) := by
  let z : ℂ := (c : ℂ) + (v : ℂ) * I
  have hz : z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z] at hre
    linarith
  have hcabs : 0 < |c| := abs_pos.mpr (ne_of_lt hcHi)
  have hnormz : |c| ≤ ‖z‖ := by
    simpa [z, Real.norm_eq_abs] using Complex.abs_re_le_norm z
  by_cases hc : -(1 / 2 : ℝ) ≤ c
  · have hrec := Complex.Gamma_add_one z hz
    have hshift : z + 1 =
        GammaCompactStripScratch.stripPoint (c + 1) v := by
      apply Complex.ext <;> simp [z, GammaCompactStripScratch.stripPoint]
    rw [hshift] at hrec
    have hnum := MAPGammaCompactStripSharp.norm_Gamma_positive_strip_le_exp_pi_half
      (a := c + 1) (t := v) (by linarith) (by linarith)
    have hnum' :
        ‖Complex.Gamma (GammaCompactStripScratch.stripPoint (c + 1) v)‖ ≤
          12 * (1 + |v|) * Real.exp (-|v|) :=
      hnum.trans (mul_le_mul_of_nonneg_left exp_pi_half_le_exp_one (by positivity))
    have hnormrec := congrArg norm hrec
    rw [norm_mul] at hnormrec
    have hdiv : ‖Complex.Gamma z‖ ≤
        12 * (1 + |v|) * Real.exp (-|v|) * |c|⁻¹ := by
      have hprod : |c| * ‖Complex.Gamma z‖ ≤
          12 * (1 + |v|) * Real.exp (-|v|) := by
        calc
          |c| * ‖Complex.Gamma z‖ ≤ ‖z‖ * ‖Complex.Gamma z‖ := by
            gcongr
          _ = ‖Complex.Gamma
              (GammaCompactStripScratch.stripPoint (c + 1) v)‖ := hnormrec.symm
          _ ≤ _ := hnum'
      have hq : ‖Complex.Gamma z‖ ≤
          (12 * (1 + |v|) * Real.exp (-|v|)) / |c| :=
        (le_div_iff₀ hcabs).2 (by simpa [mul_comm] using hprod)
      simpa [div_eq_mul_inv] using hq
    calc
      ‖Complex.Gamma ((c : ℂ) + (v : ℂ) * I)‖ = ‖Complex.Gamma z‖ := rfl
      _ ≤ 12 * (1 + |v|) * Real.exp (-|v|) * |c|⁻¹ := hdiv
      _ ≤ 12 * (1 + |v|) * Real.exp (-|v|) *
          (|c|⁻¹ + (|c| * |1 + c|)⁻¹) := by
        apply mul_le_mul_of_nonneg_left
        · exact le_add_of_nonneg_right (by positivity)
        · positivity
  · have hc' : c < -(1 / 2 : ℝ) := lt_of_not_ge hc
    let z1 : ℂ := z + 1
    have hz1 : z1 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp [z1, z] at hre
      linarith
    have hnormz1 : |1 + c| ≤ ‖z1‖ := by
      have := Complex.abs_re_le_norm z1
      simpa [z1, z, Real.norm_eq_abs, add_comm] using this
    have hc1pos : 0 < |1 + c| := by
      apply abs_pos.mpr
      linarith
    have hrec0 := Complex.Gamma_add_one z hz
    have hrec1 := Complex.Gamma_add_one z1 hz1
    have hshift : z1 + 1 =
        GammaCompactStripScratch.stripPoint (c + 2) v := by
      apply Complex.ext <;> simp [z1, z, GammaCompactStripScratch.stripPoint] <;> ring
    rw [hshift] at hrec1
    have hnum := MAPGammaCompactStripSharp.norm_Gamma_positive_strip_le_exp_pi_half
      (a := c + 2) (t := v) (by linarith) (by linarith)
    have hnum' :
        ‖Complex.Gamma (GammaCompactStripScratch.stripPoint (c + 2) v)‖ ≤
          12 * (1 + |v|) * Real.exp (-|v|) :=
      hnum.trans (mul_le_mul_of_nonneg_left exp_pi_half_le_exp_one (by positivity))
    have hnormrec0 := congrArg norm hrec0
    have hnormrec1 := congrArg norm hrec1
    rw [norm_mul] at hnormrec0 hnormrec1
    have hprod : (|c| * |1 + c|) * ‖Complex.Gamma z‖ ≤
        12 * (1 + |v|) * Real.exp (-|v|) := by
      calc
        (|c| * |1 + c|) * ‖Complex.Gamma z‖ ≤
            (‖z‖ * ‖z1‖) * ‖Complex.Gamma z‖ := by gcongr
        _ = ‖z1‖ * ‖Complex.Gamma z1‖ := by
          rw [hnormrec0]
          ring
        _ = ‖Complex.Gamma
            (GammaCompactStripScratch.stripPoint (c + 2) v)‖ := hnormrec1.symm
        _ ≤ _ := hnum'
    have hden : 0 < |c| * |1 + c| := mul_pos hcabs hc1pos
    have hdiv : ‖Complex.Gamma z‖ ≤
        12 * (1 + |v|) * Real.exp (-|v|) *
          (|c| * |1 + c|)⁻¹ := by
      have hq : ‖Complex.Gamma z‖ ≤
          (12 * (1 + |v|) * Real.exp (-|v|)) /
            (|c| * |1 + c|) :=
        (le_div_iff₀ hden).2
          (by simpa [mul_assoc, mul_comm, mul_left_comm] using hprod)
      simpa [div_eq_mul_inv] using hq
    calc
      ‖Complex.Gamma ((c : ℂ) + (v : ℂ) * I)‖ = ‖Complex.Gamma z‖ := rfl
      _ ≤ 12 * (1 + |v|) * Real.exp (-|v|) *
          (|c| * |1 + c|)⁻¹ := hdiv
      _ ≤ 12 * (1 + |v|) * Real.exp (-|v|) *
          (|c|⁻¹ + (|c| * |1 + c|)⁻¹) := by
        apply mul_le_mul_of_nonneg_left
        · exact le_add_of_nonneg_left (by positivity)
        · positivity

/-- A single absolute integrable mass absorbs the degree-seven envelope. -/
def gammaPolynomialAbsoluteMass : ℝ :=
  ∫ v : ℝ, 12 * ((1 + |v|) ^ 8 * Real.exp (-|v|))

theorem gammaPolynomialAbsoluteMass_nonneg :
    0 ≤ gammaPolynomialAbsoluteMass := by
  unfold gammaPolynomialAbsoluteMass
  exact integral_nonneg (fun v => by positivity)

/-- Uniform full-line mass with the pole distances exposed. -/
theorem integral_gammaPolynomialWeight_le
    {c : ℝ} (hcLo : -1 < c) (hcHi : c < 0) :
    (∫ v : ℝ, gammaPolynomialWeight c v) ≤
      gammaPolynomialAbsoluteMass *
        (|c|⁻¹ + (|c| * |1 + c|)⁻¹) := by
  have hleft := integrable_gammaPolynomialWeight hcLo hcHi
  have hbase : Integrable (fun v : ℝ =>
      12 * ((1 + |v|) ^ 8 * Real.exp (-|v|))) :=
    integrable_one_add_abs_pow_eight_mul_exp_neg_abs.const_mul 12
  have hfac : 0 ≤ |c|⁻¹ + (|c| * |1 + c|)⁻¹ := by positivity
  have hright := hbase.const_mul
    (|c|⁻¹ + (|c| * |1 + c|)⁻¹)
  calc
    (∫ v : ℝ, gammaPolynomialWeight c v) ≤
        ∫ v : ℝ, (|c|⁻¹ + (|c| * |1 + c|)⁻¹) *
          (12 * ((1 + |v|) ^ 8 * Real.exp (-|v|))) := by
      apply integral_mono hleft hright
      intro v
      unfold gammaPolynomialWeight
      have hgamma := norm_Gamma_negative_unit_strip_le hcLo hcHi (v := v)
      calc
        ‖Complex.Gamma ((c : ℂ) + (v : ℂ) * I)‖ * (1 + |v|) ^ 6 ≤
            (12 * (1 + |v|) * Real.exp (-|v|) *
              (|c|⁻¹ + (|c| * |1 + c|)⁻¹)) * (1 + |v|) ^ 6 := by
                gcongr
        _ ≤ (|c|⁻¹ + (|c| * |1 + c|)⁻¹) *
              (12 * ((1 + |v|) ^ 8 * Real.exp (-|v|))) := by
          have hone : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
          have hp : (1 + |v|) ^ 7 ≤ (1 + |v|) ^ 8 := by
            gcongr <;> norm_num
          let A : ℝ := 12 * Real.exp (-|v|) *
            (|c|⁻¹ + (|c| * |1 + c|)⁻¹)
          have hA : 0 ≤ A := by dsimp [A]; positivity
          calc
            (12 * (1 + |v|) * Real.exp (-|v|) *
                (|c|⁻¹ + (|c| * |1 + c|)⁻¹)) * (1 + |v|) ^ 6 =
                A * (1 + |v|) ^ 7 := by dsimp [A]; ring
            _ ≤ A * (1 + |v|) ^ 8 :=
              mul_le_mul_of_nonneg_left hp hA
            _ = (|c|⁻¹ + (|c| * |1 + c|)⁻¹) *
                (12 * ((1 + |v|) ^ 8 * Real.exp (-|v|))) := by
              dsimp [A]
              ring
    _ = gammaPolynomialAbsoluteMass *
        (|c|⁻¹ + (|c| * |1 + c|)⁻¹) := by
      rw [MeasureTheory.integral_const_mul]
      unfold gammaPolynomialAbsoluteMass
      ring

/-! ## The literal near line -/

/-- Fixed positive distance of `1-1/log X` from the neighboring Gamma pole
for every source scale `X ≥ 3`. -/
def shortGammaPoleGap : ℝ := 1 - (Real.log 3)⁻¹

theorem shortGammaPoleGap_pos : 0 < shortGammaPoleGap := by
  have hlog : 1 < Real.log 3 :=
    RamachandraShiftedDirectParameters.one_lt_log_of_three_le (by norm_num)
  unfold shortGammaPoleGap
  have hinv : (Real.log 3)⁻¹ < 1 := by
    simpa using (inv_lt_one₀ (by linarith)).2 hlog
  linarith

/-- The two pole-distance factors on `c=-1/log X` cost only one logarithm. -/
theorem shortPoleDistanceFactor_le_log
    {X : ℝ} (hX : 3 ≤ X) :
    |-(Real.log X)⁻¹|⁻¹ +
        (|-(Real.log X)⁻¹| * |1 - (Real.log X)⁻¹|)⁻¹ ≤
      (1 + shortGammaPoleGap⁻¹) * Real.log X := by
  let L : ℝ := Real.log X
  let k : ℝ := shortGammaPoleGap
  have hL : 1 < L := by
    dsimp [L]
    exact RamachandraShiftedDirectParameters.one_lt_log_of_three_le hX
  have hL0 : 0 < L := lt_trans (by norm_num) hL
  have hk : 0 < k := by exact shortGammaPoleGap_pos
  have hlog3 : 0 < Real.log 3 := by
    have := RamachandraShiftedDirectParameters.one_lt_log_of_three_le
      (show (3 : ℝ) ≤ 3 by norm_num)
    linarith
  have hlogMono : Real.log 3 ≤ L := by
    dsimp [L]
    exact Real.strictMonoOn_log.monotoneOn (by norm_num)
      (lt_of_lt_of_le (by norm_num) hX) hX
  have hinv : L⁻¹ ≤ (Real.log 3)⁻¹ :=
    (inv_le_inv₀ hL0 hlog3).2 hlogMono
  have hgap : k ≤ 1 - L⁻¹ := by
    dsimp [k, shortGammaPoleGap]
    linarith
  have hgapPos : 0 < 1 - L⁻¹ := lt_of_lt_of_le hk hgap
  have habsL : |-L⁻¹| = L⁻¹ := by
    rw [abs_neg, abs_of_pos (inv_pos.mpr hL0)]
  have habsGap : |1 - L⁻¹| = 1 - L⁻¹ := abs_of_pos hgapPos
  have hfirst : |-L⁻¹|⁻¹ = L := by
    rw [habsL, inv_inv]
  have hsecond : (|-L⁻¹| * |1 - L⁻¹|)⁻¹ ≤ L * k⁻¹ := by
    rw [habsL, habsGap, mul_inv, inv_inv]
    exact mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ hgapPos hk).2 hgap) hL0.le
  change |-L⁻¹|⁻¹ + (|-L⁻¹| * |1 - L⁻¹|)⁻¹ ≤
    (1 + k⁻¹) * L
  rw [hfirst]
  calc
    L + (|-L⁻¹| * |1 - L⁻¹|)⁻¹ ≤ L + L * k⁻¹ :=
      add_le_add_right hsecond L
    _ = (1 + k⁻¹) * L := by ring

/-- Uniform near-line Gamma mass in the exact source scale. -/
theorem integral_gammaPolynomialWeight_short_le_log
    {X : ℝ} (hX : 3 ≤ X) :
    (∫ v : ℝ, gammaPolynomialWeight (-(Real.log X)⁻¹) v) ≤
      gammaPolynomialAbsoluteMass *
        (1 + shortGammaPoleGap⁻¹) * Real.log X := by
  have hL := RamachandraShiftedDirectParameters.one_lt_log_of_three_le hX
  have hcLo : -1 < -(Real.log X)⁻¹ := by
    have hi : (Real.log X)⁻¹ < 1 := by
      simpa using (inv_lt_one₀ (by linarith)).2 hL
    linarith
  have hcHi : -(Real.log X)⁻¹ < 0 := by
    have : 0 < (Real.log X)⁻¹ := inv_pos.mpr (by linarith)
    linarith
  have hmass := integral_gammaPolynomialWeight_le hcLo hcHi
  have hpole := shortPoleDistanceFactor_le_log hX
  calc
    (∫ v : ℝ, gammaPolynomialWeight (-(Real.log X)⁻¹) v) ≤
        gammaPolynomialAbsoluteMass *
          (|-(Real.log X)⁻¹|⁻¹ +
            (|-(Real.log X)⁻¹| * |1 - (Real.log X)⁻¹|)⁻¹) := by
      simpa [sub_eq_add_neg] using hmass
    _ ≤ gammaPolynomialAbsoluteMass *
        ((1 + shortGammaPoleGap⁻¹) * Real.log X) :=
      mul_le_mul_of_nonneg_left hpole gammaPolynomialAbsoluteMass_nonneg
    _ = gammaPolynomialAbsoluteMass *
        (1 + shortGammaPoleGap⁻¹) * Real.log X := by ring

end
end RamachandraGammaWeightUniformMass

#print axioms RamachandraGammaWeightUniformMass.norm_Gamma_negative_unit_strip_le
#print axioms RamachandraGammaWeightUniformMass.integral_gammaPolynomialWeight_le
#print axioms RamachandraGammaWeightUniformMass.integral_gammaPolynomialWeight_short_le_log
