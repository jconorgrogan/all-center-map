import RamachandraShiftedDirectParameters
import KhaleAppendixBZetaPointwiseCertified

/-!
# Explicit tail absorption for the canonical Ramachandra cutoff

At `M = ceil(X (log X)^16)`, the geometric tail from the literal smoothed
series is polylogarithmic.  These are deterministic real inequalities only.
-/

namespace RamachandraShiftedDirectTailAbsorption

open RamachandraShiftedDirectSeries
open RamachandraShiftedDirectFullBudget
open RamachandraShiftedDirectParameters
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedDirectAssembly
open MRTLemma215DyadicPartition

noncomputable section

private theorem log_three_gt_109_div_100 :
    (109 / 100 : ℝ) < Real.log 3 := by
  have hmul : Real.log (2 * (3 / 2 : ℝ)) =
      Real.log 2 + Real.log (3 / 2 : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  norm_num at hmul
  rw [hmul]
  nlinarith [Real.log_two_gt_d9,
    MAPKhaleAppendixBZetaPointwiseCertified.log_three_halves_lower]

theorem log_lower_109_div_100 {X : ℝ} (hX : 3 ≤ X) :
    (109 / 100 : ℝ) ≤ Real.log X := by
  exact log_three_gt_109_div_100.le.trans
    (Real.log_le_log (by norm_num) hX)

theorem three_mul_log_le_log_pow_sixteen
    {X : ℝ} (hX : 3 ≤ X) :
    3 * Real.log X ≤ Real.log X ^ 16 := by
  let y := Real.log X
  have hy : (109 / 100 : ℝ) ≤ y := log_lower_109_div_100 hX
  have hy0 : 0 ≤ y := by linarith
  have hp : (109 / 100 : ℝ) ^ 15 ≤ y ^ 15 :=
    pow_le_pow_left₀ (by norm_num) hy 15
  have hthree : (3 : ℝ) ≤ y ^ 15 := by
    norm_num at hp ⊢
    linarith
  dsimp [y] at hthree ⊢
  calc
    3 * Real.log X ≤ Real.log X ^ 15 * Real.log X := by
      exact mul_le_mul_of_nonneg_right hthree hy0
    _ = Real.log X ^ 16 := by ring

/-- Elementary lower bound for the denominator of the geometric tail. -/
theorem one_div_two_mul_le_one_sub_exp_neg_one_div
    {X : ℝ} (hX : 3 ≤ X) :
    1 / (2 * X) ≤ 1 - Real.exp (-(1 / X)) := by
  have hX0 : 0 < X := by linarith
  have ha0 : 0 < 1 / X := one_div_pos.mpr hX0
  have hexp := Real.add_one_le_exp (1 / X)
  have hinv : (Real.exp (1 / X))⁻¹ ≤ (1 / X + 1)⁻¹ :=
    inv_anti₀ (by positivity) hexp
  rw [← Real.exp_neg] at hinv
  have hform : (1 / X + 1)⁻¹ = X / (X + 1) := by
    field_simp
    ring
  rw [hform] at hinv
  have hfirst : 1 / (X + 1) ≤ 1 - Real.exp (-(1 / X)) := by
    rw [le_sub_iff_add_le]
    calc
      1 / (X + 1) + Real.exp (-(1 / X)) ≤
          1 / (X + 1) + X / (X + 1) := add_le_add_right hinv _
      _ = 1 := by field_simp; ring
  have hden : X + 1 ≤ 2 * X := by linarith
  have hsmall : 1 / (2 * X) ≤ 1 / (X + 1) :=
    one_div_le_one_div_of_le (by positivity) hden
  exact hsmall.trans hfirst

/-- The canonical cutoff supplies at least three logarithmic units in the
exponential tail. -/
theorem canonical_geometric_power_le_inv_cube
    {X : ℝ} (hX : 3 ≤ X) :
    (Real.exp (-(1 / X))) ^ (directTruncation X + 1) ≤
      (X⁻¹) ^ 3 := by
  let M := directTruncation X
  let y := Real.log X
  have hX0 : 0 < X := by linarith
  have hlog : 3 * y ≤ y ^ 16 := by
    simpa [y] using three_mul_log_le_log_pow_sixteen hX
  have hM : X * y ^ 16 ≤ (M : ℝ) := by
    simpa [M, y] using directTruncation_lower (X := X)
  have hratio : 3 * y ≤ ((M + 1 : ℕ) : ℝ) / X := by
    have hmul : X * (3 * y) ≤ (M : ℝ) :=
      (mul_le_mul_of_nonneg_left hlog hX0.le).trans hM
    have hMsucc : (M : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by norm_num
    apply (le_div_iff₀ hX0).2
    nlinarith
  rw [← exp_neg_nat_div_eq_pow (X := X) (M + 1)]
  have hexp : Real.exp (-(((M + 1 : ℕ) : ℝ) / X)) ≤
      Real.exp (-(3 * y)) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    Real.exp (-(((M + 1 : ℕ) : ℝ) / X)) ≤
        Real.exp (-(3 * y)) := hexp
    _ = (X⁻¹) ^ 3 := by
      rw [Real.exp_neg]
      rw [show (3 : ℝ) * y = (3 : ℕ) * y by norm_num,
        Real.exp_nat_mul, Real.exp_log hX0, inv_pow]

/-- The inverse first-order geometric denominator costs at most `2X`. -/
theorem inv_one_sub_exp_neg_one_div_le
    {X : ℝ} (hX : 3 ≤ X) :
    (1 - Real.exp (-(1 / X)))⁻¹ ≤ 2 * X := by
  have hlower := one_div_two_mul_le_one_sub_exp_neg_one_div hX
  have hbase : 0 < 1 / (2 * X) := by positivity
  have hinv := inv_anti₀ hbase hlower
  simpa [one_div] using hinv

/-- The complete parenthesized geometric factor is at most `6X²`. -/
theorem geometric_tail_parenthesis_le
    {X : ℝ} (hX : 3 ≤ X) :
    Real.exp (-(1 / X)) /
        (1 - Real.exp (-(1 / X))) ^ 2 +
      (1 - Real.exp (-(1 / X)))⁻¹ ≤ 6 * X ^ 2 := by
  have hX0 : 0 < X := by linarith
  let D := 1 - Real.exp (-(1 / X))
  have hDinv : D⁻¹ ≤ 2 * X := by
    simpa [D] using inv_one_sub_exp_neg_one_div_le hX
  have hDinv0 : 0 ≤ D⁻¹ := by
    have hD : 0 < D :=
      (one_div_two_mul_le_one_sub_exp_neg_one_div hX).trans_lt' (by positivity)
    positivity
  have hr : Real.exp (-(1 / X)) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (one_div_nonneg.mpr hX0.le))
  have hsq : D⁻¹ ^ 2 ≤ (2 * X) ^ 2 :=
    pow_le_pow_left₀ hDinv0 hDinv 2
  have hfirst : Real.exp (-(1 / X)) / D ^ 2 ≤ 4 * X ^ 2 := by
    rw [div_eq_mul_inv, ← inv_pow]
    calc
      Real.exp (-(1 / X)) * D⁻¹ ^ 2 ≤ 1 * D⁻¹ ^ 2 := by
        gcongr
      _ ≤ 1 * (2 * X) ^ 2 := by gcongr
      _ = 4 * X ^ 2 := by ring
  calc
    Real.exp (-(1 / X)) / D ^ 2 + D⁻¹ ≤
        4 * X ^ 2 + 2 * X := add_le_add hfirst hDinv
    _ ≤ 6 * X ^ 2 := by nlinarith [sq_nonneg (X - 1)]

/-- The full explicit tail envelope is only polylogarithmic at the canonical
cutoff. -/
theorem canonical_shiftedDirectTailEnvelope_le
    {X : ℝ} (hX : 3 ≤ X) :
    shiftedDirectTailEnvelope (directTruncation X) X ≤
      10 * Real.log X ^ 16 := by
  let M := directTruncation X
  let y := Real.log X
  let r := Real.exp (-(1 / X))
  have hX0 : 0 < X := by linarith
  have hy : 1 ≤ y := (one_lt_log_of_three_le hX).le
  have hy16 : 1 ≤ y ^ 16 := one_le_pow₀ hy
  have hMupper : ((M + 1 : ℕ) : ℝ) ≤ X * y ^ 16 + 2 := by
    have h := directTruncation_upper hX
    dsimp [M, y] at h ⊢
    norm_num at h ⊢
    linarith
  have hrpow : r ^ (M + 1) ≤ (X⁻¹) ^ 3 := by
    simpa [r, M] using canonical_geometric_power_le_inv_cube hX
  have hparent : r / (1 - r) ^ 2 + (1 - r)⁻¹ ≤ 6 * X ^ 2 := by
    simpa [r] using geometric_tail_parenthesis_le hX
  have hMnonneg : 0 ≤ ((M + 1 : ℕ) : ℝ) := by positivity
  have hrpow0 : 0 ≤ r ^ (M + 1) := by positivity
  have hparent0 : 0 ≤ r / (1 - r) ^ 2 + (1 - r)⁻¹ := by
    have hD : 0 < 1 - r := by
      dsimp [r]
      exact (one_div_two_mul_le_one_sub_exp_neg_one_div hX).trans_lt'
        (by positivity)
    positivity
  have heq : (X * y ^ 16 + 2) * (X⁻¹) ^ 3 * (6 * X ^ 2) =
      6 * y ^ 16 + 12 / X := by
    field_simp [hX0.ne']
    ring
  unfold shiftedDirectTailEnvelope
  change ((M : ℝ) + 1) * r ^ (M + 1) *
      (r / (1 - r) ^ 2 + (1 - r)⁻¹) ≤ 10 * y ^ 16
  have hMupper' : (M : ℝ) + 1 ≤ X * y ^ 16 + 2 := by
    norm_num at hMupper ⊢
    exact hMupper
  calc
    ((M : ℝ) + 1) * r ^ (M + 1) *
        (r / (1 - r) ^ 2 + (1 - r)⁻¹) ≤
      (X * y ^ 16 + 2) * (X⁻¹) ^ 3 * (6 * X ^ 2) := by
        gcongr
    _ = 6 * y ^ 16 + 12 / X := heq
    _ ≤ 10 * y ^ 16 := by
      have hdiv : 12 / X ≤ 4 := (div_le_iff₀ hX0).2 (by linarith)
      linarith

/-- Squared form used directly by the second-moment budget. -/
theorem canonical_shiftedDirectTailEnvelope_sq_le
    {X : ℝ} (hX : 3 ≤ X) :
    shiftedDirectTailEnvelope (directTruncation X) X ^ 2 ≤
      100 * Real.log X ^ 200 := by
  have htail := canonical_shiftedDirectTailEnvelope_le hX
  have htail0 : 0 ≤ shiftedDirectTailEnvelope (directTruncation X) X := by
    unfold shiftedDirectTailEnvelope
    have hD : 0 < 1 - Real.exp (-(1 / X)) :=
      (one_div_two_mul_le_one_sub_exp_neg_one_div hX).trans_lt'
        (by positivity)
    positivity
  have hy : 1 ≤ Real.log X := (one_lt_log_of_three_le hX).le
  have hsq : shiftedDirectTailEnvelope (directTruncation X) X ^ 2 ≤
      (10 * Real.log X ^ 16) ^ 2 :=
    pow_le_pow_left₀ htail0 htail 2
  calc
    shiftedDirectTailEnvelope (directTruncation X) X ^ 2 ≤
        (10 * Real.log X ^ 16) ^ 2 := hsq
    _ = 100 * Real.log X ^ 32 := by ring
    _ ≤ 100 * Real.log X ^ 200 := by
      have hp : Real.log X ^ 32 ≤ Real.log X ^ 200 :=
        pow_le_pow_right₀ hy (by norm_num)
      exact mul_le_mul_of_nonneg_left hp (by norm_num)


/-- Canonical primitive direct-series bound with the infinite tail already
absorbed into `400 X log(X)^200`.  The displayed finite shell sum is the sole
remaining deterministic expression. -/
theorem primitiveFamilyDirectSecondMoment_le_canonicalShells
    (d : ℕ) [NeZero d]
    {T sigma delta : ℝ}
    (hT : 3 ≤ T)
    (hdelta : 0 ≤ delta)
    (hsigma : |sigma - 1 / 2| ≤ delta)
    (hsigma0 : 0 ≤ sigma) :
    let X := primitiveShiftedScale d T
    let M := directTruncation X
    let Y := directEnergyCeiling X
    primitiveFamilyDirectSecondMoment d T sigma ≤
      2 * (4 * (d : ℝ) * T +
        2 * (sourceDyadicCount M : ℝ) *
          ∑ j : Fin (sourceDyadicCount M),
            directSourceShellCost d M T Y delta j) +
      400 * ((d : ℝ) * T) * Real.log X ^ 200 := by
  dsimp only
  let X := primitiveShiftedScale d T
  let M := directTruncation X
  let Y := directEnergyCeiling X
  have hX : 3 ≤ X := by
    dsimp [X, primitiveShiftedScale]
    have hd : (1 : ℝ) ≤ d := by exact_mod_cast (NeZero.pos d)
    nlinarith
  have hM : 1 ≤ M := (three_le_directTruncation hX).trans' (by norm_num)
  have hNY : ∀ j : Fin (sourceDyadicCount M),
      ((2 * 2 ^ (j : ℕ) : ℕ) : ℝ) ≤ Y := by
    intro j
    simpa [M, Y] using sourceShell_le_directEnergyCeiling hX j
  have hraw := primitiveFamilyDirectSecondMoment_le_explicit
    d M hM (T := T) (Y := Y) (sigma := sigma) (delta := delta)
      (by linarith) hNY hdelta hsigma hsigma0
  have htail := canonical_shiftedDirectTailEnvelope_sq_le hX
  have htailScaled :
      4 * (d : ℝ) * T * shiftedDirectTailEnvelope M X ^ 2 ≤
        400 * ((d : ℝ) * T) * Real.log X ^ 200 := by
    have hfront : 0 ≤ 4 * (d : ℝ) * T := by positivity
    have hs := mul_le_mul_of_nonneg_left
      (by simpa [M] using htail) hfront
    nlinarith
  have hfinal := hraw.trans (add_le_add_right htailScaled _)
  simpa [X, M, Y] using hfinal


end
end RamachandraShiftedDirectTailAbsorption

#print axioms RamachandraShiftedDirectTailAbsorption.canonical_geometric_power_le_inv_cube
#print axioms RamachandraShiftedDirectTailAbsorption.geometric_tail_parenthesis_le
#print axioms RamachandraShiftedDirectTailAbsorption.canonical_shiftedDirectTailEnvelope_sq_le
#print axioms RamachandraShiftedDirectTailAbsorption.primitiveFamilyDirectSecondMoment_le_canonicalShells
