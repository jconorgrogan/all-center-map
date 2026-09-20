import BHPRademacherZeroBoundary
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Gaussian envelopes for a quantitative Rademacher interpolation

A Gaussian centered at the target ordinate makes the polynomial/logarithmic
boundary estimates uniform on the full vertical lines.  These scalar lemmas
track the fixed epsilon loss explicitly.
-/

namespace MAPBHPRademacherGaussianEnvelope

open Real

noncomputable section

/-- The elementary logarithm-to-small-power trade with an explicit constant. -/
theorem one_add_log_le_inv_rpow
    {eta x : ℝ} (heta : 0 < eta) (hx : 1 ≤ x) :
    1 + Real.log x ≤ (1 + eta⁻¹) * Real.rpow x eta := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hpowpos : 0 < Real.rpow x eta := Real.rpow_pos_of_pos hxpos eta
  have hpowone : 1 ≤ Real.rpow x eta := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (show 0 ≤ eta by linarith)
  have hlog := Real.log_le_sub_one_of_pos hpowpos
  have hlogEq : Real.log (Real.rpow x eta) = eta * Real.log x :=
    Real.log_rpow hxpos eta
  rw [hlogEq] at hlog
  have hdiv : Real.log x ≤ (Real.rpow x eta - 1) / eta := by
    apply (le_div_iff₀ heta).2
    simpa [mul_comm] using hlog
  have hinv : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
  calc
    1 + Real.log x ≤ 1 + (Real.rpow x eta - 1) / eta :=
      by simpa [add_comm] using add_le_add_left hdiv 1
    _ ≤ (1 + eta⁻¹) * Real.rpow x eta := by
      rw [div_eq_mul_inv]
      nlinarith

/-- A linear polynomial is killed uniformly by the centered Gaussian. -/
theorem one_add_mul_exp_neg_sq_le_two (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) * Real.exp (-(r ^ 2)) ≤ 2 := by
  by_cases hr1 : r ≤ 1
  · have hexp : Real.exp (-(r ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg r])
    nlinarith [Real.exp_pos (-(r ^ 2))]
  · have hrOne : 1 ≤ r := le_of_not_ge hr1
    have hpoly : 1 + r ≤ 1 + r ^ 2 := by nlinarith
    have hexp : 1 + r ^ 2 ≤ Real.exp (r ^ 2) := by
      simpa [add_comm] using Real.add_one_le_exp (r ^ 2)
    have hpos : 0 < Real.exp (r ^ 2) := Real.exp_pos _
    have hquot : (1 + r) / Real.exp (r ^ 2) ≤ 1 :=
      (div_le_one hpos).2 (hpoly.trans hexp)
    rw [Real.exp_neg]
    simpa [div_eq_mul_inv] using hquot.trans (by norm_num : (1 : ℝ) ≤ 2)

/-- The quadratic polynomial needed for the global boundedness premise of
Hadamard's theorem is also killed by the centered Gaussian. -/
theorem one_add_sq_mul_exp_neg_sq_le_four (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) ^ 2 * Real.exp (-(r ^ 2)) ≤ 4 := by
  by_cases hr1 : r ≤ 1
  · have hpoly : (1 + r) ^ 2 ≤ 4 := by nlinarith
    have hexp : Real.exp (-(r ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg r])
    have hnonneg : 0 ≤ (1 + r) ^ 2 := sq_nonneg _
    nlinarith [Real.exp_pos (-(r ^ 2))]
  · have hrOne : 1 ≤ r := le_of_not_ge hr1
    have hpoly : (1 + r) ^ 2 ≤ 4 * r ^ 2 := by nlinarith
    have hexp : r ^ 2 ≤ Real.exp (r ^ 2) := by
      have h := Real.add_one_le_exp (r ^ 2)
      nlinarith
    have hpos : 0 < Real.exp (r ^ 2) := Real.exp_pos _
    have hquot : r ^ 2 / Real.exp (r ^ 2) ≤ 1 :=
      (div_le_one hpos).2 hexp
    rw [Real.exp_neg]
    have hmul : (1 + r) ^ 2 * (Real.exp (r ^ 2))⁻¹ ≤
        4 * (r ^ 2 * (Real.exp (r ^ 2))⁻¹) := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_right hpoly (inv_nonneg.mpr hpos.le)
    calc
      (1 + r) ^ 2 * (Real.exp (r ^ 2))⁻¹ ≤
          4 * (r ^ 2 * (Real.exp (r ^ 2))⁻¹) := hmul
      _ ≤ 4 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa [div_eq_mul_inv] using hquot
      _ = 4 := by ring

/-- Translation of the height scale from a boundary ordinate `v` to the
center ordinate `u`. -/
theorem three_add_abs_le_center_mul (u v : ℝ) :
    3 + |v| ≤ (3 + |u|) * (1 + |v - u|) := by
  have htri : |v| ≤ |u| + |v - u| := by
    have h := abs_add_le u (v - u)
    rw [show u + (v - u) = v by ring] at h
    linarith
  have hu : 0 ≤ |u| := abs_nonneg u
  have hr : 0 ≤ |v - u| := abs_nonneg (v - u)
  nlinarith

/-- The logarithmic boundary factor times the square-root conductor-height
factor is uniformly controlled by the center scale after Gaussian damping. -/
theorem logarithmic_sqrt_gaussian_envelope
    {eta : ℝ} (heta : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    {q : ℕ} (hq : 1 ≤ q) (u v : ℝ) :
    3 * (1 + Real.log (2 * (q : ℝ) * (3 + |v|))) *
        Real.rpow (q : ℝ) (1 / 2) *
        Real.rpow (1 + |v|) (1 / 2) *
        Real.exp (-((v - u) ^ 2)) ≤
      12 * (1 + eta⁻¹) *
        Real.rpow (2 * (q : ℝ) * (3 + |u|)) (eta + 1 / 2) := by
  let r : ℝ := |v - u|
  let P : ℝ := 2 * (q : ℝ) * (3 + |v|)
  let Q : ℝ := 2 * (q : ℝ) * (3 + |u|)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hr : 0 ≤ r := abs_nonneg _
  have hPone : 1 ≤ P := by dsimp [P]; nlinarith [abs_nonneg v]
  have hQone : 1 ≤ Q := by dsimp [Q]; nlinarith [abs_nonneg u]
  have hPQ : P ≤ Q * (1 + r) := by
    dsimp [P, Q, r]
    have h := three_add_abs_le_center_mul u v
    nlinarith
  have hlog := one_add_log_le_inv_rpow heta hPone
  have hpowPQ : Real.rpow P eta ≤ Real.rpow (Q * (1 + r)) eta :=
    Real.rpow_le_rpow (by positivity) hPQ heta.le
  have hsplit : Real.rpow (Q * (1 + r)) eta =
      Real.rpow Q eta * Real.rpow (1 + r) eta :=
    Real.mul_rpow (by positivity) (by positivity)
  have hetaSum : eta + 1 / 2 ≤ 1 := by linarith
  have hbase : 1 ≤ 1 + r := by linarith
  have hrpowSum : Real.rpow (1 + r) (eta + 1 / 2) ≤ 1 + r := by
    simpa using Real.rpow_le_rpow_of_exponent_le hbase hetaSum
  have hsqrtHeight :
      Real.rpow (q : ℝ) (1 / 2) *
          Real.rpow (1 + |v|) (1 / 2) ≤
        Real.rpow Q (1 / 2) * Real.rpow (1 + r) (1 / 2) := by
    have hheight : (q : ℝ) * (1 + |v|) ≤ Q * (1 + r) := by
      dsimp [Q, r]
      have h := three_add_abs_le_center_mul u v
      nlinarith
    have hp := Real.rpow_le_rpow (by positivity) hheight (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)] at hp
    exact hp
  have hgauss := one_add_mul_exp_neg_sq_le_two r hr
  have hinv : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
  have hfac : 0 ≤ 1 + eta⁻¹ := by linarith
  have hlogNonneg : 0 ≤ 1 + Real.log P := by
    have : 0 ≤ Real.log P := Real.log_nonneg hPone
    linarith
  have hPpow : 0 ≤ Real.rpow P eta := Real.rpow_nonneg (by linarith) _
  have hQpow : 0 ≤ Real.rpow Q eta := Real.rpow_nonneg (by linarith) _
  have hrpow : 0 ≤ Real.rpow (1 + r) eta := Real.rpow_nonneg (by linarith) _
  have hQhalf : 0 ≤ Real.rpow Q (1 / 2) := Real.rpow_nonneg (by linarith) _
  have hrhalf : 0 ≤ Real.rpow (1 + r) (1 / 2) :=
    Real.rpow_nonneg (by linarith) _
  have hqhalf : 0 ≤ Real.rpow (q : ℝ) (1 / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hvhalf : 0 ≤ Real.rpow (1 + |v|) (1 / 2) :=
    Real.rpow_nonneg (by positivity) _
  have hheightNonneg :
      0 ≤ Real.rpow (q : ℝ) (1 / 2) * Real.rpow (1 + |v|) (1 / 2) := by
    exact mul_nonneg hqhalf hvhalf
  have hlogScaled :
      3 * (1 + Real.log P) ≤ 3 * ((1 + eta⁻¹) * Real.rpow P eta) :=
    mul_le_mul_of_nonneg_left hlog (by norm_num)
  have hfirst :
      (3 * (1 + Real.log P)) *
          (Real.rpow (q : ℝ) (1 / 2) * Real.rpow (1 + |v|) (1 / 2)) ≤
        (3 * ((1 + eta⁻¹) * Real.rpow P eta)) *
          (Real.rpow Q (1 / 2) * Real.rpow (1 + r) (1 / 2)) := by
    exact mul_le_mul hlogScaled hsqrtHeight hheightNonneg
      (mul_nonneg (by positivity) (mul_nonneg hfac hPpow))
  have hExpNonneg : 0 ≤ Real.exp (-(r ^ 2)) := (Real.exp_pos _).le
  have hfirstGaussian :
      ((3 * (1 + Real.log P)) *
          (Real.rpow (q : ℝ) (1 / 2) * Real.rpow (1 + |v|) (1 / 2))) *
          Real.exp (-(r ^ 2)) ≤
        ((3 * ((1 + eta⁻¹) * Real.rpow P eta)) *
          (Real.rpow Q (1 / 2) * Real.rpow (1 + r) (1 / 2))) *
          Real.exp (-(r ^ 2)) :=
    mul_le_mul_of_nonneg_right hfirst hExpNonneg
  have hreplaceP :
      (3 * ((1 + eta⁻¹) * Real.rpow P eta)) *
          (Real.rpow Q (1 / 2) * Real.rpow (1 + r) (1 / 2)) ≤
        (3 * ((1 + eta⁻¹) *
          (Real.rpow Q eta * Real.rpow (1 + r) eta))) *
          (Real.rpow Q (1 / 2) * Real.rpow (1 + r) (1 / 2)) := by
    have hp : Real.rpow P eta ≤ Real.rpow Q eta * Real.rpow (1 + r) eta := by
      rw [← hsplit]
      exact hpowPQ
    have hscaled :
        3 * ((1 + eta⁻¹) * Real.rpow P eta) ≤
          3 * ((1 + eta⁻¹) *
            (Real.rpow Q eta * Real.rpow (1 + r) eta)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hp hfac) (by norm_num)
    exact mul_le_mul_of_nonneg_right hscaled
      (mul_nonneg hQhalf hrhalf)
  have hreplacePGaussian :
      ((3 * ((1 + eta⁻¹) * Real.rpow P eta)) *
          (Real.rpow Q (1 / 2) * Real.rpow (1 + r) (1 / 2))) *
          Real.exp (-(r ^ 2)) ≤
        ((3 * ((1 + eta⁻¹) *
          (Real.rpow Q eta * Real.rpow (1 + r) eta))) *
          (Real.rpow Q (1 / 2) * Real.rpow (1 + r) (1 / 2))) *
          Real.exp (-(r ^ 2)) :=
    mul_le_mul_of_nonneg_right hreplaceP hExpNonneg
  have hQadd :
      Real.rpow Q eta * Real.rpow Q (1 / 2) =
        Real.rpow Q (eta + 1 / 2) := by
    exact (Real.rpow_add (show 0 < Q by linarith) eta (1 / 2)).symm
  have hradd :
      Real.rpow (1 + r) eta * Real.rpow (1 + r) (1 / 2) =
        Real.rpow (1 + r) (eta + 1 / 2) := by
    exact (Real.rpow_add (show 0 < 1 + r by linarith) eta (1 / 2)).symm
  have hcoefNonneg :
      0 ≤ 3 * (1 + eta⁻¹) * Real.rpow Q (eta + 1 / 2) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hfac)
      (Real.rpow_nonneg (by linarith) _)
  have hrsq : r ^ 2 = (v - u) ^ 2 := by
    dsimp only [r]
    exact sq_abs (v - u)
  rw [← hrsq]
  change
    3 * (1 + Real.log P) * Real.rpow (q : ℝ) (1 / 2) *
        Real.rpow (1 + |v|) (1 / 2) * Real.exp (-(r ^ 2)) ≤
      12 * (1 + eta⁻¹) * Real.rpow Q (eta + 1 / 2)
  calc
    3 * (1 + Real.log P) * Real.rpow (q : ℝ) (1 / 2) *
        Real.rpow (1 + |v|) (1 / 2) * Real.exp (-(r ^ 2)) =
      ((3 * (1 + Real.log P)) *
          (Real.rpow (q : ℝ) (1 / 2) * Real.rpow (1 + |v|) (1 / 2))) *
        Real.exp (-(r ^ 2)) := by ring
    _ ≤ ((3 * ((1 + eta⁻¹) * Real.rpow P eta)) *
          (Real.rpow Q (1 / 2) * Real.rpow (1 + r) (1 / 2))) *
        Real.exp (-(r ^ 2)) := hfirstGaussian
    _ ≤ ((3 * ((1 + eta⁻¹) *
          (Real.rpow Q eta * Real.rpow (1 + r) eta))) *
          (Real.rpow Q (1 / 2) * Real.rpow (1 + r) (1 / 2))) *
        Real.exp (-(r ^ 2)) := hreplacePGaussian
    _ = 3 * (1 + eta⁻¹) *
        (Real.rpow Q eta * Real.rpow Q (1 / 2)) *
        (Real.rpow (1 + r) eta * Real.rpow (1 + r) (1 / 2)) *
        Real.exp (-(r ^ 2)) := by ring
    _ = 3 * (1 + eta⁻¹) * Real.rpow Q (eta + 1 / 2) *
        (Real.rpow (1 + r) (eta + 1 / 2) * Real.exp (-(r ^ 2))) := by
          rw [hQadd, hradd]
          ring
    _ ≤ 3 * (1 + eta⁻¹) * Real.rpow Q (eta + 1 / 2) *
        ((1 + r) * Real.exp (-(r ^ 2))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hrpowSum (Real.exp_pos _).le)
            hcoefNonneg
    _ ≤ 3 * (1 + eta⁻¹) * Real.rpow Q (eta + 1 / 2) * 2 := by
          exact mul_le_mul_of_nonneg_left hgauss hcoefNonneg
    _ ≤ 12 * (1 + eta⁻¹) * Real.rpow Q (eta + 1 / 2) := by
          have hpow : 0 ≤ Real.rpow Q (eta + 1 / 2) :=
            Real.rpow_nonneg (by linarith) _
          nlinarith

/-- The logarithmic right boundary is uniformly controlled after multiplying
by the same Gaussian.  The intentionally loose constant keeps the later
three-lines statement free of numerical side conditions. -/
theorem logarithmic_gaussian_envelope
    {eta : ℝ} (heta : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    {q : ℕ} (hq : 1 ≤ q) (u v : ℝ) :
    3 * (1 + Real.log (2 * (q : ℝ) * (3 + |v|))) *
        Real.exp (1 - ((v - u) ^ 2)) ≤
      36 * (1 + eta⁻¹) *
        Real.rpow (2 * (q : ℝ) * (3 + |u|)) eta := by
  let r : ℝ := |v - u|
  let P : ℝ := 2 * (q : ℝ) * (3 + |v|)
  let Q : ℝ := 2 * (q : ℝ) * (3 + |u|)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hr : 0 ≤ r := abs_nonneg _
  have hPone : 1 ≤ P := by dsimp [P]; nlinarith [abs_nonneg v]
  have hQone : 1 ≤ Q := by dsimp [Q]; nlinarith [abs_nonneg u]
  have hPQ : P ≤ Q * (1 + r) := by
    dsimp [P, Q, r]
    have h := three_add_abs_le_center_mul u v
    nlinarith
  have hlog := one_add_log_le_inv_rpow heta hPone
  have hpowPQ : Real.rpow P eta ≤ Real.rpow (Q * (1 + r)) eta :=
    Real.rpow_le_rpow (by positivity) hPQ heta.le
  have hsplit : Real.rpow (Q * (1 + r)) eta =
      Real.rpow Q eta * Real.rpow (1 + r) eta :=
    Real.mul_rpow (by positivity) (by positivity)
  have hetaOne : eta ≤ 1 := by linarith
  have hbase : 1 ≤ 1 + r := by linarith
  have hrpow : Real.rpow (1 + r) eta ≤ 1 + r := by
    simpa using Real.rpow_le_rpow_of_exponent_le hbase hetaOne
  have hgauss := one_add_mul_exp_neg_sq_le_two r hr
  have hinv : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
  have hfac : 0 ≤ 1 + eta⁻¹ := by linarith
  have hPpow : 0 ≤ Real.rpow P eta := Real.rpow_nonneg (by linarith) _
  have hQpow : 0 ≤ Real.rpow Q eta := Real.rpow_nonneg (by linarith) _
  have hrpow0 : 0 ≤ Real.rpow (1 + r) eta :=
    Real.rpow_nonneg (by linarith) _
  have hscaled :
      3 * (1 + Real.log P) ≤ 3 * ((1 + eta⁻¹) * Real.rpow P eta) :=
    mul_le_mul_of_nonneg_left hlog (by norm_num)
  have hp : Real.rpow P eta ≤ Real.rpow Q eta * Real.rpow (1 + r) eta := by
    rw [← hsplit]
    exact hpowPQ
  have hreplace :
      3 * ((1 + eta⁻¹) * Real.rpow P eta) ≤
        3 * ((1 + eta⁻¹) *
          (Real.rpow Q eta * Real.rpow (1 + r) eta)) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hp hfac) (by norm_num)
  have hExpNonneg : 0 ≤ Real.exp 1 * Real.exp (-(r ^ 2)) := by positivity
  have hcoefNonneg : 0 ≤ 3 * (1 + eta⁻¹) * Real.rpow Q eta := by
    exact mul_nonneg (mul_nonneg (by norm_num) hfac) hQpow
  have hrsq : r ^ 2 = (v - u) ^ 2 := by
    dsimp only [r]
    exact sq_abs (v - u)
  rw [← hrsq]
  change
    3 * (1 + Real.log P) * Real.exp (1 - r ^ 2) ≤
      36 * (1 + eta⁻¹) * Real.rpow Q eta
  calc
    3 * (1 + Real.log P) * Real.exp (1 - r ^ 2) =
        (3 * (1 + Real.log P)) *
          (Real.exp 1 * Real.exp (-(r ^ 2))) := by
      rw [show 1 - r ^ 2 = 1 + (-(r ^ 2)) by ring, Real.exp_add]
    _ ≤ (3 * ((1 + eta⁻¹) * Real.rpow P eta)) *
          (Real.exp 1 * Real.exp (-(r ^ 2))) :=
      mul_le_mul_of_nonneg_right hscaled hExpNonneg
    _ ≤ (3 * ((1 + eta⁻¹) *
          (Real.rpow Q eta * Real.rpow (1 + r) eta))) *
          (Real.exp 1 * Real.exp (-(r ^ 2))) :=
      mul_le_mul_of_nonneg_right hreplace hExpNonneg
    _ = 3 * (1 + eta⁻¹) * Real.rpow Q eta *
          (Real.rpow (1 + r) eta * Real.exp (-(r ^ 2))) * Real.exp 1 := by
      ring
    _ ≤ 3 * (1 + eta⁻¹) * Real.rpow Q eta *
          ((1 + r) * Real.exp (-(r ^ 2))) * Real.exp 1 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hrpow (Real.exp_pos _).le)
          hcoefNonneg)
        (Real.exp_pos _).le
    _ ≤ 3 * (1 + eta⁻¹) * Real.rpow Q eta * 2 * Real.exp 1 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgauss hcoefNonneg)
        (Real.exp_pos _).le
    _ ≤ 3 * (1 + eta⁻¹) * Real.rpow Q eta * 2 * 3 := by
      exact mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le
        (mul_nonneg hcoefNonneg (by norm_num))
    _ ≤ 36 * (1 + eta⁻¹) * Real.rpow Q eta := by
      nlinarith

end
end MAPBHPRademacherGaussianEnvelope
