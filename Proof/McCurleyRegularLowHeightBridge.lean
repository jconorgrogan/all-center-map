import McCurleyHighImaginaryBridge
import WeakVKNearDecay

/-!
# McCurley regular-zero bridge at bounded ordinate

This file proves the deterministic part of the bounded-height near-one branch
in equation (2.7).  It consumes the literal exceptional-zero *shape* from
McCurley's Theorem 1.1 as a local higher-order hypothesis and proves that every
other zero has a gap which beats all powers of `log X` at polylogarithmic
conductor.

The source constant is `9.645908801`; the closed consumer uses the rigorously
larger `9.64590881`, exactly as in `McCurleyHighImaginaryBridge`.
-/

namespace MAPMcCurleyRegularLowHeightBridge

open Filter Asymptotics
open MAPMcCurleyHighImaginaryBridge

noncomputable section

def safeDenominator (q : ℕ) (t : ℝ) : ℝ :=
  safeClosedR * Real.log (mccurleyScale q t)

theorem safeDenominator_pos (q : ℕ) (t : ℝ) :
    0 < safeDenominator q t := by
  unfold safeDenominator
  exact mul_pos (by norm_num [safeClosedR]) (log_mccurleyScale_pos q t)

/-- The full source conclusion needed from McCurley: a zero in the published
open region is real and belongs to a real nonprincipal character.  Simplicity
and family uniqueness, though also published, are not used by this bridge. -/
theorem one_div_safeDenominator_le_one_sub_sigma_of_regular_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hPublishedExceptionShape :
      ∀ (psi : DirichletCharacter ℂ q) (s : ℂ),
        mccurleyBoundary publishedR q s.im < s.re →
        DirichletCharacter.LFunction psi s = 0 →
        s.im = 0 ∧ psi ≠ 1 ∧ psi ^ 2 = 1)
    {sigma t : ℝ}
    (hregular : ¬ (chi ≠ 1 ∧ chi ^ 2 = 1 ∧ t = 0))
    (hzero : DirichletCharacter.LFunction chi
      ((sigma : ℂ) + (t : ℂ) * Complex.I) = 0) :
    1 / safeDenominator q t ≤ 1 - sigma := by
  have hnotSafe : ¬ (mccurleyBoundary safeClosedR q t ≤ sigma) := by
    intro hsafe
    have hinside : mccurleyBoundary publishedR q t < sigma :=
      (published_boundary_lt_safe_closed_boundary q t).trans_le hsafe
    have hshape := hPublishedExceptionShape chi
      ((sigma : ℂ) + (t : ℂ) * Complex.I) (by simpa using hinside) hzero
    apply hregular
    have hshape' : t = 0 ∧ chi ≠ 1 ∧ chi ^ 2 = 1 := by
      simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add,
        Complex.add_re, Complex.ofReal_re, zero_mul, add_zero] using hshape
    exact ⟨hshape'.2.1, hshape'.2.2, hshape'.1⟩
  have hstrict : sigma < mccurleyBoundary safeClosedR q t :=
    lt_of_not_ge hnotSafe
  dsimp [mccurleyBoundary] at hstrict
  unfold safeDenominator
  linarith

theorem mccurleyScale_le_ten_mul_log_rpow
    {K X : ℝ} {q : ℕ} {t : ℝ}
    (hK : 0 ≤ K) (hlog : 1 ≤ Real.log X)
    (hq : (q : ℝ) ≤ Real.rpow (Real.log X) K)
    (ht : |t| ≤ 3) :
    mccurleyScale q t ≤
      10 * Real.rpow (Real.log X) K := by
  have hpowOne : 1 ≤ Real.rpow (Real.log X) K :=
    Real.one_le_rpow hlog hK
  unfold mccurleyScale
  apply max_le
  · apply max_le
    · exact hq.trans (by nlinarith [Real.rpow_nonneg (zero_le_one.trans hlog) K])
    · calc
        (q : ℝ) * |t| ≤ Real.rpow (Real.log X) K * 3 := by
          exact mul_le_mul hq ht (abs_nonneg t)
            (Real.rpow_nonneg (zero_le_one.trans hlog) K)
        _ ≤ 10 * Real.rpow (Real.log X) K := by
          nlinarith [Real.rpow_nonneg (zero_le_one.trans hlog) K]
  · nlinarith

theorem log_mccurleyScale_le_loglog
    {K X : ℝ} {q : ℕ} {t : ℝ}
    (hK : 0 ≤ K) (hlogX : 1 ≤ Real.log X)
    (hlog : 1 ≤ Real.log (Real.log X))
    (hq : (q : ℝ) ≤ Real.rpow (Real.log X) K)
    (ht : |t| ≤ 3) :
    Real.log (mccurleyScale q t) ≤
      (K + Real.log 10) * Real.log (Real.log X) := by
  have hscale := mccurleyScale_le_ten_mul_log_rpow hK hlogX hq ht
  have hscalePos : 0 < mccurleyScale q t :=
    zero_lt_one.trans (one_lt_mccurleyScale q t)
  have hpowPos : 0 < Real.rpow (Real.log X) K :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hlogX) K
  have hlogmono : Real.log (mccurleyScale q t) ≤
      Real.log (10 * Real.rpow (Real.log X) K) :=
    Real.log_le_log hscalePos hscale
  have hlogprod : Real.log (10 * Real.rpow (Real.log X) K) =
      Real.log 10 + K * Real.log (Real.log X) := by
    rw [Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) hpowPos.ne']
    congr 1
    exact Real.log_rpow (zero_lt_one.trans_le hlogX) K
  rw [hlogprod] at hlogmono
  have hlogTen : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
  nlinarith

private theorem eventually_loglog_le_quarter_log_rpow :
    ∀ᶠ X : ℝ in atTop,
      Real.log (Real.log X) ≤
        Real.rpow (Real.log X) (1 / 4 : ℝ) := by
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 4)).eventuallyLE
  exact Real.tendsto_log_atTop.eventually (by
    filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with L hL hL1
    have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1.le
    have hrpow0 : 0 ≤ Real.rpow L (1 / 4 : ℝ) :=
      Real.rpow_nonneg (zero_lt_one.trans hL1).le _
    have hL' : Real.log L ≤ |Real.rpow L (1 / 4 : ℝ)| := by
      simpa [Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg hlog0] using hL
    rwa [abs_of_nonneg hrpow0] at hL')

/-- McCurley's bounded-height regular-zero gap is at least a fixed multiple
of `(log X)^(-1/4)` at polylogarithmic conductor. -/
theorem weakGap_le_of_mccurley_regular_lowHeight
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) (t sigma : ℝ),
      (q : ℝ) ≤ Real.rpow (Real.log X) K →
      |t| ≤ 3 →
      1 / safeDenominator q t ≤ 1 - sigma →
      (1 / (safeClosedR * (K + Real.log 10))) *
          Real.rpow (Real.log X) (-(1 / 4 : ℝ)) ≤ 1 - sigma := by
  filter_upwards [eventually_loglog_le_quarter_log_rpow,
      eventually_gt_atTop (Real.exp (Real.exp 1))] with
      X hquarter hX q t sigma hq ht hrecip
  have hXpos : 0 < X := (Real.exp_pos _).trans hX
  have hXone : 1 < X :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans hX
  have hlogXexp : Real.exp 1 < Real.log X := by
    rw [Real.lt_log_iff_exp_lt hXpos]
    exact hX
  have hlogXone : 1 < Real.log X :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).trans hlogXexp
  have hloglogOne : 1 < Real.log (Real.log X) := by
    rw [Real.lt_log_iff_exp_lt (Real.log_pos hXone)]
    exact hlogXexp
  have hloglog := log_mccurleyScale_le_loglog
    hK hlogXone.le hloglogOne.le hq ht
  have hCpos : 0 < K + Real.log 10 :=
    add_pos_of_nonneg_of_pos hK (Real.log_pos (by norm_num))
  have hRpos : 0 < safeClosedR := by norm_num [safeClosedR]
  have hpowPos : 0 < Real.rpow (Real.log X) (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (Real.log_pos hXone) _
  have hdenUpper : safeDenominator q t ≤
      safeClosedR * (K + Real.log 10) *
        Real.rpow (Real.log X) (1 / 4 : ℝ) := by
    unfold safeDenominator
    calc
      safeClosedR * Real.log (mccurleyScale q t) ≤
          safeClosedR * ((K + Real.log 10) *
            Real.log (Real.log X)) :=
        mul_le_mul_of_nonneg_left hloglog hRpos.le
      _ ≤ safeClosedR * ((K + Real.log 10) *
            Real.rpow (Real.log X) (1 / 4 : ℝ)) := by
        gcongr
      _ = safeClosedR * (K + Real.log 10) *
            Real.rpow (Real.log X) (1 / 4 : ℝ) := by ring
  have hinv :
      1 / (safeClosedR * (K + Real.log 10) *
          Real.rpow (Real.log X) (1 / 4 : ℝ)) ≤
        1 / safeDenominator q t :=
    one_div_le_one_div_of_le (safeDenominator_pos q t) hdenUpper
  have hid :
      (1 / (safeClosedR * (K + Real.log 10))) *
          Real.rpow (Real.log X) (-(1 / 4 : ℝ)) =
        1 / (safeClosedR * (K + Real.log 10) *
          Real.rpow (Real.log X) (1 / 4 : ℝ)) := by
    have hneg := Real.rpow_neg (Real.log_pos hXone).le (1 / 4 : ℝ)
    calc
      (1 / (safeClosedR * (K + Real.log 10))) *
          Real.rpow (Real.log X) (-(1 / 4 : ℝ)) =
        (1 / (safeClosedR * (K + Real.log 10))) *
          (Real.rpow (Real.log X) (1 / 4 : ℝ))⁻¹ :=
        congrArg (fun z : ℝ =>
          (1 / (safeClosedR * (K + Real.log 10))) * z) hneg
      _ = 1 / (safeClosedR * (K + Real.log 10) *
          Real.rpow (Real.log X) (1 / 4 : ℝ)) := by field_simp
  rw [hid]
  exact hinv.trans hrecip

/-- Complete deterministic bounded-height contribution after the exact
McCurley exception-shape conclusion. -/
theorem mccurleyRegularLowHeight_nearFactor_beats_polylog
    (K P A : ℝ) (hK : 0 ≤ K) (hP : 0 ≤ P) (hA : 0 ≤ A) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q]
        (t sigma : ℝ) (chi : DirichletCharacter ℂ q),
      (q : ℝ) ≤ Real.rpow (Real.log X) K →
      |t| ≤ 3 →
      (∀ (psi : DirichletCharacter ℂ q) (s : ℂ),
        mccurleyBoundary publishedR q s.im < s.re →
        DirichletCharacter.LFunction psi s = 0 →
        s.im = 0 ∧ psi ≠ 1 ∧ psi ^ 2 = 1) →
      ¬ (chi ≠ 1 ∧ chi ^ 2 = 1 ∧ t = 0) →
      DirichletCharacter.LFunction chi
          ((sigma : ℂ) + (t : ℂ) * Complex.I) = 0 →
      Real.rpow (Real.log X) P *
          Real.rpow X (-((1 - sigma) / 12)) ≤
        Real.rpow (Real.log X) (-A) := by
  have hc : 0 < 1 / (safeClosedR * (K + Real.log 10)) := by
    have hC : 0 < K + Real.log 10 :=
      add_pos_of_nonneg_of_pos hK (Real.log_pos (by norm_num))
    exact one_div_pos.mpr (mul_pos (by norm_num [safeClosedR]) hC)
  filter_upwards [weakGap_le_of_mccurley_regular_lowHeight K hK,
      WeakVKNear.weakGap_nearFactor_beats_polylog
        (1 / 4 : ℝ) (1 / (safeClosedR * (K + Real.log 10))) P A
        (by norm_num) hc hP hA] with
      X hgap hdecay q _inst t sigma chi hq ht hshape hregular hzero
  have hrecip := one_div_safeDenominator_le_one_sub_sigma_of_regular_zero
    chi hshape hregular hzero
  have homega := hgap q t sigma hq ht hrecip
  exact hdecay (1 - sigma) homega

end

end MAPMcCurleyRegularLowHeightBridge

#print axioms MAPMcCurleyRegularLowHeightBridge.one_div_safeDenominator_le_one_sub_sigma_of_regular_zero
#print axioms MAPMcCurleyRegularLowHeightBridge.mccurleyScale_le_ten_mul_log_rpow
#print axioms MAPMcCurleyRegularLowHeightBridge.log_mccurleyScale_le_loglog
#print axioms MAPMcCurleyRegularLowHeightBridge.weakGap_le_of_mccurley_regular_lowHeight
#print axioms MAPMcCurleyRegularLowHeightBridge.mccurleyRegularLowHeight_nearFactor_beats_polylog
