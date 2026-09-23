import KhaleAppendixBHighZeroFromRaw
import KhaleAppendixBHeightCoefficientBound
import DirichletLFunctionConjugationGeneral
import APPrimitiveRegularLowGap

/-!
# Principal weak-VK gap from the high Khale argument only

The conductor-one branch does not need McCurley's bounded-height theorem.
All zeros below the fixed Khale startup height have a compact positive gap.
Above it, the already-certified high-zero reciprocal estimate applies at
level three, where the auxiliary condition `3^(1/100000) <= gamma` is
automatic.  Change of level transfers nonvanishing back to zeta.
-/

namespace MAPPrincipalWeakVKZeroGapFromKhaleHigh

open Filter DirichletZeros
open MAPKhaleAppendixBSource MAPKhaleWeakVKApplication
open MAPKhaleAppendixBHeightCoefficientBound
open MAPKhaleAppendixB1HighZeroReduction MAPKhaleAppendixB1FinalReduction

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local instance : NeZero 3 := ⟨by norm_num⟩

private theorem startup_ratio :
    (5110.6 : ℝ) / 4.45 ≤
      Real.log (Real.exp 11450) /
        Real.log (Real.log (Real.exp 11450)) := by
  rw [Real.log_exp]
  have hlogpos : 0 < Real.log (11450 : ℝ) :=
    (by norm_num : (0 : ℝ) < 9.345).trans
      log_11450_gt
  apply (le_div_iff₀ hlogpos).2
  nlinarith [log_11450_lt]

private theorem startup_loglog :
    (183 : ℝ) / (4.45 : ℝ) ^ 2 ≤
      Real.log (Real.log (Real.exp 11450)) := by
  rw [Real.log_exp]
  have h := log_11450_gt
  norm_num at h ⊢
  linarith

private theorem three_rpow_le_exp11450 :
    Real.rpow (3 : ℝ) (1 / 100000 : ℝ) ≤ Real.exp 11450 := by
  have hbase : (1 : ℝ) ≤ 3 := by norm_num
  have hexp : (1 / 100000 : ℝ) ≤ 1 := by norm_num
  have hr := Real.rpow_le_rpow_of_exponent_le hbase hexp
  rw [Real.rpow_one] at hr
  have hlarge : (3 : ℝ) ≤ Real.exp 11450 := by
    nlinarith [Real.add_one_lt_exp (x := (11450 : ℝ)) (by norm_num)]
  exact hr.trans hlarge

/-- The high-zero reciprocal estimate already rules out the level-three
principal L-function in the exact `104` region.  No finite-height McCurley
input is used. -/
theorem high_positive_three_nonvanishing
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hHigh : AppendixBHighZeroReciprocalEstimate)
    {u beta : ℝ} (hu : Real.exp 11450 ≤ u)
    (hbeta : 1 - 1 / khaleWeakDenominatorAbs 3 u ≤ beta) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 3)
      ((beta : ℂ) + (u : ℂ) * Complex.I) ≠ 0 := by
  intro hzero
  let F : ℝ := Real.rpow (Real.log u) (2 / 3 : ℝ) *
    Real.rpow (Real.log (Real.log u)) (1 / 3 : ℝ)
  let P : ℝ := Real.rpow 4.45 (2 / 3 : ℝ) * F
  let D1 : ℝ := 18 * Real.log 3 +
    appendixBHeightCoefficient 76.2 (Real.exp 11450) * P
  let D2 : ℝ := 18 * Real.log 3 + 104 * F
  have huPos : 0 < u := (Real.exp_pos 11450).trans_le hu
  have hlogu : (11450 : ℝ) ≤ Real.log u := by
    rw [← Real.log_exp 11450]
    exact Real.log_le_log (Real.exp_pos 11450) hu
  have hloguPos : 0 < Real.log u := by linarith
  have hlogloguPos : 0 < Real.log (Real.log u) := by
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 11450) hlogu
    exact (by norm_num : (0 : ℝ) < 9.345).trans
      (log_11450_gt.trans_le hmono)
  have hFpos : 0 < F := by
    dsimp [F]
    exact mul_pos (Real.rpow_pos_of_pos hloguPos _)
      (Real.rpow_pos_of_pos hlogloguPos _)
  have hcoeffNonneg :
      0 ≤ appendixBHeightCoefficient 76.2 (Real.exp 11450) := by
    unfold appendixBHeightCoefficient
    positivity
  have hD1pos : 0 < D1 := by
    dsimp [D1]
    have hPnonneg : 0 ≤ P := by
      dsimp [P]
      positivity
    have hterm : 0 ≤ appendixBHeightCoefficient 76.2 (Real.exp 11450) * P :=
      mul_nonneg hcoeffNonneg hPnonneg
    exact add_pos_of_pos_of_nonneg
      (mul_pos (by norm_num) (Real.log_pos (by norm_num))) hterm
  have hDlt : D1 < D2 := by
    dsimp [D1, D2, P]
    have hc := appendixBHeightCoefficient_mul_rpow_lt_104
    simpa only [add_comm, mul_assoc] using!
      add_lt_add_left (mul_lt_mul_of_pos_right hc hFpos) (18 * Real.log 3)
  have hD2pos : 0 < D2 := hD1pos.trans hDlt
  have hdeltaLeD2 : 1 - beta ≤ 1 / D2 := by
    have habsu : |u| = u := abs_of_pos huPos
    simpa only [D2, F, khaleWeakDenominatorAbs, khaleWeakDenominator,
      habsu, Nat.cast_ofNat, mul_assoc] using (show 1 - beta ≤
        1 / khaleWeakDenominatorAbs 3 u by linarith)
  have hinvD : 1 / D2 < 1 / D1 := one_div_lt_one_div_of_lt hD1pos hDlt
  have hdeltaLeD1 : 1 - beta ≤ 1 / D1 := hdeltaLeD2.trans hinvD.le
  have hqheight : Real.rpow (3 : ℝ) (1 / 100000 : ℝ) ≤ u :=
    three_rpow_le_exp11450.trans hu
  have hrecip := hHigh 76.2 4.45 (Real.exp 11450)
    (by norm_num) (by norm_num) (by norm_num) hFord
    (Real.exp_le_exp.mpr (by norm_num : (10650 : ℝ) ≤ 11450))
    startup_ratio startup_loglog 3 (1 : DirichletCharacter ℂ 3)
    u beta (by norm_num) hu hqheight (by
      simpa only [D1, P, F, mul_assoc, Nat.cast_ofNat] using! hdeltaLeD1) hzero
  have hcorr := appendixBFinalCorrection_le_heightMax
    (A := (76.2 : ℝ)) (T₀ := Real.exp 11450) (t := u)
    (by norm_num) (Real.exp_le_exp.mpr (by norm_num : (10650 : ℝ) ≤ 11450)) hu
  have hRhsLeD1 :
      (31.76 + appendixBFinalCorrection 76.2 u) * P +
          17.49 * Real.log 3 ≤ D1 := by
    have hPpos : 0 < P := mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hFpos
    have hm := mul_le_mul_of_nonneg_right hcorr hPpos.le
    dsimp [D1]
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)]
  have hdeltaPos : 0 < 1 - beta := by linarith [hrecip.1]
  have hD2LeInv : D2 ≤ 1 / (1 - beta) := by
    have hi := one_div_le_one_div_of_le hdeltaPos hdeltaLeD2
    simpa only [one_div, inv_inv] using hi
  have hrecip' : 1 / (1 - beta) ≤
      (31.76 + appendixBFinalCorrection 76.2 u) * P +
        17.49 * Real.log 3 := by
    simpa only [P, F, mul_assoc, Nat.cast_ofNat] using! hrecip.2
  exact (not_lt_of_ge (hD2LeInv.trans (hrecip'.trans hRhsLeD1))) hDlt

/-- Sign-symmetric version of the preceding high theorem. -/
theorem high_absolute_three_nonvanishing
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hHigh : AppendixBHighZeroReciprocalEstimate)
    {t beta : ℝ} (ht : Real.exp 11450 ≤ |t|)
    (hbeta : 1 - 1 / khaleWeakDenominatorAbs 3 t ≤ beta) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 3)
      ((beta : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  let u := |t|
  have hpositive : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 3)
      ((beta : ℂ) + (u : ℂ) * Complex.I) ≠ 0 := by
    apply high_positive_three_nonvanishing hFord hHigh ht
    simpa only [u, khaleWeakDenominatorAbs, abs_abs] using hbeta
  by_cases ht0 : 0 ≤ t
  · simpa only [u, abs_of_nonneg ht0] using hpositive
  · have htneg : t < 0 := lt_of_not_ge ht0
    have habs : u = -t := by simp [u, abs_of_neg htneg]
    let s : ℂ := (beta : ℂ) + (t : ℂ) * Complex.I
    have hsone : s ≠ 1 := by
      intro hs
      have him : t = 0 := by simpa [s] using congrArg Complex.im hs
      subst t
      norm_num at ht
      linarith [Real.exp_pos 11450]
    have hconj :=
      MAPDirichletLFunctionConjugationGeneral.LFunction_inv_conj_of_ne_one
        (1 : DirichletCharacter ℂ 3) s hsone
    intro hzero
    apply hpositive
    have hzeroConj : DirichletCharacter.LFunction
        ((1 : DirichletCharacter ℂ 3)⁻¹) (starRingEnd ℂ s) = 0 := by
      rw [hconj, hzero]
      simp
    have hsConj : starRingEnd ℂ s =
        (beta : ℂ) + (u : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [s]
      · simp [s, habs]
    simpa only [inv_one] using (show DirichletCharacter.LFunction
      ((1 : DirichletCharacter ℂ 3)⁻¹)
        ((beta : ℂ) + (u : ℂ) * Complex.I) = 0 by rwa [← hsConj])

/-- The conductor-one high theorem obtained by exact change of level. -/
theorem high_absolute_principal_one_nonvanishing
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hHigh : AppendixBHighZeroReciprocalEstimate)
    {t beta : ℝ} (ht : Real.exp 11450 ≤ |t|)
    (hbeta : 1 - 1 / khaleWeakDenominatorAbs 3 t ≤ beta) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)
      ((beta : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  apply principal_one_nonzero_of_principal_three_nonzero
  · intro hs
    have him := congrArg Complex.im hs
    simp at him
    rw [him] at ht
    norm_num at ht
    linarith [Real.exp_pos 11450]
  · exact high_absolute_three_nonvanishing hFord hHigh ht hbeta

/-- The full principal weak-VK gap, using compactness below the fixed source
cutoff and only the high Khale estimate above it. -/
theorem exists_eventually_principal_weakVK_gap_of_high_estimate
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hHigh : AppendixBHighZeroReciprocalEstimate) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ T : ℝ, T ≤ X →
        ∀ rho ∈ zeroSupport (1 : DirichletCharacter ℂ 1) 0 T,
          c * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤ 1 - rho.re := by
  obtain ⟨cLow, hcLow, hLow⟩ :=
    MAPKhaleAppendixBSource.exists_primitive_principal_preKhale_gap
  let cHigh : ℝ := 1 / (18 + 104)
  let c := min (1 / 5) (min cLow cHigh)
  have hcHigh : 0 < cHigh := by dsimp [cHigh]; norm_num
  have hc : 0 < c := lt_min (by norm_num) (lt_min hcLow hcHigh)
  have hdecay : ∀ᶠ X : ℝ in atTop,
      c * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤ c := by
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with X hX
    have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
    have hlogOne : 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hXpos]
      exact hX
    have hp : Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤ 1 := by
      calc
        Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤ Real.rpow (Real.log X) 0 :=
          Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num)
        _ = 1 := Real.rpow_zero _
    exact (mul_le_mul_of_nonneg_left hp hc.le).trans_eq (mul_one c)
  have hsource := weakGap_le_of_one_div_khaleWeakDenominatorAbs_le
    (1 : ℝ) (by norm_num : (0 : ℝ) ≤ 1)
  have hthree : ∀ᶠ X : ℝ in atTop,
      (3 : ℝ) ≤ Real.rpow (Real.log X) 1 := by
    filter_upwards [eventually_ge_atTop (Real.exp 3)] with X hX
    have hXpos : 0 < X := (Real.exp_pos 3).trans_le hX
    have hlog : 3 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hXpos]
      exact hX
    simpa using hlog
  refine ⟨c, hc, ?_⟩
  filter_upwards [hdecay, hsource, hthree,
      eventually_gt_atTop (Real.exp 1)] with X hdecayX hsourceX hthreeX hX
  intro T hTX rho hrho
  by_cases hbeta : 4 / 5 < rho.re
  · by_cases hheight : |rho.im| < Real.exp (Real.exp (Real.exp 23))
    · have hprim : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
        show (1 : DirichletCharacter ℂ 1).conductor = 1
        rw [DirichletCharacter.conductor_one]
      have hgap := hLow 1 (1 : DirichletCharacter ℂ 1) hprim rfl
        T rho hrho hbeta hheight
      exact hdecayX.trans ((min_le_right (1 / 5) (min cLow cHigh)).trans
        (min_le_left cLow cHigh) |>.trans hgap)
    · have hrect := PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
        (1 : DirichletCharacter ℂ 1) 0 T hrho
      have himX : |rho.im| ≤ X := (abs_le.mpr hrect.2).trans hTX
      have hcut : Real.exp 11450 ≤ |rho.im| := by
        have hexp23 : (24 : ℝ) < Real.exp 23 := by
          convert Real.add_one_lt_exp (x := (23 : ℝ)) (by norm_num) using 1 <;> norm_num
        have hlog : Real.log 11450 ≤ Real.exp 23 :=
          (log_11450_lt.le.trans (by norm_num : (9.346 : ℝ) ≤ 24)).trans hexp23.le
        have h11450 : (11450 : ℝ) ≤ Real.exp (Real.exp 23) := by
          rw [← Real.exp_log (by norm_num : (0 : ℝ) < 11450)]
          exact Real.exp_le_exp.mpr hlog
        exact (Real.exp_le_exp.mpr h11450).trans (le_of_not_gt hheight)
      have hzero : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)
          ((rho.re : ℂ) + (rho.im : ℂ) * Complex.I) = 0 := by
        simpa [Complex.re_add_im] using
          MAPAPPrimitiveRegularLowGap.LFunction_eq_zero_of_mem_zeroSupport
            (1 : DirichletCharacter ℂ 1) hrho
      have hrecip : 1 / khaleWeakDenominatorAbs 3 rho.im ≤ 1 - rho.re := by
        by_contra hn
        have hsigma : 1 - 1 / khaleWeakDenominatorAbs 3 rho.im ≤ rho.re := by linarith
        exact (high_absolute_principal_one_nonvanishing hFord hHigh hcut hsigma) hzero
      have hw := hsourceX 3 rho.im rho.re (by norm_num) hthreeX
        ((show (3 : ℝ) ≤ Real.exp 11450 by
          nlinarith [Real.add_one_lt_exp (x := (11450 : ℝ)) (by norm_num)]).trans hcut)
        himX hrecip
      have hXone : (1 : ℝ) ≤ X :=
        (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hX.le
      exact mul_le_mul_of_nonneg_right
        ((min_le_right (1 / 5) (min cLow cHigh)).trans
          (min_le_right cLow cHigh))
        (Real.rpow_nonneg (Real.log_nonneg hXone) _) |>.trans
          (by norm_num [cHigh] at hw ⊢; exact hw)
  · have hgap : (1 / 5 : ℝ) ≤ 1 - rho.re := by linarith
    exact hdecayX.trans ((min_le_left (1 / 5) (min cLow cHigh)).trans hgap)

/-- Backwards-compatible constructor from the old printed raw interface.  New
source-facing code should use `exists_eventually_principal_weakVK_gap_of_high_estimate`
with the exact-height repaired high estimate. -/
theorem exists_eventually_principal_weakVK_gap_of_ford_raw
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hRaw : MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ T : ℝ, T ≤ X →
        ∀ rho ∈ zeroSupport (1 : DirichletCharacter ℂ 1) 0 T,
          c * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤ 1 - rho.re :=
  exists_eventually_principal_weakVK_gap_of_high_estimate hFord
    (MAPKhaleAppendixBHighZeroFromRaw.appendixBHighZeroReciprocalEstimate_of_raw hRaw)

end
end MAPPrincipalWeakVKZeroGapFromKhaleHigh

#print axioms MAPPrincipalWeakVKZeroGapFromKhaleHigh.high_positive_three_nonvanishing
#print axioms MAPPrincipalWeakVKZeroGapFromKhaleHigh.exists_eventually_principal_weakVK_gap_of_high_estimate
#print axioms MAPPrincipalWeakVKZeroGapFromKhaleHigh.exists_eventually_principal_weakVK_gap_of_ford_raw
