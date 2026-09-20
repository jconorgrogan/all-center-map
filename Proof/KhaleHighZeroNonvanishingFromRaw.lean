import KhaleAppendixBHighZeroFromRaw
import KhaleAppendixBHeightCoefficientBound
import DirichletLFunctionConjugationGeneral

/-!
# Khale high-zero nonvanishing before the McCurley height reduction

This module isolates the part of Appendix B that is actually needed in the
polylogarithmic-conductor regular-high sector.  The auxiliary hypothesis
`q^(1/100000) <= |t|` is retained literally, so neither McCurley's bounded
height theorem nor Corollary B.2 is used.
-/

namespace MAPKhaleHighZeroNonvanishingFromRaw

set_option maxHeartbeats 4000000

open MAPKhaleAppendixBSource MAPKhaleWeakVKApplication
open MAPKhaleAppendixBHeightCoefficientBound
open MAPKhaleAppendixB1HighZeroReduction MAPKhaleAppendixB1FinalReduction

noncomputable section

private theorem startup_ratio :
    (5110.6 : ℝ) / 4.45 ≤
      Real.log (Real.exp 11450) /
        Real.log (Real.log (Real.exp 11450)) := by
  rw [Real.log_exp]
  have hlogpos : 0 < Real.log (11450 : ℝ) :=
    (by norm_num : (0 : ℝ) < 9.345).trans log_11450_gt
  apply (le_div_iff₀ hlogpos).2
  nlinarith [log_11450_lt]

private theorem startup_loglog :
    (183 : ℝ) / (4.45 : ℝ) ^ 2 ≤
      Real.log (Real.log (Real.exp 11450)) := by
  rw [Real.log_exp]
  have h := log_11450_gt
  norm_num at h ⊢
  linarith

/-- The literal high-ordinate, positive-sign consequence of Khale's B.1
calculation.  The McCurley height alternative remains an explicit hypothesis
and is not discharged here. -/
theorem high_positive_nonvanishing_of_high_estimate
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hHigh : AppendixBHighZeroReciprocalEstimate)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {u sigma : ℝ} (hq : 3 ≤ q) (hu : Real.exp 11450 ≤ u)
    (hqheight : Real.rpow (q : ℝ) (1 / 100000 : ℝ) ≤ u)
    (hsigma : 1 - 1 / khaleWeakDenominatorAbs q u ≤ sigma) :
    DirichletCharacter.LFunction chi
      ((sigma : ℂ) + (u : ℂ) * Complex.I) ≠ 0 := by
  let F : ℝ := Real.rpow (Real.log u) (2 / 3 : ℝ) *
    Real.rpow (Real.log (Real.log u)) (1 / 3 : ℝ)
  let D₁ : ℝ := 18 * Real.log q +
    appendixBHeightCoefficient 76.2 (Real.exp 11450) *
      Real.rpow 4.45 (2 / 3 : ℝ) * F
  let D₂ : ℝ := 18 * Real.log q + 104 * F
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
  have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogqPos : 0 < Real.log q :=
    Real.log_pos ((by norm_num : (1 : ℝ) < 3).trans_le hqReal)
  have hcoeffNonneg :
      0 ≤ appendixBHeightCoefficient 76.2 (Real.exp 11450) := by
    unfold appendixBHeightCoefficient
    positivity
  have hD₁pos : 0 < D₁ := by
    dsimp [D₁]
    have hterm : 0 ≤
        appendixBHeightCoefficient 76.2 (Real.exp 11450) *
          Real.rpow 4.45 (2 / 3 : ℝ) * F :=
      mul_nonneg
        (mul_nonneg hcoeffNonneg (Real.rpow_nonneg (by norm_num) _)) hFpos.le
    exact add_pos_of_pos_of_nonneg (mul_pos (by norm_num) hlogqPos) hterm
  have hDlt : D₁ < D₂ := by
    dsimp [D₁, D₂]
    have hc := appendixBHeightCoefficient_mul_rpow_lt_104
    simpa only [add_comm] using
      add_lt_add_left (mul_lt_mul_of_pos_right hc hFpos) (18 * Real.log q)
  have hboundary : 1 - 1 / D₁ < sigma := by
    have hinv : 1 / D₂ < 1 / D₁ := one_div_lt_one_div_of_lt hD₁pos hDlt
    have habsu : |u| = u := abs_of_pos huPos
    have hsigmaD₂ : 1 - 1 / D₂ ≤ sigma := by
      simpa only [D₂, F, khaleWeakDenominatorAbs, khaleWeakDenominator,
        habsu, mul_assoc] using hsigma
    linarith
  apply nonvanishing_of_highZeroReciprocalEstimate hHigh
    (A := 76.2) (B := 4.45) (T₀ := Real.exp 11450)
    (by norm_num) (by norm_num) (by norm_num) hFord
    (Real.exp_le_exp.mpr (by norm_num : (10650 : ℝ) ≤ 11450))
    startup_ratio startup_loglog (q := q) chi (gamma := u) (beta := sigma)
    hq hu hqheight
  dsimp [D₁, F] at hboundary ⊢
  simp only [mul_assoc] at hboundary ⊢
  exact hboundary

/-- Sign-symmetric high-zero nonvanishing, still retaining the literal
`q^(1/100000) <= |t|` condition. -/
theorem high_absolute_nonvanishing_of_high_estimate
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hHigh : AppendixBHighZeroReciprocalEstimate)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {t sigma : ℝ} (hq : 3 ≤ q) (ht : Real.exp 11450 ≤ |t|)
    (hqheight : Real.rpow (q : ℝ) (1 / 100000 : ℝ) ≤ |t|)
    (hsigma : 1 - 1 / khaleWeakDenominatorAbs q t ≤ sigma) :
    DirichletCharacter.LFunction chi
      ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  let u := |t|
  have hpositive (psi : DirichletCharacter ℂ q) :
      DirichletCharacter.LFunction psi
        ((sigma : ℂ) + (u : ℂ) * Complex.I) ≠ 0 := by
    apply high_positive_nonvanishing_of_high_estimate hFord hHigh psi hq ht
      hqheight
    simpa only [u, khaleWeakDenominatorAbs, abs_abs] using hsigma
  by_cases ht0 : 0 ≤ t
  · have habs : |t| = t := abs_of_nonneg ht0
    simpa only [u, habs] using hpositive chi
  · have htneg : t < 0 := lt_of_not_ge ht0
    have habs : u = -t := by simp [u, abs_of_neg htneg]
    let s : ℂ := (sigma : ℂ) + (t : ℂ) * Complex.I
    have htne : t ≠ 0 := ne_of_lt htneg
    have hsone : s ≠ 1 := by
      intro hs
      have him : t = 0 := by simpa [s] using congrArg Complex.im hs
      exact htne him
    have hconj :=
      MAPDirichletLFunctionConjugationGeneral.LFunction_inv_conj_of_ne_one
        chi s hsone
    intro hzero
    apply hpositive chi⁻¹
    have hzeroConj :
        DirichletCharacter.LFunction chi⁻¹ (starRingEnd ℂ s) = 0 := by
      rw [hconj, hzero]
      simp
    have hsConj : starRingEnd ℂ s =
        (sigma : ℂ) + (u : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [s]
      · simp [s, habs]
    rwa [hsConj] at hzeroConj

end

end MAPKhaleHighZeroNonvanishingFromRaw

#print axioms MAPKhaleHighZeroNonvanishingFromRaw.high_positive_nonvanishing_of_high_estimate
#print axioms MAPKhaleHighZeroNonvanishingFromRaw.high_absolute_nonvanishing_of_high_estimate
