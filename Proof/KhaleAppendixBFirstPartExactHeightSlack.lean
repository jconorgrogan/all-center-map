import KhaleAppendixBEtaAlgebra
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Exact-height repair of Khale Appendix B `(firstpart)`

Khale's Lemma 4.1 is applied at the four ordinates
`gamma, 2*gamma, 3*gamma, 4*gamma`.  The printed proof then replaces all
positive logarithmic errors by their value at `gamma`, which has the wrong
monotonicity.  This module retains the exact four heights, carries their
weighted excess through the deterministic Appendix-B argument, and absorbs it
in the final decimal slack.

The common `4*gamma` envelope is valid but too expensive at the startup
endpoint once the final constant `3.495` (rather than the theorem-statement
constant `3.59`) is used.  The exact weights are essential.  The quantitative
split below proves an excess at most `0.0008 P` for
`10650 <= log gamma <= 20000` and at most `0.0004 P` above `20000`.
-/

namespace MAPKhaleAppendixBFirstPartExactHeightSlack

open MAPKhaleAppendixBEtaAlgebra MAPKhaleAppendixBNumericalCore

noncomputable section

/-- The weighted logarithmic displacement of the three non-base ordinates. -/
def exactHeightWeightedLog : ℝ :=
  10.6825 * Real.log 2 + 4.5 * Real.log 3 + Real.log 4

/-- The literal excess over the false gamma-level replacement, after the
collar has replaced `1-sigma+eta` by `eta` only in the positive power term. -/
def exactHeightCorrection (B eta gamma : ℝ) : ℝ :=
  (1 / (2 * eta)) *
    ((2 / 3 : ℝ) *
        (10.6825 *
            (Real.log (Real.log (2 * gamma)) -
              Real.log (Real.log gamma)) +
          4.5 *
            (Real.log (Real.log (3 * gamma)) -
              Real.log (Real.log gamma)) +
          (Real.log (Real.log (4 * gamma)) -
            Real.log (Real.log gamma))) +
      B * Real.rpow eta (3 / 2 : ℝ) * exactHeightWeightedLog)

private theorem log_two_lt_0694 : Real.log (2 : ℝ) < 0.694 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
  have h := Real.sum_le_exp_of_nonneg (x := (0.694 : ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

private theorem log_three_lt_1099 : Real.log (3 : ℝ) < 1.099 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3)]
  have h := Real.sum_le_exp_of_nonneg (x := (1.099 : ℝ)) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

private theorem log_four_lt_1387 : Real.log (4 : ℝ) < 1.387 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 4)]
  have h := Real.sum_le_exp_of_nonneg (x := (1.387 : ℝ)) (by norm_num) 12
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

private theorem exactHeightWeightedLog_nonneg :
    0 ≤ exactHeightWeightedLog := by
  unfold exactHeightWeightedLog
  positivity

private theorem exactHeightWeightedLog_le :
    exactHeightWeightedLog ≤ 13.746155 := by
  unfold exactHeightWeightedLog
  nlinarith [log_two_lt_0694.le, log_three_lt_1099.le,
    log_four_lt_1387.le]

/-- The exact logarithmic increment at `j*gamma` is at most `log j/log gamma`.
This is the source-facing monotonicity statement missing from the printed
argument. -/
theorem loglog_mul_sub_le_log_div
    {gamma j : ℝ} (hgamma : Real.exp 10650 ≤ gamma)
    (hj : 1 ≤ j) :
    Real.log (Real.log (j * gamma)) - Real.log (Real.log gamma) ≤
      Real.log j / Real.log gamma := by
  have hgammaPos : 0 < gamma := (Real.exp_pos 10650).trans_le hgamma
  have hjPos : 0 < j := zero_lt_one.trans_le hj
  have hlogGamma : (10650 : ℝ) ≤ Real.log gamma := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) hgamma
  have hlogGammaPos : 0 < Real.log gamma := by linarith
  have hlogjNonneg : 0 ≤ Real.log j := Real.log_nonneg hj
  have hlogProd : Real.log (j * gamma) =
      Real.log j + Real.log gamma := by
    rw [Real.log_mul hjPos.ne' hgammaPos.ne']
  have hsumPos : 0 < Real.log j + Real.log gamma :=
    add_pos_of_nonneg_of_pos hlogjNonneg hlogGammaPos
  have hratioPos : 0 <
      (Real.log j + Real.log gamma) / Real.log gamma := by positivity
  have hlogRatio := Real.log_le_sub_one_of_pos hratioPos
  have hratioSub :
      (Real.log j + Real.log gamma) / Real.log gamma - 1 =
        Real.log j / Real.log gamma := by
    field_simp
    ring
  rw [hratioSub] at hlogRatio
  have hdiff :
      Real.log (Real.log j + Real.log gamma) -
          Real.log (Real.log gamma) =
        Real.log ((Real.log j + Real.log gamma) /
          Real.log gamma) := by
    rw [Real.log_div hsumPos.ne' hlogGammaPos.ne']
  rw [hlogProd]
  linarith

/-- Normalized exact four-height loss.  The coarse expression on the right is
chosen so all remaining endpoint arithmetic is rational. -/
theorem exactHeightCorrection_le_coarse
    {B gamma : ℝ} (hB : 0 < B)
    (hgamma : Real.exp 10650 ≤ gamma) :
    exactHeightCorrection B (khaleEta B gamma) gamma ≤
      (5.68 / Real.log gamma) *
        ((2 / 3 : ℝ) / Real.log (Real.log gamma) + 4 / 3) *
        (Real.rpow B (2 / 3 : ℝ) *
          Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)) := by
  let L : ℝ := Real.log gamma
  let ell : ℝ := Real.log (Real.log gamma)
  let eta : ℝ := khaleEta B gamma
  let M : ℝ := Real.rpow B (2 / 3 : ℝ) *
    Real.rpow (L / ell) (2 / 3 : ℝ)
  let P : ℝ := Real.rpow B (2 / 3 : ℝ) *
    Real.rpow L (2 / 3 : ℝ) * Real.rpow ell (1 / 3 : ℝ)
  have hLlower : (10650 : ℝ) ≤ L := by
    dsimp [L]
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) hgamma
  have hL : 0 < L := by linarith
  have hell : 0 < ell := by
    dsimp [ell]
    exact Real.log_pos (by linarith)
  have heta : 0 < eta := by
    dsimp [eta]
    exact khaleEta_pos hB (by simpa only [L] using hL)
      (by simpa only [ell] using hell)
  have hM : 0 < M := by dsimp [M]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have h2 := loglog_mul_sub_le_log_div hgamma
    (show (1 : ℝ) ≤ 2 by norm_num)
  have h3 := loglog_mul_sub_le_log_div hgamma
    (show (1 : ℝ) ≤ 3 by norm_num)
  have h4 := loglog_mul_sub_le_log_div hgamma
    (show (1 : ℝ) ≤ 4 by norm_num)
  have hlogPart :
      10.6825 *
          (Real.log (Real.log (2 * gamma)) - Real.log (Real.log gamma)) +
        4.5 *
          (Real.log (Real.log (3 * gamma)) - Real.log (Real.log gamma)) +
        (Real.log (Real.log (4 * gamma)) - Real.log (Real.log gamma)) ≤
      exactHeightWeightedLog / L := by
    have hL' : Real.log gamma = L := rfl
    rw [hL'] at h2 h3 h4
    unfold exactHeightWeightedLog
    field_simp [hL.ne'] at h2 h3 h4 ⊢
    nlinarith
  have hinside :
      (2 / 3 : ℝ) *
          (10.6825 *
              (Real.log (Real.log (2 * gamma)) - Real.log (Real.log gamma)) +
            4.5 *
              (Real.log (Real.log (3 * gamma)) - Real.log (Real.log gamma)) +
            (Real.log (Real.log (4 * gamma)) - Real.log (Real.log gamma))) +
        B * Real.rpow eta (3 / 2 : ℝ) * exactHeightWeightedLog ≤
      exactHeightWeightedLog *
        ((2 / 3 : ℝ) / L + (4 / 3 : ℝ) * ell / L) := by
    have hlogScaled := mul_le_mul_of_nonneg_left hlogPart
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
    have hetaId :
        B * Real.rpow eta (3 / 2 : ℝ) * L = (4 / 3 : ℝ) * ell := by
      simpa only [eta, L, ell] using
        B_mul_eta_three_halves_mul_log hB
          (by simpa only [L] using hL)
          (by simpa only [ell] using hell)
    have hetaTerm :
        B * Real.rpow eta (3 / 2 : ℝ) = (4 / 3 : ℝ) * ell / L := by
      apply (eq_div_iff hL.ne').2
      simpa only [mul_assoc] using hetaId
    rw [hetaTerm]
    calc
      (2 / 3 : ℝ) *
            (10.6825 *
                (Real.log (Real.log (2 * gamma)) - Real.log (Real.log gamma)) +
              4.5 *
                (Real.log (Real.log (3 * gamma)) - Real.log (Real.log gamma)) +
              (Real.log (Real.log (4 * gamma)) - Real.log (Real.log gamma))) +
          ((4 / 3 : ℝ) * ell / L) * exactHeightWeightedLog ≤
        (2 / 3 : ℝ) * (exactHeightWeightedLog / L) +
          ((4 / 3 : ℝ) * ell / L) * exactHeightWeightedLog :=
            by
              simpa only [add_comm] using
                add_le_add_right hlogScaled
                  (((4 / 3 : ℝ) * ell / L) * exactHeightWeightedLog)
      _ = exactHeightWeightedLog *
          ((2 / 3 : ℝ) / L + (4 / 3 : ℝ) * ell / L) := by ring
  have hinvEta : 1 / eta = sourceScale * M := by
    simpa only [eta, M, L, ell, khaleInvEtaScale, mul_assoc] using
      one_div_khaleEta hB (by simpa only [L] using hL)
        (by simpa only [ell] using hell)
  have hMell : M * ell = P := by
    have hr := ratio_two_thirds_mul_loglog
      (by simpa only [L] using hL) (by simpa only [ell] using hell)
    calc
      M * ell = Real.rpow B (2 / 3 : ℝ) *
          (Real.rpow (L / ell) (2 / 3 : ℝ) * ell) := by
            dsimp [M]; ring
      _ = Real.rpow B (2 / 3 : ℝ) *
          (Real.rpow L (2 / 3 : ℝ) * Real.rpow ell (1 / 3 : ℝ)) := by
            rw [show Real.rpow (L / ell) (2 / 3 : ℝ) * ell =
                Real.rpow L (2 / 3 : ℝ) * Real.rpow ell (1 / 3 : ℝ) by
              simpa only [L, ell] using hr]
      _ = P := by dsimp [P]; ring
  have hscaleWeight : sourceScale * exactHeightWeightedLog / 2 ≤ 5.68 := by
    have hs := sourceScale_upper
    have hw := exactHeightWeightedLog_le
    have hs0 : 0 ≤ sourceScale := Real.rpow_nonneg (by norm_num) _
    have hw0 := exactHeightWeightedLog_nonneg
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hinside
    (show 0 ≤ 1 / (2 * eta) by positivity)
  have hinvEtaTwo : 1 / (2 * eta) = sourceScale * M / 2 := by
    calc
      1 / (2 * eta) = (1 / eta) / 2 := by field_simp [heta.ne']
      _ = sourceScale * M / 2 := by rw [hinvEta]
  have hrewrite :
      (1 / (2 * eta)) * exactHeightWeightedLog *
          ((2 / 3 : ℝ) / L + (4 / 3 : ℝ) * ell / L) =
        (sourceScale * exactHeightWeightedLog / 2) *
          (M * ell) * (1 / L) *
          ((2 / 3 : ℝ) / ell + 4 / 3) := by
    rw [hinvEtaTwo]
    field_simp [hL.ne', hell.ne']
  have hscaled' :
      (1 / (2 * eta)) *
          ((2 / 3 : ℝ) *
              (10.6825 *
                  (Real.log (Real.log (2 * gamma)) - Real.log (Real.log gamma)) +
                4.5 *
                  (Real.log (Real.log (3 * gamma)) - Real.log (Real.log gamma)) +
                (Real.log (Real.log (4 * gamma)) - Real.log (Real.log gamma))) +
            B * Real.rpow eta (3 / 2 : ℝ) * exactHeightWeightedLog) ≤
        (1 / (2 * eta)) * exactHeightWeightedLog *
          ((2 / 3 : ℝ) / L + (4 / 3 : ℝ) * ell / L) := by
    calc
      _ ≤ (1 / (2 * eta)) *
          (exactHeightWeightedLog *
            ((2 / 3 : ℝ) / L + (4 / 3 : ℝ) * ell / L)) := hscaled
      _ = _ := by ring
  rw [hrewrite, hMell] at hscaled'
  have hfactorNonneg :
      0 ≤ P * (1 / L) * ((2 / 3 : ℝ) / ell + 4 / 3) := by
    positivity
  have hcoefMul := mul_le_mul_of_nonneg_right hscaleWeight hfactorNonneg
  have hcoefMul' :
      (sourceScale * exactHeightWeightedLog / 2) * P * (1 / L) *
          ((2 / 3 : ℝ) / ell + 4 / 3) ≤
        5.68 * P * (1 / L) * ((2 / 3 : ℝ) / ell + 4 / 3) := by
    simpa only [mul_assoc] using hcoefMul
  have hfinal := hscaled'.trans hcoefMul'
  change exactHeightCorrection B eta gamma ≤
    (5.68 / L) * ((2 / 3 : ℝ) / ell + 4 / 3) * P
  rw [show (5.68 / L) * ((2 / 3 : ℝ) / ell + 4 / 3) * P =
      5.68 * P * (1 / L) * ((2 / 3 : ℝ) / ell + 4 / 3) by ring]
  unfold exactHeightCorrection
  exact hfinal

/-- Low/startup half of the requested `L=20000` split. -/
theorem exactHeightCorrection_le_low
    {B gamma : ℝ} (hB : 0 < B)
    (hgamma : Real.exp 10650 ≤ gamma)
    (hLtop : Real.log gamma ≤ 20000) :
    exactHeightCorrection B (khaleEta B gamma) gamma ≤
      0.0008 *
        (Real.rpow B (2 / 3 : ℝ) *
          Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)) := by
  have hc := exactHeightCorrection_le_coarse hB hgamma
  have hL : (10650 : ℝ) ≤ Real.log gamma := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) hgamma
  have hell : (9 : ℝ) ≤ Real.log (Real.log gamma) := by
    rw [← Real.log_exp 9]
    apply Real.log_le_log (Real.exp_pos 9)
    have he : Real.exp 9 < (10650 : ℝ) := by
      rw [show Real.exp (9 : ℝ) = Real.exp 1 ^ (9 : ℕ) by
        simpa using (Real.exp_one_pow 9).symm]
      calc
        Real.exp 1 ^ (9 : ℕ) < (2.7182818286 : ℝ) ^ (9 : ℕ) := by
          gcongr
          exact Real.exp_one_lt_d9
        _ < 10650 := by norm_num
    linarith
  let P : ℝ := Real.rpow B (2 / 3 : ℝ) *
    Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
    Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hscalar :
      (5.68 / Real.log gamma) *
          ((2 / 3 : ℝ) / Real.log (Real.log gamma) + 4 / 3) ≤
        0.0008 := by
    have hLpos : 0 < Real.log gamma := by linarith
    have hellpos : 0 < Real.log (Real.log gamma) := by linarith
    have hleft : 5.68 / Real.log gamma ≤ 5.68 / 10650 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
    have hright :
        (2 / 3 : ℝ) / Real.log (Real.log gamma) + 4 / 3 ≤
          (2 / 3 : ℝ) / 9 + 4 / 3 := by
      gcongr
    have hleft0 : 0 ≤ 5.68 / Real.log gamma := by positivity
    have hright0 : 0 ≤ (2 / 3 : ℝ) / 9 + 4 / 3 := by norm_num
    calc
      (5.68 / Real.log gamma) *
          ((2 / 3 : ℝ) / Real.log (Real.log gamma) + 4 / 3) ≤
        (5.68 / 10650) * ((2 / 3 : ℝ) / 9 + 4 / 3) :=
          mul_le_mul hleft hright (by positivity) (by norm_num)
      _ ≤ 0.0008 := by norm_num
  have hm := mul_le_mul_of_nonneg_right hscalar hP
  exact hc.trans (by simpa only [P, mul_assoc] using hm)

/-- High half of the requested `L=20000` split. -/
theorem exactHeightCorrection_le_high
    {B gamma : ℝ} (hB : 0 < B)
    (hgamma : Real.exp 10650 ≤ gamma)
    (hL : 20000 ≤ Real.log gamma) :
    exactHeightCorrection B (khaleEta B gamma) gamma ≤
      0.0004 *
        (Real.rpow B (2 / 3 : ℝ) *
          Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)) := by
  have hc := exactHeightCorrection_le_coarse hB hgamma
  have hell : (9 : ℝ) ≤ Real.log (Real.log gamma) := by
    rw [← Real.log_exp 9]
    apply Real.log_le_log (Real.exp_pos 9)
    have he : Real.exp 9 < (10650 : ℝ) := by
      rw [show Real.exp (9 : ℝ) = Real.exp 1 ^ (9 : ℕ) by
        simpa using (Real.exp_one_pow 9).symm]
      calc
        Real.exp 1 ^ (9 : ℕ) < (2.7182818286 : ℝ) ^ (9 : ℕ) := by
          gcongr
          exact Real.exp_one_lt_d9
        _ < 10650 := by norm_num
    have hbase : (10650 : ℝ) ≤ Real.log gamma := by linarith
    linarith
  let P : ℝ := Real.rpow B (2 / 3 : ℝ) *
    Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
    Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hLpos : 0 < Real.log gamma := by linarith
  have hellpos : 0 < Real.log (Real.log gamma) := by linarith
  have hscalar :
      (5.68 / Real.log gamma) *
          ((2 / 3 : ℝ) / Real.log (Real.log gamma) + 4 / 3) ≤
        0.0004 := by
    have hleft : 5.68 / Real.log gamma ≤ 5.68 / 20000 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
    have hright :
        (2 / 3 : ℝ) / Real.log (Real.log gamma) + 4 / 3 ≤
          (2 / 3 : ℝ) / 9 + 4 / 3 := by
      gcongr
    have hleft0 : 0 ≤ 5.68 / Real.log gamma := by positivity
    calc
      (5.68 / Real.log gamma) *
          ((2 / 3 : ℝ) / Real.log (Real.log gamma) + 4 / 3) ≤
        (5.68 / 20000) * ((2 / 3 : ℝ) / 9 + 4 / 3) :=
          mul_le_mul hleft hright (by positivity) (by norm_num)
      _ ≤ 0.0004 := by norm_num
  have hm := mul_le_mul_of_nonneg_right hscalar hP
  exact hc.trans (by simpa only [P, mul_assoc] using hm)

/-- Uniform startup bound used by the repaired final Appendix-B rounding.
The split is retained in the preceding two lemmas for auditability; the weaker
`0.0008` coefficient is valid throughout the whole source range. -/
theorem exactHeightCorrection_le_point0008
    {B gamma : ℝ} (hB : 0 < B)
    (hgamma : Real.exp 10650 ≤ gamma) :
    exactHeightCorrection B (khaleEta B gamma) gamma ≤
      0.0008 *
        (Real.rpow B (2 / 3 : ℝ) *
          Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)) := by
  rcases le_total (Real.log gamma) 20000 with hLow | hHigh
  · exact exactHeightCorrection_le_low hB hgamma hLow
  · have h := exactHeightCorrection_le_high hB hgamma hHigh
    have hLlower : (10650 : ℝ) ≤ Real.log gamma := by
      rw [← Real.log_exp 10650]
      exact Real.log_le_log (Real.exp_pos 10650) hgamma
    have hL : 0 ≤ Real.log gamma := by linarith
    have hell : 0 ≤ Real.log (Real.log gamma) := by
      exact (Real.log_pos (by linarith [hLlower])).le
    have hP : 0 ≤
        Real.rpow B (2 / 3 : ℝ) *
          Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ) := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hB.le _)
          (Real.rpow_nonneg hL _))
        (Real.rpow_nonneg hell _)
    nlinarith

end
end MAPKhaleAppendixBFirstPartExactHeightSlack

#print axioms MAPKhaleAppendixBFirstPartExactHeightSlack.loglog_mul_sub_le_log_div
#print axioms MAPKhaleAppendixBFirstPartExactHeightSlack.exactHeightCorrection_le_low
#print axioms MAPKhaleAppendixBFirstPartExactHeightSlack.exactHeightCorrection_le_high
#print axioms MAPKhaleAppendixBFirstPartExactHeightSlack.exactHeightCorrection_le_point0008
