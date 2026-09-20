import KhaleAppendixB1FinalReduction
import KhaleAppendixBMcCurleyHeight

/-!
# Source-faithful high-zero input for Khale Appendix B.1

This module makes the preliminary McCurley step explicit.  The analytic
reciprocal estimate is required only in the range in which Khale applies its
Lemmas 4.1 and 5.1: `gamma ≥ q^(1/100000)`.
-/

namespace MAPKhaleAppendixB1HighZeroReduction

open MAPKhaleAppendixBSource MAPKhaleAppendixB1FinalReduction
open MAPKhaleAppendixBMcCurleyHeight

noncomputable section

/-- The reciprocal estimate after the first paragraph of the proof of B.1.
The extra height hypothesis is the literal one supplied by McCurley's theorem.
-/
abbrev AppendixBHighZeroReciprocalEstimate : Prop :=
  ∀ (A B T₀ : ℝ),
    0 < A → 0 < B → B ≤ 4.45 →
    FordHurwitzEquation12 A B →
    Real.exp 10650 ≤ T₀ →
    5110.6 / B ≤ Real.log T₀ / Real.log (Real.log T₀) →
    183 / B ^ 2 ≤ Real.log (Real.log T₀) →
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
        (gamma beta : ℝ),
      3 ≤ q → T₀ ≤ gamma →
      Real.rpow (q : ℝ) (1 / 100000 : ℝ) ≤ gamma →
      1 - beta ≤ 1 /
        (18 * Real.log q + appendixBHeightCoefficient A T₀ *
          Real.rpow B (2 / 3 : ℝ) *
          Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)) →
      DirichletCharacter.LFunction chi
          ((beta : ℂ) + (gamma : ℂ) * Complex.I) = 0 →
      beta < 1 ∧
      1 / (1 - beta) ≤
        (31.76 + appendixBFinalCorrection A gamma) *
            Real.rpow B (2 / 3 : ℝ) *
            Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
            Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ) +
          17.49 * Real.log q

/-- The deterministic final contradiction in Appendix B.1, with the
`q^(1/100000) <= gamma` hypothesis kept explicit.  This is the exact
high-zero statement available before McCurley's height reduction. -/
theorem nonvanishing_of_highZeroReciprocalEstimate
    (hHigh : AppendixBHighZeroReciprocalEstimate)
    {A B T₀ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hBtop : B ≤ 4.45)
    (hFord : FordHurwitzEquation12 A B)
    (hT₀ : Real.exp 10650 ≤ T₀)
    (hratio : 5110.6 / B ≤ Real.log T₀ / Real.log (Real.log T₀))
    (hloglog : 183 / B ^ 2 ≤ Real.log (Real.log T₀))
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {gamma beta : ℝ}
    (hq : 3 ≤ q) (hgamma : T₀ ≤ gamma)
    (hqheight : Real.rpow (q : ℝ) (1 / 100000 : ℝ) ≤ gamma)
    (hboundary : 1 - 1 /
      (18 * Real.log q + appendixBHeightCoefficient A T₀ *
        Real.rpow B (2 / 3 : ℝ) *
        Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
        Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)) < beta) :
    DirichletCharacter.LFunction chi
        ((beta : ℂ) + (gamma : ℂ) * Complex.I) ≠ 0 := by
  intro hzero
  have hrecip := hHigh A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q chi gamma beta hq hgamma hqheight (by linarith [hboundary]) hzero
  let P : ℝ :=
    Real.rpow B (2 / 3 : ℝ) *
      Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
      Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)
  let D : ℝ := 18 * Real.log q + appendixBHeightCoefficient A T₀ * P
  have hgammaPos : 0 < gamma :=
    (Real.exp_pos 10650).trans_le (hT₀.trans hgamma)
  have hloggamma : (10650 : ℝ) ≤ Real.log gamma := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) (hT₀.trans hgamma)
  have hloggammaPos : 0 < Real.log gamma := by linarith
  have hlogloggammaPos : 0 < Real.log (Real.log gamma) := by
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 10650) hloggamma
    exact (Real.log_pos (by norm_num : (1 : ℝ) < 10650)).trans_le hmono
  have hPpos : 0 < P := by
    dsimp only [P]
    exact mul_pos
      (mul_pos (Real.rpow_pos_of_pos hB _)
        (Real.rpow_pos_of_pos hloggammaPos _))
      (Real.rpow_pos_of_pos hlogloggammaPos _)
  have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogqPos : 0 < Real.log q :=
    Real.log_pos ((by norm_num : (1 : ℝ) < 3).trans_le hqReal)
  have hcoeffPos : 0 < appendixBHeightCoefficient A T₀ := by
    unfold appendixBHeightCoefficient
    have : (0 : ℝ) ≤ max (sSup (appendixBCorrection A '' Set.Ici T₀)) 0 :=
      le_max_right _ _
    linarith
  have hDpos : 0 < D := by
    dsimp only [D]
    positivity
  have hcorr := appendixBFinalCorrection_le_heightMax hA hT₀ hgamma
  have hRhsLeD :
      (31.76 + appendixBFinalCorrection A gamma) * P +
          17.49 * Real.log q ≤ D := by
    dsimp only [D]
    have hmul := mul_le_mul_of_nonneg_right hcorr hPpos.le
    nlinarith
  have hrecip' : 1 / (1 - beta) ≤
      (31.76 + appendixBFinalCorrection A gamma) * P +
        17.49 * Real.log q := by
    simpa only [P, mul_assoc] using hrecip.2
  have hdeltaPos : 0 < 1 - beta := by linarith [hrecip.1]
  have hboundaryD : 1 - 1 / D < beta := by
    simpa only [D, P, mul_assoc] using hboundary
  have hdeltaLt : 1 - beta < 1 / D := by linarith
  have hDltRecip : D < 1 / (1 - beta) := by
    have hinv := one_div_lt_one_div_of_lt hdeltaPos hdeltaLt
    simpa only [one_div, inv_inv] using hinv
  exact (not_lt_of_ge (hrecip'.trans hRhsLeD)) hDltRecip

private theorem coarse_eighteen_log_gap
    {A B T₀ : ℝ} (hB : 0 < B)
    {q : ℕ} {gamma beta : ℝ} (hq : 3 ≤ q)
    (hT₀ : Real.exp 10650 ≤ T₀) (hgamma : T₀ ≤ gamma)
    (hgap : 1 - beta ≤ 1 /
      (18 * Real.log q + appendixBHeightCoefficient A T₀ *
        Real.rpow B (2 / 3 : ℝ) *
        Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
        Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ))) :
    1 - beta ≤ 1 / (18 * Real.log q) := by
  let P : ℝ := Real.rpow B (2 / 3 : ℝ) *
    Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
    Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)
  have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogqPos : 0 < Real.log q :=
    Real.log_pos ((by norm_num : (1 : ℝ) < 3).trans_le hqReal)
  have hgammaPos : 0 < gamma :=
    (Real.exp_pos 10650).trans_le (hT₀.trans hgamma)
  have hloggamma : (10650 : ℝ) ≤ Real.log gamma := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) (hT₀.trans hgamma)
  have hloggammaPos : 0 < Real.log gamma := by linarith
  have hlogloggammaPos : 0 < Real.log (Real.log gamma) := by
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 10650) hloggamma
    exact Real.log_pos (by norm_num : (1 : ℝ) < 10650) |>.trans_le hmono
  have hPpos : 0 < P := by
    dsimp [P]
    exact mul_pos
      (mul_pos (Real.rpow_pos_of_pos hB _)
        (Real.rpow_pos_of_pos hloggammaPos _))
      (Real.rpow_pos_of_pos hlogloggammaPos _)
  have hcoeffNonneg : 0 ≤ appendixBHeightCoefficient A T₀ := by
    unfold appendixBHeightCoefficient
    have : (0 : ℝ) ≤ max (sSup (appendixBCorrection A '' Set.Ici T₀)) 0 :=
      le_max_right _ _
    linarith
  have hbasePos : 0 < 18 * Real.log q := mul_pos (by norm_num) hlogqPos
  have hdenGe : 18 * Real.log q ≤
      18 * Real.log q + appendixBHeightCoefficient A T₀ * P := by
    exact le_add_of_nonneg_right (mul_nonneg hcoeffNonneg hPpos.le)
  have hinv : 1 /
      (18 * Real.log q + appendixBHeightCoefficient A T₀ * P) ≤
      1 / (18 * Real.log q) :=
    one_div_le_one_div_of_le hbasePos hdenGe
  have hgap' : 1 - beta ≤ 1 /
      (18 * Real.log q + appendixBHeightCoefficient A T₀ * P) := by
    simpa only [P, mul_assoc] using hgap
  exact hgap'.trans hinv

/-- McCurley's real-exception theorem plus the high-zero estimate yields the
exact final reciprocal proposition consumed by the deterministic B.1 weld. -/
theorem finalReciprocalEstimate_of_highZero_and_mccurley
    (hMcCurley : McCurleyTheorem11RealException)
    (hHigh : AppendixBHighZeroReciprocalEstimate) :
    AppendixBFinalReciprocalZeroEstimate := by
  intro A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q _inst chi gamma beta hq hgamma hgap hzero
  have h18 := coarse_eighteen_log_gap hB hq hT₀ hgamma hgap
  have hqheight := q_rpow_one_over_100000_le_ordinate_of_zero
    hMcCurley chi hq (hT₀.trans hgamma) h18 hzero
  exact hHigh A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q chi gamma beta hq hgamma hqheight hgap hzero

/-- Combined source-faithful constructor for Appendix-B Theorem B.1. -/
theorem appendixBTheoremB1_of_highZero_and_mccurley
    (hMcCurley : McCurleyTheorem11RealException)
    (hHigh : AppendixBHighZeroReciprocalEstimate) :
    AppendixBTheoremB1 :=
  appendixBTheoremB1_of_finalReciprocalEstimate
    (finalReciprocalEstimate_of_highZero_and_mccurley hMcCurley hHigh)

end
end MAPKhaleAppendixB1HighZeroReduction

#print axioms MAPKhaleAppendixB1HighZeroReduction.appendixBTheoremB1_of_highZero_and_mccurley
