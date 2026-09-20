import BHPShiftedHolderReduction
import RamachandraTheorem6ShiftedStripSource

/-!
# Corrected BHP Holder/Ramachandra weld

This file joins the deterministic positive-offset Holder reduction to the
literal shifted fourth moment in Ramachandra's Theorem 6.  The Perron window
is enlarged to `2T`; consequently Holder sees the fourth moment through
height `4T`.  This avoids the endpoint pole on the horizontal side of the
height-`T` BHP rectangle.

The analytic content of Ramachandra's theorem remains the explicit premise
`RamachandraTheorem6K2Source`.  No version of the misnormalised printed BHP
quantity `J` is assumed here.
-/

namespace MAPBHPShiftedRamachandraWeld

open scoped BigOperators
open MAPBHPCorrectedPerronKernel
open MAPBHPShiftedHolderReduction
open MAPMRTLemma211AllCharacterSource
open MAPMRTCorollary25Minkowski
open RamachandraTheorem6ShiftedStripSource

noncomputable section

private theorem harmonic_nonneg_real (n : ℕ) :
    (0 : ℝ) ≤ (harmonic n : ℝ) := by
  norm_cast
  unfold harmonic
  positivity

/-- The two fourth-moment interfaces are definitionally identical. -/
theorem allCharacterShiftedLineFourthIntegral_eq_source
    (q : ℕ) [NeZero q] (U x0 : ℝ) :
    allCharacterShiftedLineFourthIntegral q
        (canonicalRamachandraOffset x0) U =
      allCharacterShiftedStripFourthIntegral q U
        ((1 / 2 : ℝ) + canonicalRamachandraOffset x0) := by
  rfl

/-- At ambient scale at least two, the robust Ramachandra offset avoids the
pole line `delta = 1/2`. -/
theorem canonicalRamachandraOffset_ne_half
    {x0 : ℝ} (hx0 : 2 ≤ x0) :
    canonicalRamachandraOffset x0 ≠ (1 / 2 : ℝ) := by
  have hx0pos : 0 < x0 := by linarith
  have hlog2half : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2le : Real.log 2 ≤ Real.log x0 :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hx0pos hx0
  have hlogx : 0 < Real.log x0 := Real.log_pos (by linarith)
  have hden : 0 < 400 * Real.log x0 := mul_pos (by norm_num) hlogx
  have hoffset : canonicalRamachandraOffset x0 < (1 / 2 : ℝ) := by
    unfold canonicalRamachandraOffset
    rw [inv_lt_iff_one_lt_mul₀ hden]
    nlinarith
  exact ne_of_lt hoffset

/-- Holder, same-character one-spacing, and the endpoint-safe specialization
of Ramachandra Theorem 6.  The exact Holder kernel is retained so this theorem
introduces no extra logarithmic comparison.

The convolution window is `2T`; this is why the source moment occurs at
height `4T` and why the canonical offset has denominator `400 log x0`. -/
theorem canonicalShiftedPerronConvolutionFourth_le_exactKernel
    (hRamachandra : RamachandraTheorem6K2Source)
    {q : ℕ} [NeZero q]
    {S : Finset (DirichletCharacter ℂ q × ℝ)}
    {T x0 K : ℝ}
    (hT : 1 ≤ T) (hx0 : 2 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hTx : T ≤ x0)
    (hK : 0 ≤ K) (hthreshold : K ≤ Real.log (Real.log x0))
    (hqpoly : (q : ℝ) ≤ (Real.log x0) ^ K)
    (hheight : ∀ z ∈ S, |z.2| ≤ T)
    (hsep : SameCharacterOneSeparated S) :
    ∃ C₆ : ℝ, 0 < C₆ ∧
      (∑ z ∈ S,
        perronConvolution
          (shiftedCriticalLineLNorm z.1
            (canonicalRamachandraOffset x0)) (2 * T) z.2 ^ 4) ≤
        ((∫ u in (-(2 * T))..(2 * T), perronWeight u) ^ 3 *
          (4 * (harmonic (⌊4 * (2 * T)⌋₊ + 1) : ℝ))) *
        ((4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
          Real.log x0 ^ 401) := by
  obtain ⟨C₆, hC₆, hmean⟩ :=
    canonicalFourfoldHeightShiftedFourthIntegral_polylog_le
      hRamachandra hT hx0 hqx hTx hK hthreshold hqpoly
  refine ⟨C₆, hC₆, ?_⟩
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hheightTwo : ∀ z ∈ S, |z.2| ≤ 2 * T := by
    intro z hz
    exact (hheight z hz).trans (by linarith)
  have hholder := sum_shiftedPerronConvolution_fourth_le_exactKernel
    (q := q) (S := S) (delta := canonicalRamachandraOffset x0)
    (T := 2 * T) (canonicalRamachandraOffset_ne_half hx0)
    (by positivity) hheightTwo hsep
  have hmean' :
      allCharacterShiftedLineFourthIntegral q
          (canonicalRamachandraOffset x0) (2 * (2 * T)) ≤
        (4 * C₆ * (4 : ℝ) ^ 400) * (q : ℝ) * T *
          Real.log x0 ^ 401 := by
    have hfour : 2 * (2 * T) = 4 * T := by ring
    rw [hfour]
    rw [allCharacterShiftedLineFourthIntegral_eq_source]
    exact hmean
  have hkernel0 :
      0 ≤ (∫ u in (-(2 * T))..(2 * T), perronWeight u) ^ 3 *
        (4 * (harmonic (⌊4 * (2 * T)⌋₊ + 1) : ℝ)) := by
    have hint : 0 ≤ ∫ u in (-(2 * T))..(2 * T), perronWeight u :=
      intervalIntegral.integral_nonneg (by linarith)
        (fun u hu => (perronWeight_pos u).le)
    exact mul_nonneg (pow_nonneg hint 3)
      (mul_nonneg (by norm_num) (harmonic_nonneg_real _))
  exact hholder.trans (mul_le_mul_of_nonneg_left hmean' hkernel0)

end
end MAPBHPShiftedRamachandraWeld

#print axioms MAPBHPShiftedRamachandraWeld.allCharacterShiftedLineFourthIntegral_eq_source
#print axioms MAPBHPShiftedRamachandraWeld.canonicalRamachandraOffset_ne_half
#print axioms MAPBHPShiftedRamachandraWeld.canonicalShiftedPerronConvolutionFourth_le_exactKernel
