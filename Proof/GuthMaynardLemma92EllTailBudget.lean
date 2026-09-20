import GuthMaynardLemma92LargeEllRange
import GuthMaynardLemma92LargeEllSelectedWeld

/-!
# Explicit scalar budget for the discarded ell tail

After choosing a detector radius `R`, the large-ell Fourier factor is bounded
by `(2/R)^j` as soon as the smoothing width is at most half of `R*T`.
This file keeps the remaining polynomial factors literal.
-/

open scoped Real

noncomputable section
namespace GuthMaynardJIteration

/-- Exact cancellation of the dyadic scale in the discarded-frequency
denominator. -/
theorem sourceLemma92_ellTail_frequencyGap_eq
    {M : ℕ} (hM : 0 < M) (T B R : ℝ) :
    (M : ℝ) * (R * T / (M : ℝ) - B / (M : ℝ)) = R * T - B := by
  have hMreal : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  field_simp [hMreal]

/-- If `2B ≤ R*T`, the large-ell Fourier ratio is at most `2/R`. -/
theorem sourceLemma92_ellTail_ratio_le_two_div_radius
    {M : ℕ} (hM : 0 < M) {T B R : ℝ}
    (hT : 0 < T) (_hB : 0 ≤ B) (hR : 0 < R)
    (hhalf : 2 * B ≤ R * T) :
    T / ((M : ℝ) *
        (R * T / (M : ℝ) - B / (M : ℝ))) ≤ 2 / R := by
  rw [sourceLemma92_ellTail_frequencyGap_eq hM]
  have hRT : 0 < R * T := mul_pos hR hT
  have hgap : 0 < R * T - B := by
    nlinarith
  rw [div_le_div_iff₀ hgap hR]
  nlinarith

/-- The literal first-Poisson ell window has at most `7*T^6` indices when
the smoothing width is below `T^6`. -/
theorem card_sourceLemma92LargeEllRange_cast_le_seven_time_six
    {M : ℕ} (hM : 0 < M) {T B : ℝ}
    (hT : 1 ≤ T) (hB : 0 ≤ B) (hBT : B ≤ T ^ 6) :
    ((sourceLemma92LargeEllRange M T B).card : ℝ) ≤ 7 * T ^ 6 := by
  have hMreal : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hnum0 : 0 ≤ T ^ 6 + B := by positivity
  have hdiv : (T ^ 6 + B) / (M : ℝ) ≤ 2 * T ^ 6 := by
    calc
      (T ^ 6 + B) / (M : ℝ) ≤ T ^ 6 + B :=
        (div_le_self hnum0 hMreal)
      _ ≤ 2 * T ^ 6 := by linarith
  have hcard := card_sourceLemma92LargeEllRange_cast_le hM
    (by linarith : (0 : ℝ) ≤ T) hB
  have hT6 : 1 ≤ T ^ 6 := by
    simpa using (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hT 6)
  calc
    ((sourceLemma92LargeEllRange M T B).card : ℝ) ≤
        2 * ((T ^ 6 + B) / (M : ℝ)) + 3 := hcard
    _ ≤ 2 * (2 * T ^ 6) + 3 := by linarith
    _ ≤ 7 * T ^ 6 := by linarith

/-- Complete explicit upper envelope for the discarded ell tail on the
literal large first-Poisson range. -/
theorem sourceLemma92EllTailCostRadius_largeRange_le
    {M : ℕ} (hM : 0 < M) {T S eta C delta R : ℝ} (j : ℕ)
    (hT : 1 ≤ T) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hB6 : T ^ delta ≤ T ^ 6) (hR : 0 < R)
    (hhalf : 2 * T ^ delta ≤ R * T) :
    sourceLemma92EllTailCostRadius
        (sourceLemma92LargeEllRange M T (T ^ delta)) M
        T S eta C delta R j ≤
      (7 * T ^ 6) * (2 * T ^ delta) *
        (((7 * (M : ℝ)) * (2 * (M : ℝ)) *
          (C * T ^ eta * (2 / R) ^ j * S)) ^ 2) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hB0 : 0 ≤ T ^ delta := (Real.rpow_pos_of_pos hTpos delta).le
  have hcard := card_sourceLemma92LargeEllRange_cast_le_seven_time_six
    hM hT hB0 hB6
  have hMone : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hmcard : 4 * (M : ℝ) + 3 ≤ 7 * (M : ℝ) := by nlinarith
  have hratio := sourceLemma92_ellTail_ratio_le_two_div_radius
    hM hTpos hB0 hR hhalf
  have hratio0 : 0 ≤
      T / ((M : ℝ) *
        (R * T / (M : ℝ) - T ^ delta / (M : ℝ))) := by
    have hgap : 0 < (M : ℝ) *
        (R * T / (M : ℝ) - T ^ delta / (M : ℝ)) := by
      rw [sourceLemma92_ellTail_frequencyGap_eq hM]
      have hRT : 0 < R * T := mul_pos hR hTpos
      nlinarith
    positivity
  have hpow :
      (T / ((M : ℝ) *
        (R * T / (M : ℝ) - T ^ delta / (M : ℝ)))) ^ j ≤
          (2 / R) ^ j := pow_le_pow_left₀ hratio0 hratio j
  unfold sourceLemma92EllTailCostRadius
  gcongr

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceLemma92_ellTail_frequencyGap_eq
#print axioms GuthMaynardJIteration.sourceLemma92_ellTail_ratio_le_two_div_radius
#print axioms GuthMaynardJIteration.card_sourceLemma92LargeEllRange_cast_le_seven_time_six
#print axioms GuthMaynardJIteration.sourceLemma92EllTailCostRadius_largeRange_le
