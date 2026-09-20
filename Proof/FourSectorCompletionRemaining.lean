import EqualShortSectorCompletion

/-!
# Four-sector MAP summation after equal-short and zero closure

This module combines the exact sector decomposition with the now-global
equal-short and zero-sector theorems.  It leaves the positive-plus-negative
mass as a literal finite expression, not as a premise.
-/

noncomputable section

namespace MAPMixedMeanCompletion

open DeterminantCountWeld MixedMeanFrontend MixedMeanMajorantWeld
open MAPMixedMeanFloor MAPMixedMeanZeroClose MAPMixedMean MixedMellinCert

def equalShortHarmonicEnvelope (k M N : ℕ) (T : ℝ) : ℝ :=
  (2 : ℝ) * M * N * (2 * Real.pi * N / T + 1) *
    ((harmonic (2 * N) : ℚ) : ℝ) ^ (k * k - 1)

def nonzeroTauSurvivorMass (k M N : ℕ) (T U : ℝ) : ℝ :=
  weightedMass (tauTupleWeight k)
      (positiveFrequencySector M N
        (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
    weightedMass (tauTupleWeight k)
      (negativeFrequencySector M N
        (Real.pi / (2 * U)) (Real.pi / (2 * T)))

def zeroHarmonicEnvelope (k M N : ℕ) (U : ℝ) : ℝ :=
  (8 * N * shortFloorCollar M U : ℕ) *
    ((harmonic (shortFloorCollar M U) : ℚ) : ℝ) *
    ((harmonic (2 * N) : ℚ) : ℝ) ^ (k * k - 1) *
    ((harmonic (2 * M) : ℚ) : ℝ) ^ (k * k - 1)

/-- All four exact Fourier sectors are summed.  Equal-short and zero are
replaced by proved global envelopes; positive and negative remain as the
literal finite nonzero mass whose Shiu aggregation is still open. -/
theorem paperTauSurvivorMass_le_envelopes_add_nonzero
    (k M N : ℕ) {T U : ℝ}
    (hk : 1 ≤ k) (hM : 0 < M) (hT : 0 < T) (hU : 0 < U) :
    paperTauSurvivorMass k M N T U ≤
      equalShortHarmonicEnvelope k M N T +
        nonzeroTauSurvivorMass k M N T U +
        zeroHarmonicEnvelope k M N U := by
  have heq := equalShortFrequencySector_tauMass_le_harmonic
    k M N (U := U) hk hT
  have hzero := zeroFrequencySector_tauMass_le_harmonic
    k M N hk hM hT hU
  rw [paperTauSurvivorMass_eq_sector_sum]
  unfold equalShortHarmonicEnvelope nonzeroTauSurvivorMass zeroHarmonicEnvelope
  calc
    weightedMass (tauTupleWeight k)
          (equalShortFrequencySector M N
            (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
        weightedMass (tauTupleWeight k)
          (positiveFrequencySector M N
            (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
        weightedMass (tauTupleWeight k)
          (negativeFrequencySector M N
            (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
        weightedMass (tauTupleWeight k)
          (zeroFrequencySector M N
            (Real.pi / (2 * U)) (Real.pi / (2 * T))) =
      weightedMass (tauTupleWeight k)
          (equalShortFrequencySector M N
            (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
        (weightedMass (tauTupleWeight k)
            (positiveFrequencySector M N
              (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
          weightedMass (tauTupleWeight k)
            (negativeFrequencySector M N
              (Real.pi / (2 * U)) (Real.pi / (2 * T)))) +
        weightedMass (tauTupleWeight k)
          (zeroFrequencySector M N
            (Real.pi / (2 * U)) (Real.pi / (2 * T))) := by ring
    _ ≤ (2 : ℝ) * M * N * (2 * Real.pi * N / T + 1) *
          ((harmonic (2 * N) : ℚ) : ℝ) ^ (k * k - 1) +
        (weightedMass (tauTupleWeight k)
            (positiveFrequencySector M N
              (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
          weightedMass (tauTupleWeight k)
            (negativeFrequencySector M N
              (Real.pi / (2 * U)) (Real.pi / (2 * T)))) +
        ((8 * N * shortFloorCollar M U : ℕ) : ℝ) *
          ((harmonic (shortFloorCollar M U) : ℚ) : ℝ) *
          ((harmonic (2 * N) : ℚ) : ℝ) ^ (k * k - 1) *
          ((harmonic (2 * M) : ℚ) : ℝ) ^ (k * k - 1) :=
      add_le_add (add_le_add heq (le_refl _)) hzero

/-- Strongest paper-facing mixed-mean theorem without a MAP-owned sector
premise.  The only unresolved summand is `nonzeroTauSurvivorMass`. -/
theorem paperLiteralMixedMean_re_le_envelopes_add_nonzero
    {a k M N : ℕ} {βraw graw : ℕ → ℂ} (t₀ : ℝ)
    {T U : ℝ} (hk : 1 ≤ k) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hT : 0 < T) (hU : 0 < U)
    (hcoeff : MAPNormalizedWrapper.PaperCoefficientBounds
      M N a k βraw graw) :
    (paperLiteralMixedMean M N βraw graw t₀ T U).re ≤
      256 * T * U *
        (Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) /
          ((M : ℝ) * (N : ℝ))) *
        (equalShortHarmonicEnvelope k M N T +
          nonzeroTauSurvivorMass k M N T U +
          zeroHarmonicEnvelope k M N U) := by
  have hfront := paperLiteralMixedMean_re_le_tauSurvivorMass
    (M := M) (N := N) (a := a) (k := k)
    (βraw := βraw) (graw := graw) t₀ hM hN hT hU hcoeff
  have hsectors := paperTauSurvivorMass_le_envelopes_add_nonzero
    k M N hk (by omega) hT hU
  have hL4 : 0 ≤ Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) := by
    rw [show 4 * a = a * 4 by omega, pow_mul]
    positivity
  calc
    (paperLiteralMixedMean M N βraw graw t₀ T U).re ≤
      256 * T * U *
        (Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) /
          ((M : ℝ) * (N : ℝ))) *
        paperTauSurvivorMass k M N T U := hfront
    _ ≤ 256 * T * U *
        (Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) /
          ((M : ℝ) * (N : ℝ))) *
        (equalShortHarmonicEnvelope k M N T +
          nonzeroTauSurvivorMass k M N T U +
          zeroHarmonicEnvelope k M N U) := by
      exact mul_le_mul_of_nonneg_left hsectors
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hT.le) hU.le)
          (div_nonneg hL4 (by positivity)))

end MAPMixedMeanCompletion
