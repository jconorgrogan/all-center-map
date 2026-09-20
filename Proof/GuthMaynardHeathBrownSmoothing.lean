import GuthMaynardHeathBrownShiftRemoval

/-!
# Exact dyadic smoothing majorant in the Heath--Brown branch

The rough published-proof exposition replaces the normalized hard dyadic
half-weight by

`exp (-(n/(2M))^h) - exp (-(n/M)^h)`

with `h = log T`, before applying Mellin inversion (Hardy, Warwick notes,
p. 4, lines 219--237 of the extracted text).  Here we prove an explicit,
uniform lower bound on that cutoff for every `M ≤ n ≤ 2M` and every `h ≥ 1`.
Consequently the hard normalized coefficient, with or without the auxiliary
Mellin phase, is majorized by a fixed multiple of the smooth coefficient.

This is the last purely finite/order-theoretic step before the analytic
reflection estimate.  It introduces no large-value, contour-shift, or
length-comparison premise.
-/

namespace GuthMaynardHeathBrownSmoothing

open GuthMaynardHeathBrownInterface
open GuthMaynardHeathBrownMajorant
open GuthMaynardHeathBrownShiftRemoval

noncomputable section

def smoothDyadicCutoff (h : ℝ) (M n : ℕ) : ℝ :=
  Real.exp (-Real.rpow ((n : ℝ) / (2 * M : ℕ)) h) -
    Real.exp (-Real.rpow ((n : ℝ) / (M : ℝ)) h)

/-- A convenient explicit floor.  The two entries correspond to the split
`n/M ≤ 3/2` and `3/2 < n/M`. -/
def smoothDyadicFloor : ℝ :=
  min (Real.exp (-(3 / 4 : ℝ)) - Real.exp (-1))
    (Real.exp (-1) - Real.exp (-(3 / 2 : ℝ)))

theorem smoothDyadicFloor_pos : 0 < smoothDyadicFloor := by
  unfold smoothDyadicFloor
  rw [lt_min_iff]
  constructor <;> apply sub_pos.mpr <;> rw [Real.exp_lt_exp] <;> norm_num

theorem smoothDyadicFloor_le_cutoff
    {h : ℝ} {M n : ℕ} (hh : 1 ≤ h) (hM : 1 ≤ M)
    (hn : n ∈ Finset.Icc M (2 * M)) :
    smoothDyadicFloor ≤ smoothDyadicCutoff h M n := by
  have hnIcc := Finset.mem_Icc.mp hn
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hM
  have hnPos : 0 < (n : ℝ) := by
    exact lt_of_lt_of_le hMpos (by exact_mod_cast hnIcc.1)
  have hratioLower : 1 ≤ (n : ℝ) / M := by
    rw [le_div_iff₀ hMpos]
    simpa using (by exact_mod_cast hnIcc.1 : (M : ℝ) ≤ n)
  have hratioUpper : (n : ℝ) / M ≤ 2 := by
    rw [div_le_iff₀ hMpos]
    norm_num
    exact_mod_cast hnIcc.2
  have hhalfEq :
      (n : ℝ) / (2 * M : ℕ) = ((n : ℝ) / M) / 2 := by
    push_cast
    field_simp
    <;> ring
  have hhNonneg : 0 ≤ h := le_trans (by norm_num) hh
  by_cases hsmall : (n : ℝ) / M ≤ 3 / 2
  · have hhalfPos : 0 < (n : ℝ) / (2 * M : ℕ) := by positivity
    have hhalfLeOne : (n : ℝ) / (2 * M : ℕ) ≤ 1 := by
      rw [hhalfEq]
      linarith
    have hhalfLeThreeFourth :
        (n : ℝ) / (2 * M : ℕ) ≤ 3 / 4 := by
      rw [hhalfEq]
      linarith
    have hleftPow :
        Real.rpow ((n : ℝ) / (2 * M : ℕ)) h ≤ 3 / 4 := by
      calc
        Real.rpow ((n : ℝ) / (2 * M : ℕ)) h ≤
            Real.rpow ((n : ℝ) / (2 * M : ℕ)) 1 :=
          Real.rpow_le_rpow_of_exponent_ge hhalfPos hhalfLeOne hh
        _ = (n : ℝ) / (2 * M : ℕ) := by simp
        _ ≤ 3 / 4 := hhalfLeThreeFourth
    have hrightPow : 1 ≤ Real.rpow ((n : ℝ) / M) h :=
      Real.one_le_rpow hratioLower hhNonneg
    have hleftExp :
        Real.exp (-(3 / 4 : ℝ)) ≤
          Real.exp (-Real.rpow ((n : ℝ) / (2 * M : ℕ)) h) := by
      rw [Real.exp_le_exp]
      linarith
    have hrightExp :
        Real.exp (-Real.rpow ((n : ℝ) / M) h) ≤ Real.exp (-1) := by
      rw [Real.exp_le_exp]
      linarith
    exact (min_le_left _ _).trans (by
      unfold smoothDyadicCutoff
      linarith)
  · have hratioThreeHalves : 3 / 2 ≤ (n : ℝ) / M := le_of_not_ge hsmall
    have hhalfPos : 0 < (n : ℝ) / (2 * M : ℕ) := by positivity
    have hhalfLeOne : (n : ℝ) / (2 * M : ℕ) ≤ 1 := by
      rw [hhalfEq]
      linarith
    have hleftPow :
        Real.rpow ((n : ℝ) / (2 * M : ℕ)) h ≤ 1 :=
      Real.rpow_le_one (le_of_lt hhalfPos) hhalfLeOne hhNonneg
    have hrightPow :
        3 / 2 ≤ Real.rpow ((n : ℝ) / M) h := by
      calc
        (3 / 2 : ℝ) ≤ (n : ℝ) / M := hratioThreeHalves
        _ = Real.rpow ((n : ℝ) / M) 1 := by simp
        _ ≤ Real.rpow ((n : ℝ) / M) h :=
          Real.rpow_le_rpow_of_exponent_le hratioLower hh
    have hleftExp :
        Real.exp (-1) ≤
          Real.exp (-Real.rpow ((n : ℝ) / (2 * M : ℕ)) h) := by
      rw [Real.exp_le_exp]
      linarith
    have hrightExp :
        Real.exp (-Real.rpow ((n : ℝ) / M) h) ≤
          Real.exp (-(3 / 2 : ℝ)) := by
      rw [Real.exp_le_exp]
      linarith
    exact (min_le_right _ _).trans (by
      unfold smoothDyadicCutoff
      linarith)

/-- The fixed-multiple smooth coefficient that pointwise dominates the hard
normalized half-weight. -/
def smoothMajorantCoefficient (h : ℝ) (M n : ℕ) : ℝ :=
  smoothDyadicCutoff h M n / smoothDyadicFloor

theorem one_le_smoothMajorantCoefficient
    {h : ℝ} {M n : ℕ} (hh : 1 ≤ h) (hM : 1 ≤ M)
    (hn : n ∈ Finset.Icc M (2 * M)) :
    1 ≤ smoothMajorantCoefficient h M n := by
  unfold smoothMajorantCoefficient
  rw [le_div_iff₀ smoothDyadicFloor_pos]
  simpa using smoothDyadicFloor_le_cutoff hh hM hn

/-- Exact hard-to-smooth majorization, retaining the Mellin phase and the
printed dyadic endpoints. -/
theorem differenceQuadraticForm_shiftedHalfWeight_le_smooth
    {h : ℝ} {M : ℕ} (hh : 1 ≤ h) (hM : 1 ≤ M)
    (tau : ℝ) (W : Finset ℝ) :
    differenceQuadraticForm (shiftedNormalizedHalfWeight M tau) M W ≤
      differenceQuadraticForm
        (fun n => (smoothMajorantCoefficient h M n : ℂ)) M W := by
  apply differenceQuadraticForm_majorant
  intro n hn
  calc
    ‖shiftedNormalizedHalfWeight M tau n‖ =
        ‖normalizedHalfWeight M n‖ :=
      norm_shiftedNormalizedHalfWeight M tau n
    _ ≤ 1 := norm_normalizedHalfWeight_le_one hM hn
    _ ≤ smoothMajorantCoefficient h M n :=
      one_le_smoothMajorantCoefficient hh hM hn

end

end GuthMaynardHeathBrownSmoothing

#print axioms GuthMaynardHeathBrownSmoothing.smoothDyadicFloor_pos
#print axioms GuthMaynardHeathBrownSmoothing.smoothDyadicFloor_le_cutoff
#print axioms GuthMaynardHeathBrownSmoothing.one_le_smoothMajorantCoefficient
#print axioms GuthMaynardHeathBrownSmoothing.differenceQuadraticForm_shiftedHalfWeight_le_smooth
