import GuthMaynardHeathBrownMajorant

/-!
# Removing the reflected Mellin shift in the Heath--Brown branch

After smoothing and reflection, the rough proof of Heath--Brown's
difference-set estimate contains coefficients of the form

`sqrt (M / n) * exp (i * tau * log n)`

on `M ≤ n ≤ 2M`.  The source then removes the auxiliary Mellin variable
`tau` by the coefficient-majorant principle (Hardy, Warwick notes on
Heath--Brown's theorem, p. 5, lines 247--256 of the extracted text).

This file certifies that finite step exactly.  It also proves that the
normalized half-weight is bounded by one, so the result is controlled by the
coefficient-one quadratic form.  No smoothing, reflection, length comparison,
or analytic large-value estimate is assumed here.
-/

namespace GuthMaynardHeathBrownShiftRemoval

open scoped BigOperators
open GuthMaynardHeathBrownInterface
open GuthMaynardHeathBrownMajorant

noncomputable section

/-- The normalized `n^{-1/2}` weight on a dyadic block.  Multiplication by
`M^{-1/2}` recovers the usual half-weight. -/
def normalizedHalfWeight (M n : ℕ) : ℂ :=
  (Real.sqrt ((M : ℝ) / (n : ℝ)) : ℂ)

/-- The unit-modulus Mellin phase produced by reflection. -/
def mellinShiftPhase (tau : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((tau * Real.log n : ℝ) : ℂ) * Complex.I)

/-- The literal shifted normalized coefficient in the reflected polynomial. -/
def shiftedNormalizedHalfWeight (M : ℕ) (tau : ℝ) (n : ℕ) : ℂ :=
  normalizedHalfWeight M n * mellinShiftPhase tau n

theorem norm_mellinShiftPhase (tau : ℝ) (n : ℕ) :
    ‖mellinShiftPhase tau n‖ = 1 := by
  unfold mellinShiftPhase
  exact Complex.norm_exp_ofReal_mul_I _

theorem normalizedHalfWeight_nonneg (M n : ℕ) :
    0 ≤ Real.sqrt ((M : ℝ) / (n : ℝ)) :=
  Real.sqrt_nonneg _

/-- On the exact printed block `M ≤ n ≤ 2M`, the normalized half-weight is
at most one. -/
theorem norm_normalizedHalfWeight_le_one
    {M n : ℕ} (hM : 1 ≤ M) (hn : n ∈ Finset.Icc M (2 * M)) :
    ‖normalizedHalfWeight M n‖ ≤ 1 := by
  have hnIcc := Finset.mem_Icc.mp hn
  have hnPos : 0 < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (Nat.zero_lt_of_lt hM) hnIcc.1
  have hMn : (M : ℝ) ≤ n := by exact_mod_cast hnIcc.1
  have hratio : (M : ℝ) / n ≤ 1 := (div_le_one hnPos).2 hMn
  unfold normalizedHalfWeight
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one]
  exact hratio

/-- The auxiliary Mellin phase changes no coefficient norm. -/
theorem norm_shiftedNormalizedHalfWeight
    (M : ℕ) (tau : ℝ) (n : ℕ) :
    ‖shiftedNormalizedHalfWeight M tau n‖ =
      ‖normalizedHalfWeight M n‖ := by
  rw [shiftedNormalizedHalfWeight, norm_mul,
    norm_mellinShiftPhase, mul_one]

/-- Exact source step: the reflected Mellin variable `tau` can be removed
from the difference-set quadratic form without changing the finite range or
the sample set. -/
theorem differenceQuadraticForm_shiftedHalfWeight_le_unshifted
    (M : ℕ) (tau : ℝ) (W : Finset ℝ) :
    differenceQuadraticForm (shiftedNormalizedHalfWeight M tau) M W ≤
      differenceQuadraticForm (normalizedHalfWeight M) M W := by
  apply differenceQuadraticForm_majorant
    (b := fun n => Real.sqrt ((M : ℝ) / (n : ℝ)))
  intro n hn
  rw [norm_shiftedNormalizedHalfWeight]
  unfold normalizedHalfWeight
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- The reflected half-weight is in the coefficient-one ball used by
`HeathBrownOneCoefficientCore`. -/
theorem differenceQuadraticForm_shiftedHalfWeight_le_one
    {M : ℕ} (hM : 1 ≤ M) (tau : ℝ) (W : Finset ℝ) :
    differenceQuadraticForm (shiftedNormalizedHalfWeight M tau) M W ≤
      differenceQuadraticForm (fun _ => (1 : ℂ)) M W := by
  exact differenceQuadraticForm_le_oneCoefficient M W
    (fun n hn => (norm_shiftedNormalizedHalfWeight M tau n).trans_le
      (norm_normalizedHalfWeight_le_one hM hn))

/-- The two source reductions compose: remove the Mellin shift, then compare
the normalized half-weight with the coefficient-one polynomial. -/
theorem differenceQuadraticForm_shiftRemoval_chain
    {M : ℕ} (hM : 1 ≤ M) (tau : ℝ) (W : Finset ℝ) :
    differenceQuadraticForm (shiftedNormalizedHalfWeight M tau) M W ≤
        differenceQuadraticForm (normalizedHalfWeight M) M W ∧
      differenceQuadraticForm (normalizedHalfWeight M) M W ≤
        differenceQuadraticForm (fun _ => (1 : ℂ)) M W := by
  constructor
  · exact differenceQuadraticForm_shiftedHalfWeight_le_unshifted M tau W
  · exact differenceQuadraticForm_le_oneCoefficient M W
      (fun n hn => norm_normalizedHalfWeight_le_one hM hn)

end

end GuthMaynardHeathBrownShiftRemoval

#print axioms GuthMaynardHeathBrownShiftRemoval.norm_mellinShiftPhase
#print axioms GuthMaynardHeathBrownShiftRemoval.norm_normalizedHalfWeight_le_one
#print axioms GuthMaynardHeathBrownShiftRemoval.norm_shiftedNormalizedHalfWeight
#print axioms GuthMaynardHeathBrownShiftRemoval.differenceQuadraticForm_shiftedHalfWeight_le_unshifted
#print axioms GuthMaynardHeathBrownShiftRemoval.differenceQuadraticForm_shiftedHalfWeight_le_one
#print axioms GuthMaynardHeathBrownShiftRemoval.differenceQuadraticForm_shiftRemoval_chain
