import RamachandraShiftedContourSharpEnvelopes
import RamachandraShiftedDirectParameters

/-!
# Fourth-power functional-factor envelopes for the moment assembly

These are the exact powers needed after weighted Cauchy.  In particular the
long line retains `d^3 (1+|t+v|)^3`; replacing the `3/4` exponent by one
before taking fourth powers would lose a full factor of `T`.
-/

namespace RamachandraShiftedFunctionalFactorMomentEnvelope

open Complex
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedContourSharpEnvelopes
open BHPRamachandraMeanValueFromDyadicAFE

noncomputable section

def longFunctionalMomentConstant : ℝ :=
  (4 * (Real.rpow 2000 (1 / 4) * Real.rpow 2000 (3 / 4))) ^ 4

theorem longFunctionalMomentConstant_nonneg :
    0 ≤ longFunctionalMomentConstant := by
  unfold longFunctionalMomentConstant
  positivity

private theorem rpow_three_quarters_pow_four {x : ℝ} (hx : 0 ≤ x) :
    (Real.rpow x (3 / 4)) ^ 4 = x ^ 3 := by
  calc
    (Real.rpow x (3 / 4)) ^ 4 =
        Real.rpow (Real.rpow x (3 / 4)) (4 : ℝ) := by
      exact (Real.rpow_natCast _ 4).symm
    _ = Real.rpow x ((3 / 4 : ℝ) * 4) := by
      exact (Real.rpow_mul hx (3 / 4 : ℝ) 4).symm
    _ = x ^ 3 := by norm_num [Real.rpow_natCast]

/-- Sharp fourth-power envelope on the literal long line. -/
theorem norm_functionalFactor_long_pow_four_le
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hprim : psi.IsPrimitive) {sigma t v : ℝ} (hne : t + v ≠ 0) :
    ‖ramachandraFunctionalFactor psi (longFunctionalPoint sigma t v)‖ ^ 4 ≤
      longFunctionalMomentConstant * (d : ℝ) ^ 3 * (1 + |t + v|) ^ 3 := by
  have hraw := norm_functionalFactor_longFunctionalPoint_sharp_le
    psi hprim (sigma := sigma) (t := t) (v := v) hne
  let B : ℝ := 1 + |t + v|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsplit : Real.rpow (2000 * B) (3 / 4) =
      Real.rpow 2000 (3 / 4) * Real.rpow B (3 / 4) := by
    exact Real.mul_rpow (by norm_num) hB
  have hfactor :
      ‖ramachandraFunctionalFactor psi (longFunctionalPoint sigma t v)‖ ≤
        (4 * (Real.rpow 2000 (1 / 4) * Real.rpow 2000 (3 / 4))) *
          Real.rpow (d : ℝ) (3 / 4) * Real.rpow B (3 / 4) := by
    rw [hsplit] at hraw
    calc
      _ ≤ Real.rpow (d : ℝ) (3 / 4) *
          (4 * (Real.rpow 2000 (1 / 4) *
            (Real.rpow 2000 (3 / 4) * Real.rpow B (3 / 4)))) := by
        simpa [B] using hraw
      _ = _ := by ring
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hfactor 4
  calc
    ‖ramachandraFunctionalFactor psi (longFunctionalPoint sigma t v)‖ ^ 4 ≤
        ((4 * (Real.rpow 2000 (1 / 4) * Real.rpow 2000 (3 / 4))) *
          Real.rpow (d : ℝ) (3 / 4) * Real.rpow B (3 / 4)) ^ 4 := hpow
    _ = longFunctionalMomentConstant * (d : ℝ) ^ 3 * B ^ 3 := by
      rw [mul_pow, mul_pow,
        rpow_three_quarters_pow_four (Nat.cast_nonneg d),
        rpow_three_quarters_pow_four hB]
      rfl
    _ = longFunctionalMomentConstant * (d : ℝ) ^ 3 *
        (1 + |t + v|) ^ 3 := rfl

/-- Separating the external ordinate from the Mellin ordinate costs no more
than the product of the two degree-three weights. -/
theorem one_add_abs_add_pow_three_le (t v : ℝ) :
    (1 + |t + v|) ^ 3 ≤ (1 + |t|) ^ 3 * (1 + |v|) ^ 3 := by
  have hbase : 1 + |t + v| ≤ (1 + |t|) * (1 + |v|) := by
    have htri := abs_add_le t v
    nlinarith [abs_nonneg t, abs_nonneg v]
  calc
    (1 + |t + v|) ^ 3 ≤ ((1 + |t|) * (1 + |v|)) ^ 3 := by
      gcongr
    _ = (1 + |t|) ^ 3 * (1 + |v|) ^ 3 := mul_pow _ _ _

end
end RamachandraShiftedFunctionalFactorMomentEnvelope

#print axioms RamachandraShiftedFunctionalFactorMomentEnvelope.norm_functionalFactor_long_pow_four_le
#print axioms RamachandraShiftedFunctionalFactorMomentEnvelope.one_add_abs_add_pow_three_le
