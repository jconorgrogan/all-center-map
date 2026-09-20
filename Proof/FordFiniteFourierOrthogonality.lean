import Mathlib.Analysis.Fourier.ZMod

open scoped BigOperators ZMod
open Finset

namespace MAPFordFiniteFourierOrthogonality
noncomputable section

lemma stdAddChar_sum_mul {L : ℕ} [NeZero L] (b : ZMod L) :
    (∑ x : ZMod L, ZMod.stdAddChar (x * b)) =
      if b = 0 then (L : ℂ) else 0 := by
  simpa using (AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar L))

lemma int_zero_of_mod_zero_of_abs_lt {L : ℕ} [NeZero L] {a : ℤ}
    (ha : |a| < (L : ℤ)) (h : (a : ZMod L) = 0) : a = 0 := by
  have hm : a ≡ 0 [ZMOD (L : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff a 0 L).1 (by simpa using h)
  obtain ⟨t, ht⟩ := (Int.modEq_iff_add_fac.mp hm)
  have hL : (0 : ℤ) < L := by exact_mod_cast (NeZero.pos L)
  have habs : -(L : ℤ) < a ∧ a < L := (abs_lt.mp ha)
  by_cases ht0 : t = 0
  · simpa [ht0] using ht.symm
  · by_cases htpos : 0 < t
    · have hmul : (L : ℤ) ≤ L * t := by
        have h := mul_le_mul_of_nonneg_left
          (show (1 : ℤ) ≤ t by omega) (le_of_lt hL)
        simpa using h
      nlinarith
    · have htneg : t ≤ -1 := by omega
      have hmul : L * t ≤ -(L : ℤ) := by
        have h := mul_le_mul_of_nonneg_left
          (show t ≤ (-1 : ℤ) by omega) (le_of_lt hL)
        simpa using h
      nlinarith

/-- Integer frequency coordinates have no alias in `ZMod L` when their
absolute values are below `L`.  This is the exact bridge needed before using
`AddChar.sum_mulShift` coordinate by coordinate on `(ZMod L)^k`. -/
lemma frequency_mod_zero_iff {L k : ℕ} [NeZero L]
    (freq : Fin k → ℤ) (hbound : ∀ j, |freq j| < (L : ℤ)) :
    (∀ j, (freq j : ZMod L) = 0) ↔ ∀ j, freq j = 0 := by
  constructor
  · intro h j
    exact int_zero_of_mod_zero_of_abs_lt (hbound j) (h j)
  · intro h j
    simp [h j]

/-- The finite root-of-unity construction contract.  For an expanded masked
carrier indexed by `β`, `freq b : Fin k → ℤ` is the exact integer equation
frequency.  After mapping each coordinate to `ZMod L`, the scalar theorem
`stdAddChar_sum_mul` is applied in each coordinate; `frequency_mod_zero_iff`
justifies replacing the resulting modular zero test by the literal integer
system whenever `L` exceeds the stated bound.  The product carrier has
normalization `L^k`. -/
def vectorFrequencyMod {L k : ℕ} (freq : Fin k → ℤ) : Fin k → ZMod L :=
  fun j => freq j

end
end MAPFordFiniteFourierOrthogonality

#print axioms MAPFordFiniteFourierOrthogonality.stdAddChar_sum_mul
#print axioms MAPFordFiniteFourierOrthogonality.int_zero_of_mod_zero_of_abs_lt
#print axioms MAPFordFiniteFourierOrthogonality.frequency_mod_zero_iff
