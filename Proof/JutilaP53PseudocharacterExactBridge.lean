import JutilaP53AggregateCorrelationLeaf
import JutilaPseudocharacterMExact

/-!
# Exact pseudocharacter bridge for Jutila p.53

The aggregate correlation module keeps a small local definition to avoid a
large import fan-out.  This module certifies that it is exactly the Selberg
pseudocharacter already used in the Lemma-6 development, and that the
weighted value is real.  Thus taking its real part in the source weight (3.3)
does not alter the coefficient.
-/

namespace MAPJutilaP53PseudocharacterExactBridge

open scoped BigOperators
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaPseudocharacterMExact

noncomputable section

theorem jutilaP53SelbergPseudoAt_eq_selbergPseudoAt (r n : ℕ) :
    jutilaP53SelbergPseudoAt r n = selbergPseudoAt r n := by
  rfl

theorem selbergPseudoAt_im_eq_zero (r n : ℕ) :
    (selbergPseudoAt r n).im = 0 := by
  unfold selbergPseudoAt selbergPseudoCoeff
  simp

theorem jutilaP53WeightedPseudocharacter_im_eq_zero
    (S : Finset ℕ) (n : ℕ) :
    (jutilaP53WeightedPseudocharacter S n).im = 0 := by
  unfold jutilaP53WeightedPseudocharacter
  change Complex.imLm (∑ r ∈ S,
    (r : ℂ)⁻¹ * jutilaP53SelbergPseudoAt r n) = 0
  rw [map_sum Complex.imLm]
  apply Finset.sum_eq_zero
  intro r hr
  simp [Complex.mul_im,
    jutilaP53SelbergPseudoAt_eq_selbergPseudoAt,
    selbergPseudoAt_im_eq_zero]

/-- The `re` in the p.53 weight is only a typed projection of an exactly
real source coefficient. -/
theorem jutilaP53WeightedPseudocharacter_eq_ofReal
    (S : Finset ℕ) (n : ℕ) :
    jutilaP53WeightedPseudocharacter S n =
      (jutilaP53PseudoReal S n : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa [jutilaP53PseudoReal] using
      jutilaP53WeightedPseudocharacter_im_eq_zero S n

end

end MAPJutilaP53PseudocharacterExactBridge

#print axioms MAPJutilaP53PseudocharacterExactBridge.jutilaP53WeightedPseudocharacter_eq_ofReal
