import JutilaP53KernelSourceForm

/-!
# Exact double-`r` expansion of the p.53 pseudocharacter square

This is the algebra immediately preceding Jutila's use of Lemma 2.  The
prime on the source `r`-sum remains represented by the selected finite set
`S`; no full interval of squarefree integers is reintroduced.
-/

namespace MAPJutilaP53PseudocharacterSquareExpansion

open scoped BigOperators
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53PseudocharacterExactBridge

noncomputable section

def normalizedP53PseudoAt (r n : ℕ) : ℂ :=
  (r : ℂ)⁻¹ * jutilaP53SelbergPseudoAt r n

theorem norm_normalizedP53PseudoAt_le_one
    {r n : ℕ} (hr : 0 < r) :
    ‖normalizedP53PseudoAt r n‖ ≤ 1 := by
  have hf := norm_jutilaP53SelbergPseudoAt_le r n
  have hphiNat : Nat.totient (r.gcd n) ≤ r :=
    (Nat.totient_le _).trans (Nat.gcd_le_left n hr)
  have hphi : (Nat.totient (r.gcd n) : ℝ) ≤ r := by
    exact_mod_cast hphiNat
  have hfr : ‖jutilaP53SelbergPseudoAt r n‖ ≤ (r : ℝ) :=
    hf.trans hphi
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  unfold normalizedP53PseudoAt
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (r : ℝ)⁻¹ * ‖jutilaP53SelbergPseudoAt r n‖ ≤
        (r : ℝ)⁻¹ * (r : ℝ) :=
      mul_le_mul_of_nonneg_left hfr (by positivity)
    _ = 1 := inv_mul_cancel₀ hrR.ne'

theorem weightedPseudocharacter_eq_sum_normalized
    (S : Finset ℕ) (n : ℕ) :
    jutilaP53WeightedPseudocharacter S n =
      ∑ r ∈ S, normalizedP53PseudoAt r n := by
  rfl

/-- Literal finite double-sum expansion of the square in (3.3). -/
theorem pseudoReal_sq_eq_doubleSum
    (S : Finset ℕ) (n : ℕ) :
    ((jutilaP53PseudoReal S n) ^ 2 : ℂ) =
      ∑ r ∈ S, ∑ r' ∈ S,
        normalizedP53PseudoAt r n * normalizedP53PseudoAt r' n := by
  have hreal := jutilaP53WeightedPseudocharacter_eq_ofReal S n
  have hsq := congrArg (fun z : ℂ => z ^ 2) hreal
  rw [weightedPseudocharacter_eq_sum_normalized] at hsq
  change (∑ r ∈ S, normalizedP53PseudoAt r n) ^ 2 =
    ((jutilaP53PseudoReal S n : ℝ) : ℂ) ^ 2 at hsq
  rw [← hsq]
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]

end

end MAPJutilaP53PseudocharacterSquareExpansion

#print axioms MAPJutilaP53PseudocharacterSquareExpansion.norm_normalizedP53PseudoAt_le_one
#print axioms MAPJutilaP53PseudocharacterSquareExpansion.pseudoReal_sq_eq_doubleSum
