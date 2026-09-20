import JutilaP53PrincipalRResidueAggregation
import JutilaPseudocharacterMollifierSum

/-!
# Elementary average bound for the normalized p.53 Euler mass
-/

namespace MAPJutilaP53NormalizedEulerMassBound

open scoped BigOperators
open MAPJutilaP53PrincipalRResidueAggregation
open MAPJutilaLemma3AbsoluteMass
open MAPJutilaPseudocharacterMollifierBound
open MAPJutilaPseudocharacterMollifierSum

noncomputable section

/-- A single normalized Euler-mass entry is bounded by the product of the
standard totient quotients. -/
theorem normalizedEulerMass_term_le_totientQuotient_mul
    {r r' : ℕ} (hr : 1 ≤ r) (hr' : 1 ≤ r')
    (hsq : Squarefree r) (hsq' : Squarefree r') :
    (((r * r' : ℕ) : ℝ)⁻¹) *
        (lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ) ≤
      totientQuotient r * totientQuotient r' := by
  have hlarge : ∀ p ∈ r.primeFactors ∪ r'.primeFactors, 2 ≤ p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Nat.prime_of_mem_primeFactors hp).two_le
    · exact (Nat.prime_of_mem_primeFactors hp).two_le
  have hmassNat := lemmaThreeAbsoluteMass_le r.primeFactors r'.primeFactors hlarge
  have hmass :
      (lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ) ≤
        pseudocharacterEulerProduct r * pseudocharacterEulerProduct r' := by
    unfold pseudocharacterEulerProduct
    exact_mod_cast hmassNat
  have hrpos : 0 < r := by omega
  have hr'pos : 0 < r' := by omega
  have hphi : 0 < (Nat.totient r : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hrpos
  have hphi' : 0 < (Nat.totient r' : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hr'pos
  have hEuler0 : 0 ≤ pseudocharacterEulerProduct r' := by
    unfold pseudocharacterEulerProduct
    positivity
  have hprod := mul_le_mul
    (pseudocharacterEulerProduct_le_sq_div_totient hrpos hsq)
    (pseudocharacterEulerProduct_le_sq_div_totient hr'pos hsq')
    hEuler0 (by positivity)
  calc
    (((r * r' : ℕ) : ℝ)⁻¹) *
        (lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ) ≤
      (((r * r' : ℕ) : ℝ)⁻¹) *
        (pseudocharacterEulerProduct r * pseudocharacterEulerProduct r') :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ (((r * r' : ℕ) : ℝ)⁻¹) *
        (((r : ℝ) ^ 2 / (Nat.totient r : ℝ)) *
          ((r' : ℝ) ^ 2 / (Nat.totient r' : ℝ))) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = totientQuotient r * totientQuotient r' := by
      unfold totientQuotient
      push_cast
      field_simp [show (r : ℝ) ≠ 0 by positivity,
        show (r' : ℝ) ≠ 0 by positivity, hphi.ne', hphi'.ne']

/-- The complete normalized Euler mass costs `R^2` times a fixed harmonic
power.  This is the exact elementary form needed before the collar's
polylogarithmic absorption. -/
theorem p53NormalizedEulerMass_le_R_sq_mul_harmonic_pow_eight
    {S : Finset ℕ} {R : ℕ} (hS : S ⊆ Finset.Icc 1 R)
    (hSq : ∀ r ∈ S, Squarefree r) :
    p53NormalizedEulerMass S ≤
      (R : ℝ) ^ 2 * (harmonic R : ℝ) ^ 8 := by
  have hterm : ∀ r ∈ S, ∀ r' ∈ S,
      (((r * r' : ℕ) : ℝ)⁻¹) *
          (lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ) ≤
        totientQuotient r * totientQuotient r' := by
    intro r hr r' hr'
    exact normalizedEulerMass_term_le_totientQuotient_mul
      (Finset.mem_Icc.mp (hS hr)).1 (Finset.mem_Icc.mp (hS hr')).1
      (hSq r hr) (hSq r' hr')
  have htq0 : ∀ r : ℕ, 0 ≤ totientQuotient r := by
    intro r
    unfold totientQuotient
    positivity
  have hsum : (∑ r ∈ S, totientQuotient r) ≤
      (R : ℝ) * (harmonic R : ℝ) ^ 4 := by
    calc
      (∑ r ∈ S, totientQuotient r) ≤
          ∑ r ∈ Finset.Icc 1 R, totientQuotient r := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hS
          (fun r hrI hrS => htq0 r)
      _ ≤ (R : ℝ) * (harmonic R : ℝ) ^ 4 :=
        sum_totientQuotient_Icc_le R
  have hsum0 : 0 ≤ ∑ r ∈ S, totientQuotient r := by
    exact Finset.sum_nonneg fun r hr => htq0 r
  unfold p53NormalizedEulerMass
  calc
    (∑ r ∈ S, ∑ r' ∈ S,
        (((r * r' : ℕ) : ℝ)⁻¹) *
          (lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ)) ≤
      ∑ r ∈ S, ∑ r' ∈ S,
        totientQuotient r * totientQuotient r' := by
      apply Finset.sum_le_sum
      intro r hr
      exact Finset.sum_le_sum (hterm r hr)
    _ = (∑ r ∈ S, totientQuotient r) ^ 2 := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
    _ ≤ ((R : ℝ) * (harmonic R : ℝ) ^ 4) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self hsum0 hsum
    _ = (R : ℝ) ^ 2 * (harmonic R : ℝ) ^ 8 := by ring

end
end MAPJutilaP53NormalizedEulerMassBound

#print axioms MAPJutilaP53NormalizedEulerMassBound.normalizedEulerMass_term_le_totientQuotient_mul
#print axioms MAPJutilaP53NormalizedEulerMassBound.p53NormalizedEulerMass_le_R_sq_mul_harmonic_pow_eight
