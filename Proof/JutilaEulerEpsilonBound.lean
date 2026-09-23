import Mathlib

/-! # Uniform epsilon bound for the ambient finite Euler factor -/
namespace MAPJutilaEulerEpsilonBound
open scoped BigOperators
noncomputable section

/-- A finite prime cutoff absorbs every factor of two into `q^eta`, except
for at most `K` small primes. The constant is uniform in the modulus. -/
theorem two_pow_primeFactors_card_le_of_cutoff
    {eta : ℝ} (heta : 0 < eta) {K : ℕ}
    (hK : Real.rpow 2 eta⁻¹ ≤ (K : ℝ))
    (q : ℕ) (hq : 0 < q) :
    (2 : ℝ)^q.primeFactors.card ≤ (2 : ℝ)^K * Real.rpow (q : ℝ) eta := by
  let small := q.primeFactors.filter (fun p => p < K)
  let large := q.primeFactors.filter (fun p => ¬ p < K)
  have hsmall : small.card ≤ K := by
    calc
      small.card ≤ (Finset.range K).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = K := Finset.card_range K
  have hcard : small.card + large.card = q.primeFactors.card := by
    simpa [small, large] using
      (Finset.card_filter_add_card_filter_not
        (s := q.primeFactors) (p := fun p => p < K))
  have hlarge : (2 : ℝ)^large.card ≤ Real.rpow (∏ p ∈ large, (p : ℝ)) eta := by
    have heq := Real.finsetProd_rpow large (fun p => (p : ℝ))
      (fun p hp => Nat.cast_nonneg p) eta
    change (2 : ℝ)^large.card ≤ (∏ p ∈ large, (p : ℝ)) ^ eta
    rw [← heq, ← Finset.prod_const]
    apply Finset.prod_le_prod₀ (fun p hp => by norm_num)
    intro p hp
    have hKp : K ≤ p := Nat.le_of_not_gt (Finset.mem_filter.mp hp).2
    have hpbound : Real.rpow 2 eta⁻¹ ≤ (p : ℝ) :=
      hK.trans (Nat.cast_le.mpr hKp)
    have hb := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hpbound heta.le
    simpa [Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 2) heta.ne'] using hb
  have hsubset : large ⊆ q.primeFactors := Finset.filter_subset _ _
  have hprod : (∏ p ∈ large, (p : ℝ)) ≤ (q : ℝ) := by
    have hnat : (∏ p ∈ large, p) ≤ q :=
      (Finset.prod_le_prod_of_subset_of_one_le' hsubset
        (fun p hp hnot => (Nat.prime_of_mem_primeFactors hp).one_le)).trans
          (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))
    simpa only [Nat.cast_prod] using (Nat.cast_le (α := ℝ)).mpr hnat
  calc
    (2 : ℝ)^q.primeFactors.card = (2 : ℝ)^small.card * (2 : ℝ)^large.card := by
      rw [← hcard, pow_add]
    _ ≤ (2 : ℝ)^K * Real.rpow (∏ p ∈ large, (p : ℝ)) eta :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num) hsmall) hlarge
        (by positivity) (by positivity)
    _ ≤ (2 : ℝ)^K * Real.rpow (q : ℝ) eta :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Finset.prod_nonneg fun p hp => Nat.cast_nonneg p) hprod heta.le)
        (by positivity)

/-- Arbitrarily small power loss for the ambient Euler factor, with a single
positive constant valid for every positive natural modulus. -/
theorem exists_two_pow_primeFactors_card_le_rpow
    {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q →
      (2 : ℝ)^q.primeFactors.card ≤ C * Real.rpow (q : ℝ) eta := by
  obtain ⟨K, hK⟩ := exists_nat_ge (Real.rpow 2 eta⁻¹)
  exact ⟨(2 : ℝ)^K, by positivity,
    fun q hq => two_pow_primeFactors_card_le_of_cutoff heta hK q hq⟩

end
end MAPJutilaEulerEpsilonBound
#print axioms MAPJutilaEulerEpsilonBound.exists_two_pow_primeFactors_card_le_rpow
