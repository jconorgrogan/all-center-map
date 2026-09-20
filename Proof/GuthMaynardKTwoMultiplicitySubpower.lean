import GuthMaynardPoweringKTwo
import ShiuAnalyticLayer

/-!
# Premise-free subpower control of the `k = 2` product multiplicity

The low/intermediate part of Heath--Brown's large-values argument uses
`A₂(N)`, the largest number of representations `n = m₁m₂` with both factors
in `(N,2N]`.  This file proves the exact elementary reduction

`A₂(N) ≤ τ₂(n)`

at an extremizing product, and then applies the already-certified
premise-free subpolynomial bound for `τ₂²`.  No prime distribution or
large-values theorem occurs here.
-/

namespace GuthMaynardKTwoMultiplicitySubpower

open MixedMellinCert
open GuthMaynardPoweringKTwo
open GuthMaynardLengthComparison
open ShiuFoundation
open ShiuAnalyticLayer

noncomputable section

/-- Projection to the first coordinate injects the literal product fiber
into the positive divisors of its product. -/
theorem productMultiplicity_le_card_divisors
    {N : ℝ} (hN : 0 ≤ N) {n : ℕ} (hn : 0 < n) :
    productMultiplicity N n ≤ n.divisors.card := by
  unfold productMultiplicity
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqmem : q.1 ∈ realDyadicIoc N ∧ q.2 ∈ realDyadicIoc N := by
      simpa using hq'.1
    exact Nat.mem_divisors.mpr ⟨⟨q.2, hq'.2.symm⟩, hn.ne'⟩
  · intro a ha b hb hab
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    apply Prod.ext hab
    have haMem : a.1 ∈ realDyadicIoc N := by
      have := (Finset.mem_product.mp ha'.1).1
      simpa using this
    have haPos : 0 < a.1 := by
      have haLower := (mem_realDyadicIoc_iff.mp haMem).1
      exact_mod_cast hN.trans_lt haLower
    have hmul : a.1 * a.2 = a.1 * b.2 := by
      calc
        a.1 * a.2 = n := ha'.2
        _ = b.1 * b.2 := hb'.2.symm
        _ = a.1 * b.2 := by rw [hab]
    exact Nat.mul_left_cancel haPos hmul

/-- For positive `n`, the order-two convolution divisor function is the
ordinary positive divisor count. -/
theorem tauAF_two_eq_card_divisors {n : ℕ} (hn : 0 < n) :
    tauAF 2 n = n.divisors.card := by
  rw [show 2 = 1 + 1 by omega, tauAF_succ_apply]
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hd0 : d ≠ 0 := fun h => hn.ne' (by simpa [h] using hdvd)
  simp [tauAF, ArithmeticFunction.zeta_apply, hd0]

/-- The literal product multiplicity is bounded by `τ₂`. -/
theorem productMultiplicity_le_tauAF_two
    {N : ℝ} (hN : 0 ≤ N) {n : ℕ} (hn : 0 < n) :
    productMultiplicity N n ≤ tauAF 2 n := by
  rw [tauAF_two_eq_card_divisors hn]
  exact productMultiplicity_le_card_divisors hN hn

/-- Premise-free fixed-exponent control of the exact maximum `A₂(N)²`.
The base `4N²` is the literal upper endpoint of the product range. -/
theorem maxProductMultiplicity_square_subpolynomial :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N →
        (maxProductMultiplicity N : ℝ) ^ 2 ≤
          C * Real.rpow (4 * N ^ 2) epsilon := by
  intro epsilon hepsilon
  obtain ⟨C, hC, htau⟩ :=
    tauAF_square_subpolynomial 2 (by norm_num) epsilon hepsilon
  refine ⟨C, hC, ?_⟩
  intro N hN
  by_cases hnonempty : (productIoc N).Nonempty
  · obtain ⟨n, hnmem, hnsup⟩ :=
      Finset.exists_mem_eq_sup (productIoc N) hnonempty (productMultiplicity N)
    have hbounds := mem_productIoc_iff.mp hnmem
    have hnposReal : 0 < (n : ℝ) :=
      (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hN)).trans hbounds.1
    have hnpos : 0 < n := by exact_mod_cast hnposReal
    have hmult := productMultiplicity_le_tauAF_two
      (le_trans zero_le_one hN) hnpos
    have hmultReal : (productMultiplicity N n : ℝ) ≤ (tauAF 2 n : ℝ) := by
      exact_mod_cast hmult
    have hmultSq : (productMultiplicity N n : ℝ) ^ 2 ≤
        (tauAF 2 n : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hmultReal 2
    have htauN := htau n hnpos
    have hbase : 0 ≤ (n : ℝ) := by positivity
    have hmono : Real.rpow (n : ℝ) epsilon ≤
        Real.rpow (4 * N ^ 2) epsilon :=
      Real.rpow_le_rpow hbase hbounds.2 hepsilon.le
    have hmax : maxProductMultiplicity N = productMultiplicity N n := by
      simpa [maxProductMultiplicity] using hnsup
    calc
      (maxProductMultiplicity N : ℝ) ^ 2 =
          (productMultiplicity N n : ℝ) ^ 2 := by rw [hmax]
      _ ≤ (tauAF 2 n : ℝ) ^ 2 := hmultSq
      _ ≤ C * Real.rpow (n : ℝ) epsilon := htauN
      _ ≤ C * Real.rpow (4 * N ^ 2) epsilon :=
        mul_le_mul_of_nonneg_left hmono hC.le
  · have hempty : productIoc N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    have hbase : 0 ≤ 4 * N ^ 2 := by positivity
    simp [maxProductMultiplicity, hempty,
      mul_nonneg hC.le (Real.rpow_nonneg hbase _)]

end

end GuthMaynardKTwoMultiplicitySubpower

#print axioms GuthMaynardKTwoMultiplicitySubpower.productMultiplicity_le_tauAF_two
#print axioms GuthMaynardKTwoMultiplicitySubpower.maxProductMultiplicity_square_subpolynomial
