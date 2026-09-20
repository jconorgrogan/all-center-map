import GuthMaynardLemma118IntervalPacking
import CGLProofDAG

namespace GuthMaynardGMClassicalSmallN

open scoped BigOperators ComplexConjugate
open CGLProofDAG

noncomputable section

theorem norm_dirichletPolynomial_le_N
    {N : ℕ} {b : ℕ → ℂ} (hN : 1 ≤ N) (hb : ∀ n, ‖b n‖ ≤ 1) (t : ℝ) :
    ‖dirichletPolynomial b N t‖ ≤ N := by
  unfold dirichletPolynomial
  calc
    ‖∑ n ∈ Finset.Ioc N (2 * N),
        b n * Complex.exp (Complex.I * (t * Real.log n))‖ ≤
        ∑ n ∈ Finset.Ioc N (2 * N),
          ‖b n * Complex.exp (Complex.I * (t * Real.log n))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc N (2 * N), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hexp : ‖Complex.exp (Complex.I * (t * Real.log n))‖ = 1 := by
        simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (t * Real.log n)
      rw [norm_mul, hexp, mul_one]
      exact hb n
    _ = (N : ℝ) := by simp; omega

theorem card_le_two_mul_T_of_oneSeparated
    {T : ℝ} {W : Finset ℝ} (hT : 1 ≤ T)
    (hsep : OneSeparated W) (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T) :
    (W.card : ℝ) ≤ 2 * T := by
  have hpack := GuthMaynardLemma118.card_cast_le_one_add_div
    W 0 T 1 (by norm_num) (by linarith) (by
      intro x hx
      simpa using hheight x hx) (by
      intro x hx y hy hxy
      exact hsep x hx y hy hxy)
  nlinarith

theorem smallN_largeValue_cardinality
    {N₀ N : ℕ} {T V : ℝ} {b : ℕ → ℂ} {W : Finset ℝ}
    (hN₀ : 1 ≤ N₀) (hN : 1 ≤ N) (hNN₀ : (N : ℝ) ≤ N₀)
    (hT : 1 ≤ T) (hV : 0 < V) (hb : ∀ n, ‖b n‖ ≤ 1)
    (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T)
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖) :
    (W.card : ℝ) ≤ 2 * (N₀ : ℝ) ^ 2 * T * (N : ℝ) ^ 2 / V ^ 4 := by
  by_cases hW : W.Nonempty
  · obtain ⟨t, ht⟩ := hW
    have hVN : V ≤ (N : ℝ) :=
      (hlarge t ht).trans (norm_dirichletPolynomial_le_N hN hb t)
    have hcard := card_le_two_mul_T_of_oneSeparated hT hsep hheight
    have hN₀0 : 0 ≤ (N₀ : ℝ) := by positivity
    have hN0 : 0 ≤ (N : ℝ) := by positivity
    have hV4 : 0 < V ^ 4 := pow_pos hV 4
    have hV4N4 : V ^ 4 ≤ (N : ℝ) ^ 4 := by
      exact pow_le_pow_left₀ hV.le hVN 4
    have hN2 : (N : ℝ) ^ 2 ≤ (N₀ : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ hN0 hNN₀ 2
    have hN4 : (N : ℝ) ^ 4 ≤ (N₀ : ℝ) ^ 2 * (N : ℝ) ^ 2 := by
      calc
        (N : ℝ) ^ 4 = (N : ℝ) ^ 2 * (N : ℝ) ^ 2 := by ring
        _ ≤ (N₀ : ℝ) ^ 2 * (N : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hN2 (sq_nonneg _)
    have hfactor : 1 ≤ (N₀ : ℝ) ^ 2 * (N : ℝ) ^ 2 / V ^ 4 := by
      apply (le_div_iff₀ hV4).2
      simpa only [one_mul] using hV4N4.trans hN4
    have htarget : 2 * T ≤
        2 * (N₀ : ℝ) ^ 2 * T * (N : ℝ) ^ 2 / V ^ 4 := by
      have hmul := mul_le_mul_of_nonneg_left hfactor (by positivity : 0 ≤ 2 * T)
      convert hmul using 1 <;> ring
    exact hcard.trans htarget
  · have hcard : (W.card : ℝ) = 0 := by simp [Finset.not_nonempty_iff_eq_empty.mp hW]
    rw [hcard]
    positivity

theorem smallN_largeValue_cardinality_rpow
    {N₀ N : ℕ} {T V : ℝ} {b : ℕ → ℂ} {W : Finset ℝ}
    (hN₀ : 1 ≤ N₀) (hN : 1 ≤ N) (hNN₀ : (N : ℝ) ≤ N₀)
    (hT : 1 ≤ T) (hV : 0 < V) (hb : ∀ n, ‖b n‖ ≤ 1)
    (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T)
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖) :
    (W.card : ℝ) ≤ 2 * (N₀ : ℝ) ^ 2 * T *
      Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4 := by
  have hraw := smallN_largeValue_cardinality hN₀ hN hNN₀ hT hV hb hsep hheight hlarge
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpow := Real.rpow_le_rpow_of_exponent_le hN1
    (by norm_num : (2 : ℝ) ≤ 12 / 5)
  have hpow' : (N : ℝ) ^ 2 ≤ Real.rpow (N : ℝ) (12 / 5 : ℝ) := by
    simpa [Real.rpow_natCast] using hpow
  have hfactor : 0 ≤ 2 * (N₀ : ℝ) ^ 2 * T / V ^ 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hpow' hfactor
  calc
    (W.card : ℝ) ≤ 2 * (N₀ : ℝ) ^ 2 * T * (N : ℝ) ^ 2 / V ^ 4 := hraw
    _ = (2 * (N₀ : ℝ) ^ 2 * T / V ^ 4) * (N : ℝ) ^ 2 := by ring
    _ ≤ (2 * (N₀ : ℝ) ^ 2 * T / V ^ 4) * Real.rpow (N : ℝ) (12 / 5 : ℝ) := hmul
    _ = 2 * (N₀ : ℝ) ^ 2 * T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4 := by ring

end
end GuthMaynardGMClassicalSmallN

#print axioms GuthMaynardGMClassicalSmallN.norm_dirichletPolynomial_le_N
#print axioms GuthMaynardGMClassicalSmallN.smallN_largeValue_cardinality
#print axioms GuthMaynardGMClassicalSmallN.smallN_largeValue_cardinality_rpow
