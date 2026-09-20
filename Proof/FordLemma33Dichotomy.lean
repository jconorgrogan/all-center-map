import FordLemma33WeightedHolder

namespace FordLemma33Dichotomy

/-- The literal diagonal/off-diagonal split, with no claim that its inputs
have yet been produced for a particular counting problem. -/
theorem count_dichotomy_squared
    {k : ℕ} (hk : 1 ≤ k) {L D O M J K A B : ℝ}
    (hL : 0 ≤ L) (hO : 0 ≤ O) (hJ : 0 ≤ J) (hA : 0 ≤ A)
    (hsplit : L = D + O) (hdiag : D ≤ A * M)
    (hmoment : M ^ k ≤ L ^ (k - 1) * J)
    (hoff : O ^ 2 ≤ B ^ 2 * J * K) :
    L ^ 2 ≤ max (((2 * A) ^ k * J) ^ 2) (4 * B ^ 2 * J * K) := by
  by_cases hbranch : L ≤ 2 * D
  · have hlin : L ≤ (2 * A) * M := by nlinarith
    have hbound := FordLemma33WeightedHolder.scalar_moment_absorption
      hk hL hJ (by positivity : 0 ≤ 2 * A) hlin hmoment
    exact le_trans (pow_le_pow_left₀ hL hbound 2) (le_max_left _ _)
  · have hlin : L ≤ 2 * O := by linarith
    have hpow := pow_le_pow_left₀ hL hlin 2
    apply le_trans _ (le_max_right _ _)
    nlinarith

theorem count_dichotomy
    {k : ℕ} (hk : 1 ≤ k) {L D O M J K A B : ℝ}
    (hL : 0 ≤ L) (hO : 0 ≤ O) (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsplit : L = D + O) (hdiag : D ≤ A * M)
    (hmoment : M ^ k ≤ L ^ (k - 1) * J)
    (hoff : O ^ 2 ≤ B ^ 2 * J * K) :
    L ≤ max ((2 * A) ^ k * J) (2 * B * Real.sqrt (J * K)) := by
  by_cases hbranch : L ≤ 2 * D
  · have hlin : L ≤ (2 * A) * M := by nlinarith
    exact le_trans (FordLemma33WeightedHolder.scalar_moment_absorption
      hk hL hJ (by positivity : 0 ≤ 2 * A) hlin hmoment) (le_max_left _ _)
  · have hsqrt := Real.sq_sqrt (mul_nonneg hJ hK)
    have hsqrtnonneg := Real.sqrt_nonneg (J * K)
    have hbound : O ≤ B * Real.sqrt (J * K) := by
      have hmul : (B * Real.sqrt (J * K)) ^ 2 = B ^ 2 * J * K := by
        rw [mul_pow, hsqrt]
        ring
      have hnonneg : 0 ≤ B * Real.sqrt (J * K) := mul_nonneg hB hsqrtnonneg
      nlinarith
    apply le_trans _ (le_max_right _ _)
    linarith

end FordLemma33Dichotomy

#print axioms FordLemma33Dichotomy.count_dichotomy_squared
#print axioms FordLemma33Dichotomy.count_dichotomy
