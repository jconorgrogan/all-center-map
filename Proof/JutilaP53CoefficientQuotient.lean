import JutilaGappedGrahamBypass
import JutilaP53PseudocharacterExactBridge

/-!
# The coefficient quotient in Jutila (3.6)

This file certifies the two elementary estimates hidden in the first passage
to (3.6).  First, on the literal source ranges, the two-scale exponential
difference in `b_n` is bounded below by an absolute constant.  Second, after
the pseudocharacter and exponential factors cancel, the remaining coefficient
quotient is bounded by the gapped divisor-square energy.
-/

namespace MAPJutilaP53CoefficientQuotient

open scoped BigOperators
open MAPJutilaGappedGrahamBypass
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53PseudocharacterExactBridge

noncomputable section

private theorem one_tenth_lt_exp_neg_half_sub_exp_neg_one :
    (1 / 10 : ℝ) < Real.exp (-(1 / 2 : ℝ)) - Real.exp (-1) := by
  have hhalf : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    nlinarith [Real.add_one_le_exp (-(1 / 2 : ℝ))]
  have hone : Real.exp (-1) < (2 / 5 : ℝ) :=
    Real.exp_neg_one_lt_d9.trans (by norm_num)
  linarith

private theorem one_tenth_lt_exp_neg_one_sub_exp_neg_two :
    (1 / 10 : ℝ) < Real.exp (-1) - Real.exp (-2) := by
  have honeLow : (1 / 3 : ℝ) < Real.exp (-1) :=
    (by norm_num : (1 / 3 : ℝ) < 0.36787944116).trans
      Real.exp_neg_one_gt_d9
  have honeHigh : Real.exp (-1) < (2 / 5 : ℝ) :=
    Real.exp_neg_one_lt_d9.trans (by norm_num)
  have hsq : Real.exp (-1) * Real.exp (-1) <
      (2 / 5 : ℝ) * (2 / 5 : ℝ) :=
    mul_self_lt_mul_self (Real.exp_pos (-1)).le honeHigh
  have hexpTwo : Real.exp (-2) = Real.exp (-1) * Real.exp (-1) := by
    rw [show (-2 : ℝ) = -1 + -1 by norm_num, Real.exp_add]
  rw [hexpTwo]
  nlinarith

/-- Uniform lower bound for the source smoothing difference.  The harmless
eventual separation `4*z1 ≤ x` is much weaker than Jutila's actual choices
`z1=D^(1/2+7 epsilon)` and `x=D^(1+12 epsilon) log^2 D`. -/
theorem one_tenth_le_source_exp_difference
    {M N z1 x n : ℝ}
    (hM : 0 < M) (hMz : M ≤ z1) (hz : 0 < z1)
    (hsep : 4 * z1 ≤ x) (hxN : x ≤ N)
    (hzn : z1 < n) (hnx : n ≤ x) :
    (1 / 10 : ℝ) ≤ Real.exp (-(n / N)) - Real.exp (-(n / M)) := by
  have hx : 0 < x := lt_of_lt_of_le (by nlinarith : 0 < 4 * z1) hsep
  have hN : 0 < N := hx.trans_le hxN
  have hn : 0 < n := hz.trans hzn
  by_cases hhalf : n ≤ x / 2
  · have hnN : n / N ≤ (1 / 2 : ℝ) := by
      rw [div_le_iff₀ hN]
      nlinarith
    have hfirst : Real.exp (-(1 / 2 : ℝ)) ≤ Real.exp (-(n / N)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hsecondArg : 1 ≤ n / M := by
      rw [le_div_iff₀ hM]
      simpa only [one_mul] using hMz.trans hzn.le
    have hsecond : Real.exp (-(n / M)) ≤ Real.exp (-1) :=
      Real.exp_le_exp.mpr (by linarith)
    exact le_of_lt (lt_of_lt_of_le
      one_tenth_lt_exp_neg_half_sub_exp_neg_one (by linarith))
  · have hnN : n / N ≤ 1 := by
      rw [div_le_one hN]
      exact hnx.trans hxN
    have hfirst : Real.exp (-1) ≤ Real.exp (-(n / N)) :=
      Real.exp_le_exp.mpr (by linarith)
    have htwoM : 2 * M ≤ n := by
      have : 2 * z1 ≤ x / 2 := by linarith
      nlinarith
    have hsecondArg : 2 ≤ n / M := by
      rw [le_div_iff₀ hM]
      exact htwoM
    have hsecond : Real.exp (-(n / M)) ≤ Real.exp (-2) :=
      Real.exp_le_exp.mpr (by linarith)
    exact le_of_lt (lt_of_lt_of_le
      one_tenth_lt_exp_neg_one_sub_exp_neg_two (by linarith))

/-- The real coefficient of the source polynomial `g(s+alpha,chi,x)` after
the character and the row-dependent complex power are moved into the Halasz
phase. -/
def jutilaP53DetectedCoefficientReal
    (z1 z2 alpha X : ℝ) (S : Finset ℕ) (n : ℕ) : ℝ :=
  jutilaDivisorCoefficient z1 z2 n *
    Real.exp (-((n : ℝ) / X)) *
    jutilaP53PseudoReal S n *
    Real.rpow (n : ℝ) (-alpha)

def jutilaP53DetectedCoefficient
    (z1 z2 alpha X : ℝ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  (jutilaP53DetectedCoefficientReal z1 z2 alpha X S n : ℂ)

theorem norm_jutilaP53DetectedCoefficient_sq
    {z1 z2 alpha X : ℝ} {S : Finset ℕ} {n : ℕ} (hn : 0 < n) :
    ‖jutilaP53DetectedCoefficient z1 z2 alpha X S n‖ ^ 2 =
      (jutilaDivisorCoefficient z1 z2 n) ^ 2 *
        (jutilaP53PseudoReal S n) ^ 2 *
        Real.exp (-2 * ((n : ℝ) / X)) *
        Real.rpow (n : ℝ) (-2 * alpha) := by
  have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast hn.le
  have hrpow : 0 ≤ Real.rpow (n : ℝ) (-alpha) :=
    Real.rpow_nonneg hn0 _
  have hexp : 0 ≤ Real.exp (-((n : ℝ) / X)) := (Real.exp_pos _).le
  unfold jutilaP53DetectedCoefficient jutilaP53DetectedCoefficientReal
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hexpSq : Real.exp (-((n : ℝ) / X)) ^ 2 =
      Real.exp (-2 * ((n : ℝ) / X)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hrpowSq : Real.rpow (n : ℝ) (-alpha) ^ 2 =
      Real.rpow (n : ℝ) (-2 * alpha) := by
    calc
      Real.rpow (n : ℝ) (-alpha) ^ 2 =
          Real.rpow (n : ℝ) ((-alpha) * (2 : ℝ)) := by
        exact (Real.rpow_mul_natCast hn0 (-alpha) 2).symm
      _ = Real.rpow (n : ℝ) (-2 * alpha) := by ring_nf
  rw [mul_pow, mul_pow, mul_pow, hexpSq, hrpowSq]
  ring

/-- Pointwise coefficient-quotient bound in Lemma 7.  It is stated directly
with the literal p.53 weight and therefore checks all cancellations, including
the real pseudocharacter factor. -/
theorem detectedCoefficient_div_correlationWeight_le
    {z1 z2 alpha X M N x : ℝ} {S : Finset ℕ} {n : ℕ}
    (hX : 0 < X) (hM : 0 < M) (hMz : M ≤ z1) (hz : 0 < z1)
    (hsep : 4 * z1 ≤ x) (hxN : x ≤ N)
    (hzn : z1 < (n : ℝ)) (hnx : (n : ℝ) ≤ x)
    (hP : jutilaP53PseudoReal S n ≠ 0) :
    ‖jutilaP53DetectedCoefficient z1 z2 alpha X S n‖ ^ 2 /
        jutilaP53CorrelationWeight S M N n ≤
      10 * (jutilaDivisorCoefficient z1 z2 n) ^ 2 *
        Real.rpow (n : ℝ) (1 - 2 * alpha) := by
  have hn : 0 < n := by
    have : (0 : ℝ) < n := hz.trans hzn
    exact_mod_cast this
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hMN : M < N := by
    have hx : 0 < x := lt_of_lt_of_le (by nlinarith : 0 < 4 * z1) hsep
    have hzx : z1 < x := hzn.trans_le hnx
    exact hMz.trans_lt (hzx.trans_le hxN)
  have hb :=
    MAPJutilaHalaszLargeValueFront.jutilaCorrelationWeight_pos
      hM hMN hn hP
  have hb' : 0 < jutilaP53CorrelationWeight S M N n := by
    simpa [jutilaP53CorrelationWeight] using hb
  rw [div_le_iff₀ hb']
  rw [norm_jutilaP53DetectedCoefficient_sq hn]
  unfold jutilaP53CorrelationWeight
  unfold MAPJutilaHalaszLargeValueFront.jutilaCorrelationWeight
  have hgap := one_tenth_le_source_exp_difference
    hM hMz hz hsep hxN hzn hnx
  have hexpLe : Real.exp (-2 * ((n : ℝ) / X)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (div_nonneg hnR.le hX.le)
  have hsplit :
      Real.rpow (n : ℝ) (1 - 2 * alpha) * (n : ℝ)⁻¹ =
        Real.rpow (n : ℝ) (-2 * alpha) := by
    calc
      Real.rpow (n : ℝ) (1 - 2 * alpha) * (n : ℝ)⁻¹ =
          Real.rpow (n : ℝ) (1 - 2 * alpha) *
            Real.rpow (n : ℝ) (-1) := by
        rw [show Real.rpow (n : ℝ) (-1) = (n : ℝ)⁻¹ by
          simpa using Real.rpow_neg_one (n : ℝ)]
      _ = Real.rpow (n : ℝ) ((1 - 2 * alpha) + -1) := by
        exact (Real.rpow_add hnR (1 - 2 * alpha) (-1)).symm
      _ = Real.rpow (n : ℝ) (-2 * alpha) := by
        congr 1
        ring
  have htenGap : 1 ≤ 10 *
      (Real.exp (-((n : ℝ) / N)) - Real.exp (-((n : ℝ) / M))) := by
    nlinarith
  have hsmooth : Real.exp (-2 * ((n : ℝ) / X)) ≤ 10 *
      (Real.exp (-((n : ℝ) / N)) - Real.exp (-((n : ℝ) / M))) :=
    hexpLe.trans htenGap
  have hcoeff0 : 0 ≤ (jutilaDivisorCoefficient z1 z2 n) ^ 2 := sq_nonneg _
  have hP0 : 0 ≤ (jutilaP53PseudoReal S n) ^ 2 := sq_nonneg _
  have hrpow0 : 0 ≤ Real.rpow (n : ℝ) (-2 * alpha) :=
    Real.rpow_nonneg hnR.le _
  calc
    (jutilaDivisorCoefficient z1 z2 n) ^ 2 *
          (jutilaP53PseudoReal S n) ^ 2 *
          Real.exp (-2 * ((n : ℝ) / X)) *
          Real.rpow (n : ℝ) (-2 * alpha) ≤
        (jutilaDivisorCoefficient z1 z2 n) ^ 2 *
          (jutilaP53PseudoReal S n) ^ 2 *
          (10 * (Real.exp (-((n : ℝ) / N)) -
            Real.exp (-((n : ℝ) / M)))) *
          Real.rpow (n : ℝ) (-2 * alpha) := by
      gcongr
    _ = 10 * (jutilaDivisorCoefficient z1 z2 n) ^ 2 *
          Real.rpow (n : ℝ) (1 - 2 * alpha) *
        ((n : ℝ)⁻¹ * (jutilaP53PseudoReal S n) ^ 2 *
          (Real.exp (-((n : ℝ) / N)) -
            Real.exp (-((n : ℝ) / M)))) := by rw [hsplit.symm]; ring

/-- The complete coefficient-quotient input for the integrated Halasz weld.
The sharp Graham asymptotic is absent: after the exact pointwise cancellation,
the elementary divisor-square harmonic bound loses only `log^4 x`. -/
theorem sum_detectedCoefficient_div_correlationWeight_le_logPow
    {z1 z2 alpha X M N : ℝ} {S cols : Finset ℕ} {x : ℕ}
    (hz1 : 1 < z1) (hz12 : z1 < z2) (halpha : alpha ≤ 1)
    (hx : 1 ≤ x) (hX : 0 < X)
    (hM : 0 < M) (hMz : M ≤ z1)
    (hsep : 4 * z1 ≤ (x : ℝ)) (hxN : (x : ℝ) ≤ N)
    (hcols : cols ⊆ Finset.Icc 1 x)
    (hzcols : ∀ n ∈ cols, z1 < (n : ℝ))
    (hP : ∀ n ∈ cols, jutilaP53PseudoReal S n ≠ 0) :
    (∑ n ∈ cols,
        ‖jutilaP53DetectedCoefficient z1 z2 alpha X S n‖ ^ 2 /
          jutilaP53CorrelationWeight S M N n) ≤
      10 * Real.rpow (x : ℝ) (2 - 2 * alpha) *
        (1 + Real.log (x : ℝ)) ^ 4 := by
  have hz : 0 < z1 := by linarith
  calc
    (∑ n ∈ cols,
        ‖jutilaP53DetectedCoefficient z1 z2 alpha X S n‖ ^ 2 /
          jutilaP53CorrelationWeight S M N n) ≤
        ∑ n ∈ cols,
          10 * (jutilaDivisorCoefficient z1 z2 n) ^ 2 *
            Real.rpow (n : ℝ) (1 - 2 * alpha) := by
      apply Finset.sum_le_sum
      intro n hn
      exact detectedCoefficient_div_correlationWeight_le
        hX hM hMz hz hsep hxN (hzcols n hn)
          (by exact_mod_cast (Finset.mem_Icc.mp (hcols hn)).2) (hP n hn)
    _ ≤ ∑ n ∈ Finset.Icc 1 x,
          10 * (jutilaDivisorCoefficient z1 z2 n) ^ 2 *
            Real.rpow (n : ℝ) (1 - 2 * alpha) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hcols
      intro n hn hnot
      exact mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = 10 * (∑ n ∈ Finset.Icc 1 x,
          (jutilaDivisorCoefficient z1 z2 n) ^ 2 *
            Real.rpow (n : ℝ) (1 - 2 * alpha)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ 10 * (Real.rpow (x : ℝ) (2 - 2 * alpha) *
          (1 + Real.log (x : ℝ)) ^ 4) := by
      exact mul_le_mul_of_nonneg_left
        (jutilaWeightedCoefficientEnergy_le_logPow hz1 hz12 halpha hx)
        (by norm_num)
    _ = 10 * Real.rpow (x : ℝ) (2 - 2 * alpha) *
          (1 + Real.log (x : ℝ)) ^ 4 := by ring

end

end MAPJutilaP53CoefficientQuotient

#print axioms MAPJutilaP53CoefficientQuotient.one_tenth_le_source_exp_difference
#print axioms MAPJutilaP53CoefficientQuotient.norm_jutilaP53DetectedCoefficient_sq
#print axioms MAPJutilaP53CoefficientQuotient.detectedCoefficient_div_correlationWeight_le
#print axioms MAPJutilaP53CoefficientQuotient.sum_detectedCoefficient_div_correlationWeight_le_logPow
