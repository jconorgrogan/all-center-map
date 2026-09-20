import RamachandraShiftedCoefficientEnergy

/-!
# A polylogarithmic Graham bypass on the gapped Jutila branch

The published proof invokes Graham's sharp Barban--Vehov asymptotic for the
quadratic divisor weight.  MAP's live collar has a weak zero-free gap, which
can absorb any fixed polylogarithmic loss.  For that route it is enough to
use the elementary bound `|lambda_d| ≤ 1`, dominate by the divisor function,
and invoke the already certified divisor-square harmonic mean.
-/

namespace MAPJutilaGappedGrahamBypass

open scoped BigOperators
open RamachandraShiftedCoefficientEnergy
open FixedCharacterPoweredBridge
open CGLProofDAG
open ShiuSelbergMainWeight

noncomputable section

/-- Jutila's piecewise logarithmic sieve coefficient from equations
(2.5)--(2.6), written with real sieve levels to avoid irrelevant rounding. -/
def jutilaLambda (z1 z2 : ℝ) (d : ℕ) : ℝ :=
  if (d : ℝ) < z1 then
    (ArithmeticFunction.moebius d : ℝ)
  else if (d : ℝ) ≤ z2 then
    (ArithmeticFunction.moebius d : ℝ) *
      (Real.log (z2 / (d : ℝ)) / Real.log (z2 / z1))
  else 0

/-- The only coefficient property needed by the gapped Graham bypass. -/
theorem abs_jutilaLambda_le_one
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2) (d : ℕ) :
    |jutilaLambda z1 z2 d| ≤ 1 := by
  unfold jutilaLambda
  split_ifs with hd1 hd2
  · exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  · have hz1le : z1 ≤ (d : ℝ) := le_of_not_gt hd1
    have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le (by linarith) hz1le
    have hz2pos : 0 < z2 := by linarith
    have hdenpos : 0 < Real.log (z2 / z1) := by
      apply Real.log_pos
      exact (one_lt_div (by linarith)).2 hz12
    have hnum0 : 0 ≤ Real.log (z2 / (d : ℝ)) := by
      apply Real.log_nonneg
      exact (one_le_div hdpos).2 hd2
    have hratio : z2 / (d : ℝ) ≤ z2 / z1 := by
      exact (div_le_div_iff_of_pos_left hz2pos hdpos (by linarith)).2 hz1le
    have hlog : Real.log (z2 / (d : ℝ)) ≤ Real.log (z2 / z1) := by
      exact Real.log_le_log (div_pos hz2pos hdpos) hratio
    have hquot0 : 0 ≤
        Real.log (z2 / (d : ℝ)) / Real.log (z2 / z1) := by positivity
    have hquot1 :
        Real.log (z2 / (d : ℝ)) / Real.log (z2 / z1) ≤ 1 :=
      (div_le_one hdenpos).2 hlog
    have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    rw [abs_mul, abs_of_nonneg hquot0]
    exact (mul_le_mul hmu hquot1 hquot0 (by norm_num)).trans_eq (mul_one 1)
  · simp

/-- Up to the lower sieve level, Jutila's piecewise coefficient is exactly
the Möbius function, including the endpoint. -/
theorem jutilaLambda_eq_moebius_of_le_z1
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    {d : ℕ} (hd : (d : ℝ) ≤ z1) :
    jutilaLambda z1 z2 d = (ArithmeticFunction.moebius d : ℝ) := by
  unfold jutilaLambda
  by_cases hdlt : (d : ℝ) < z1
  · rw [if_pos hdlt]
  · rw [if_neg hdlt]
    have hdeq : (d : ℝ) = z1 := le_antisymm hd (le_of_not_gt hdlt)
    have hdz2 : (d : ℝ) ≤ z2 := by linarith
    rw [if_pos hdz2, hdeq]
    have hden : Real.log (z2 / z1) ≠ 0 := by
      exact ne_of_gt (Real.log_pos ((one_lt_div (by linarith)).2 hz12))
    field_simp

def jutilaDivisorCoefficient (z1 z2 : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, jutilaLambda z1 z2 d

/-- The exact source assertion `a_1=1` and `a_n=0` on
`2 ≤ n ≤ z1`, obtained from finite Möbius cancellation. -/
theorem jutilaDivisorCoefficient_eq_kronecker_of_le_z1
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    {n : ℕ} (hn : (n : ℝ) ≤ z1) :
    jutilaDivisorCoefficient z1 z2 n = if n = 1 then 1 else 0 := by
  unfold jutilaDivisorCoefficient
  calc
    (∑ d ∈ n.divisors, jutilaLambda z1 z2 d) =
        ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hddiv
      apply jutilaLambda_eq_moebius_of_le_z1 hz1 hz12
      have hnpos : 0 < n :=
        Nat.pos_of_ne_zero (Nat.mem_divisors.mp hddiv).2
      have hdn : d ≤ n :=
        Nat.le_of_dvd hnpos (Nat.mem_divisors.mp hddiv).1
      exact (by exact_mod_cast hdn : (d : ℝ) ≤ n) |>.trans hn
    _ = if n = 1 then 1 else 0 := sum_moebius_divisors_real n

theorem jutilaDivisorCoefficient_one
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2) :
    jutilaDivisorCoefficient z1 z2 1 = 1 := by
  simpa using jutilaDivisorCoefficient_eq_kronecker_of_le_z1
    hz1 hz12 (show ((1 : ℕ) : ℝ) ≤ z1 by norm_num; linarith)

theorem jutilaDivisorCoefficient_zero_of_two_le
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    {n : ℕ} (hn2 : 2 ≤ n) (hn : (n : ℝ) ≤ z1) :
    jutilaDivisorCoefficient z1 z2 n = 0 := by
  rw [jutilaDivisorCoefficient_eq_kronecker_of_le_z1 hz1 hz12 hn,
    if_neg (by omega)]

def jutilaQuadraticDivisorWeight
    (lambda : ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x,
    (∑ d ∈ n.divisors, lambda d) ^ 2

theorem abs_divisorWeight_le_card
    (lambda : ℕ → ℝ) (hlambda : ∀ d : ℕ, |lambda d| ≤ 1)
    {n : ℕ} :
    |∑ d ∈ n.divisors, lambda d| ≤ n.divisors.card := by
  calc
    |∑ d ∈ n.divisors, lambda d| ≤
        ∑ d ∈ n.divisors, |lambda d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact hlambda d
    _ = n.divisors.card := by simp

theorem divisorWeight_sq_le_orderedDivisorCount_sq
    (lambda : ℕ → ℝ) (hlambda : ∀ d : ℕ, |lambda d| ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, lambda d) ^ 2 ≤
      (orderedDivisorCount 2 n : ℝ) ^ 2 := by
  have habs := abs_divisorWeight_le_card lambda hlambda (n := n)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [sq_abs] at hsq
  simpa [orderedDivisorCount_two_eq_card_divisors (Nat.ne_of_gt hn)] using hsq

/-- Elementary replacement for the sharp Graham asymptotic.  The loss is a
fixed fourth power of a harmonic number and is therefore harmless after the
live weak-gap absorption. -/
theorem jutilaQuadraticDivisorWeight_le
    (lambda : ℕ → ℝ) (hlambda : ∀ d : ℕ, |lambda d| ≤ 1)
    (x : ℕ) :
    jutilaQuadraticDivisorWeight lambda x ≤
      (x : ℝ) * (harmonic x : ℝ) ^ 4 := by
  have hpoint : ∀ n ∈ Finset.Icc 1 x,
      (∑ d ∈ n.divisors, lambda d) ^ 2 ≤
        (x : ℝ) * ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
    intro n hn
    have hnI := Finset.mem_Icc.mp hn
    have hnpos : 0 < n := by omega
    have hsq := divisorWeight_sq_le_orderedDivisorCount_sq
      lambda hlambda hnpos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hnx : (n : ℝ) ≤ x := by exact_mod_cast hnI.2
    have hscale : (1 : ℝ) ≤ (x : ℝ) / (n : ℝ) :=
      (one_le_div hnR).2 hnx
    have hcount0 : 0 ≤ (orderedDivisorCount 2 n : ℝ) ^ 2 := sq_nonneg _
    calc
      (∑ d ∈ n.divisors, lambda d) ^ 2 ≤
          (orderedDivisorCount 2 n : ℝ) ^ 2 := hsq
      _ ≤ ((x : ℝ) / (n : ℝ)) *
          (orderedDivisorCount 2 n : ℝ) ^ 2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hscale hcount0
      _ = (x : ℝ) *
          ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by ring
  calc
    jutilaQuadraticDivisorWeight lambda x ≤
        ∑ n ∈ Finset.Icc 1 x,
          (x : ℝ) * ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
      unfold jutilaQuadraticDivisorWeight
      exact Finset.sum_le_sum hpoint
    _ = (x : ℝ) *
        ∑ n ∈ Finset.Icc 1 x,
          ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
      rw [Finset.mul_sum]
    _ = (x : ℝ) *
        ∑ n ∈ Finset.Ioc 0 x,
          ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
      congr 2
    _ ≤ (x : ℝ) * (harmonic x : ℝ) ^ 4 := by
      exact mul_le_mul_of_nonneg_left
        (sum_orderedDivisorCount_two_sq_div_le x) (Nat.cast_nonneg x)

theorem jutilaQuadraticDivisorWeight_jutilaLambda_le
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2) (x : ℕ) :
    jutilaQuadraticDivisorWeight (jutilaLambda z1 z2) x ≤
      (x : ℝ) * (harmonic x : ℝ) ^ 4 := by
  exact jutilaQuadraticDivisorWeight_le (jutilaLambda z1 z2)
    (abs_jutilaLambda_le_one hz1 hz12) x

theorem jutilaQuadraticDivisorWeight_jutilaLambda_le_logPow
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    {x : ℕ} (hx : 1 ≤ x) :
    jutilaQuadraticDivisorWeight (jutilaLambda z1 z2) x ≤
      (x : ℝ) * (1 + Real.log (x : ℝ)) ^ 4 := by
  have hh := harmonic_le_one_add_log x
  have hh0 : 0 ≤ (harmonic x : ℝ) := by
    exact_mod_cast (harmonic_pos (by omega : x ≠ 0)).le
  have hpow := pow_le_pow_left₀ hh0 hh 4
  exact (jutilaQuadraticDivisorWeight_jutilaLambda_le hz1 hz12 x).trans
    (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg x))

/-- The coefficient quotient used in Jutila (3.6) needs no sharp Graham
asymptotic on the gapped route.  The source weight is
`n^(1-2*alpha) = n^(-1) * n^(2-2*alpha)`.  Since `alpha ≤ 1`, the second
factor is increasing and can be frozen at the upper endpoint; the remaining
divisor-square harmonic mean is already certified above. -/
theorem jutilaWeightedCoefficientEnergy_le_logPow
    {z1 z2 alpha : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    (halpha : alpha ≤ 1) {x : ℕ} (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Icc 1 x,
        (jutilaDivisorCoefficient z1 z2 n) ^ 2 *
          Real.rpow (n : ℝ) (1 - 2 * alpha)) ≤
      Real.rpow (x : ℝ) (2 - 2 * alpha) *
        (1 + Real.log (x : ℝ)) ^ 4 := by
  have hdelta : 0 ≤ 2 - 2 * alpha := by linarith
  have hpoint : ∀ n ∈ Finset.Icc 1 x,
      (jutilaDivisorCoefficient z1 z2 n) ^ 2 *
          Real.rpow (n : ℝ) (1 - 2 * alpha) ≤
        Real.rpow (x : ℝ) (2 - 2 * alpha) *
          ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
    intro n hn
    have hnI := Finset.mem_Icc.mp hn
    have hnpos : 0 < n := by omega
    have hnRpos : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hnx : (n : ℝ) ≤ x := by exact_mod_cast hnI.2
    have hpow :
        Real.rpow (n : ℝ) (2 - 2 * alpha) ≤
          Real.rpow (x : ℝ) (2 - 2 * alpha) :=
      Real.rpow_le_rpow hnRpos.le hnx hdelta
    have hsq :
        (jutilaDivisorCoefficient z1 z2 n) ^ 2 ≤
          (orderedDivisorCount 2 n : ℝ) ^ 2 := by
      exact divisorWeight_sq_le_orderedDivisorCount_sq
        (jutilaLambda z1 z2) (abs_jutilaLambda_le_one hz1 hz12) hnpos
    have hdiv :
        (jutilaDivisorCoefficient z1 z2 n) ^ 2 / (n : ℝ) ≤
          (orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ) :=
      div_le_div_of_nonneg_right hsq hnRpos.le
    have hsplit :
        Real.rpow (n : ℝ) (1 - 2 * alpha) =
          (n : ℝ)⁻¹ * Real.rpow (n : ℝ) (2 - 2 * alpha) := by
      rw [show 1 - 2 * alpha = -1 + (2 - 2 * alpha) by ring]
      calc
        Real.rpow (n : ℝ) (-1 + (2 - 2 * alpha)) =
            Real.rpow (n : ℝ) (-1) *
              Real.rpow (n : ℝ) (2 - 2 * alpha) := by
          exact Real.rpow_add hnRpos (-1) (2 - 2 * alpha)
        _ = (n : ℝ)⁻¹ * Real.rpow (n : ℝ) (2 - 2 * alpha) := by
          rw [show Real.rpow (n : ℝ) (-1) = (n : ℝ)⁻¹ by
            simpa using Real.rpow_neg_one (n : ℝ)]
    rw [hsplit]
    calc
      (jutilaDivisorCoefficient z1 z2 n) ^ 2 *
          ((n : ℝ)⁻¹ * Real.rpow (n : ℝ) (2 - 2 * alpha)) =
        Real.rpow (n : ℝ) (2 - 2 * alpha) *
          ((jutilaDivisorCoefficient z1 z2 n) ^ 2 / (n : ℝ)) := by ring
      _ ≤ Real.rpow (x : ℝ) (2 - 2 * alpha) *
          ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
        exact mul_le_mul hpow hdiv (by positivity)
          (Real.rpow_nonneg (Nat.cast_nonneg x) _)
  calc
    (∑ n ∈ Finset.Icc 1 x,
        (jutilaDivisorCoefficient z1 z2 n) ^ 2 *
          Real.rpow (n : ℝ) (1 - 2 * alpha)) ≤
        ∑ n ∈ Finset.Icc 1 x,
          Real.rpow (x : ℝ) (2 - 2 * alpha) *
            ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
      exact Finset.sum_le_sum hpoint
    _ = Real.rpow (x : ℝ) (2 - 2 * alpha) *
        ∑ n ∈ Finset.Icc 1 x,
          ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
      rw [Finset.mul_sum]
    _ = Real.rpow (x : ℝ) (2 - 2 * alpha) *
        ∑ n ∈ Finset.Ioc 0 x,
          ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
      congr 2
    _ ≤ Real.rpow (x : ℝ) (2 - 2 * alpha) *
        (harmonic x : ℝ) ^ 4 := by
      exact mul_le_mul_of_nonneg_left
        (sum_orderedDivisorCount_two_sq_div_le x)
        (Real.rpow_nonneg (Nat.cast_nonneg x) _)
    _ ≤ Real.rpow (x : ℝ) (2 - 2 * alpha) *
        (1 + Real.log (x : ℝ)) ^ 4 := by
      have hh := harmonic_le_one_add_log x
      have hh0 : 0 ≤ (harmonic x : ℝ) := by
        exact_mod_cast (harmonic_pos (by omega : x ≠ 0)).le
      have hpow4 := pow_le_pow_left₀ hh0 hh 4
      exact mul_le_mul_of_nonneg_left hpow4
        (Real.rpow_nonneg (Nat.cast_nonneg x) _)

end

end MAPJutilaGappedGrahamBypass

#print axioms MAPJutilaGappedGrahamBypass.jutilaQuadraticDivisorWeight_le
#print axioms MAPJutilaGappedGrahamBypass.abs_jutilaLambda_le_one
#print axioms MAPJutilaGappedGrahamBypass.jutilaDivisorCoefficient_eq_kronecker_of_le_z1
#print axioms MAPJutilaGappedGrahamBypass.jutilaQuadraticDivisorWeight_jutilaLambda_le_logPow
#print axioms MAPJutilaGappedGrahamBypass.jutilaWeightedCoefficientEnergy_le_logPow
