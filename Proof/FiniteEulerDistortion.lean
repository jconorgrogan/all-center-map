import ShiuLemma4EndpointWeld
import PrimeDistortionChebyshev

/-!
# Complete finite Euler-product distortion for Shiu's Lemma 4

This module closes the literal finite Euler-product target isolated in
`ShiuLemma4TauTail`.  All constants are explicit.
-/

namespace ShiuFiniteEulerDistortion

open ShiuLemma4TauTail ShiuPrimeDistortionChebyshev ShiuLemma4EndpointWeld
open scoped BigOperators

noncomputable section

/-- The largest local parameter forced by `p ≥ 2` and `δ ≥ 3/4`. -/
def localCap : ℝ := (2 : ℝ) ^ (-(3 / 4 : ℝ))

/-- A uniform quadratic remainder constant for `-log(1-u)`. -/
def localQuadraticConstant : ℝ := (1 - localCap)⁻¹

theorem localCap_nonneg : 0 ≤ localCap := by
  exact Real.rpow_nonneg (by norm_num) _

theorem localCap_lt_one : localCap < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem localQuadraticConstant_nonneg : 0 ≤ localQuadraticConstant := by
  exact inv_nonneg.mpr (sub_nonneg.mpr localCap_lt_one.le)

/-- Generic local logarithmic majorant. -/
theorem inv_one_sub_le_exp_linear_add_quadratic
    {a u : ℝ} (_hu0 : 0 ≤ u) (hua : u ≤ a) (ha1 : a < 1) :
    (1 - u)⁻¹ ≤ Real.exp (u + (1 - a)⁻¹ * u ^ 2) := by
  have h1u : 0 < 1 - u := by linarith
  have h1a : 0 < 1 - a := by linarith
  have hinv : (1 - u)⁻¹ ≤ (1 - a)⁻¹ :=
    (inv_le_inv₀ h1u h1a).2 (by linarith)
  have hlog := Real.one_sub_inv_le_log_of_pos h1u
  have hneglog :
      -Real.log (1 - u) ≤ u + (1 - a)⁻¹ * u ^ 2 := by
    calc
      -Real.log (1 - u) ≤ (1 - u)⁻¹ - 1 := by linarith
      _ = u + (1 - u)⁻¹ * u ^ 2 := by
        field_simp
        ring
      _ ≤ u + (1 - a)⁻¹ * u ^ 2 := by
        gcongr
  calc
    (1 - u)⁻¹ = Real.exp (-Real.log (1 - u)) := by
      rw [Real.exp_neg, Real.exp_log h1u]
    _ ≤ Real.exp (u + (1 - a)⁻¹ * u ^ 2) :=
      Real.exp_le_exp.mpr hneglog

/-- Prime powers at `δ ≥ 3/4` lie in the fixed local interval. -/
theorem prime_rpow_neg_le_localCap
    {p : ℕ} (hp : p.Prime) {δ : ℝ} (hδ : 3 / 4 ≤ δ) :
    (p : ℝ) ^ (-δ) ≤ localCap := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc
    (p : ℝ) ^ (-δ) ≤ (2 : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    _ ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = localCap := rfl

/-- The local Euler factor used in the product. -/
theorem prime_local_euler_factor_le
    {p : ℕ} (hp : p.Prime) {δ : ℝ} (hδ : 3 / 4 ≤ δ) :
    (1 - (p : ℝ) ^ (-δ))⁻¹ ≤
      Real.exp ((p : ℝ) ^ (-δ) +
        localQuadraticConstant * ((p : ℝ) ^ (-δ)) ^ 2) := by
  exact inv_one_sub_le_exp_linear_add_quadratic
    (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    (prime_rpow_neg_le_localCap hp hδ) localCap_lt_one

/-- The square of a distorted prime power is bounded by `p^{-3/2}`. -/
theorem prime_rpow_neg_sq_le_three_halves
    {p : ℕ} (hp : p.Prime) {δ : ℝ} (hδ : 3 / 4 ≤ δ) :
    ((p : ℝ) ^ (-δ)) ^ 2 ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  calc
    ((p : ℝ) ^ (-δ)) ^ 2 = (p : ℝ) ^ ((-δ) * 2) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_mul (Nat.cast_nonneg p) (-δ) (2 : ℝ)).symm
    _ ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)

/-- Uniform finite quadratic budget, with the deliberately round constant `3`. -/
theorem sum_prime_rpow_neg_sq_le_three
    (y : ℕ) {δ : ℝ} (hδ : 3 / 4 ≤ δ) :
    (∑ p ∈ (y + 1).primesBelow, ((p : ℝ) ^ (-δ)) ^ 2) ≤ 3 := by
  have hsummable : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  calc
    (∑ p ∈ (y + 1).primesBelow, ((p : ℝ) ^ (-δ)) ^ 2) ≤
        ∑ p ∈ (y + 1).primesBelow, (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact prime_rpow_neg_sq_le_three_halves
        (Nat.prime_of_mem_primesBelow hp) hδ
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
      exact hsummable.sum_le_tsum _ (fun n hn => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ ≤ 3 := by
      have h := MAPMertensAnalyticLeaf.pSeries_le_one_add_inv_sub_one
        (show (1 : ℝ) < 3 / 2 by norm_num)
      norm_num at h
      exact h

/-! ## Linear distortion from exponent `1` to exponent `1-ε` -/

/-- Pointwise first-order comparison which keeps coefficient one on `1/p`. -/
theorem prime_rpow_one_sub_eps_le_inv_add_log
    {p : ℕ} (hp : p.Prime) {ε : ℝ} :
    (p : ℝ) ^ (-(1 - ε)) ≤
      (p : ℝ)⁻¹ + ε *
        (Real.log p * (p : ℝ) ^ (-(1 - ε))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  let u : ℝ := (p : ℝ) ^ (-(1 - ε))
  let x : ℝ := ε * Real.log (p : ℝ)
  have hu0 : 0 ≤ u := Real.rpow_nonneg hp0.le _
  have hbasic := Real.one_sub_le_exp_neg x
  have hmul := mul_le_mul_of_nonneg_left hbasic hu0
  have hux : u * Real.exp (-x) = (p : ℝ)⁻¹ := by
    dsimp [u, x]
    rw [Real.rpow_def_of_pos hp0, ← Real.exp_add]
    rw [show Real.log (p : ℝ) * (-(1 - ε)) +
        -(ε * Real.log (p : ℝ)) = -Real.log (p : ℝ) by ring,
      Real.exp_neg, Real.exp_log hp0]
  dsimp [u, x] at hmul ⊢
  rw [hux] at hmul
  nlinarith

/-- Finite masked summation of the coefficient-one comparison. -/
theorem masked_prime_rpow_sum_le_reciprocal_add_distortion
    (y modulus : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ p ∈ (y + 1).primesBelow,
        (if p ∣ modulus then 0 else (p : ℝ) ^ (-(1 - ε)))) ≤
      (∑ p ∈ (y + 1).primesBelow,
        (if p ∣ modulus then 0 else (p : ℝ)⁻¹)) +
        ε * primeLogRpowSum y (1 - ε) := by
  have hfirst :
      (∑ p ∈ (y + 1).primesBelow,
          (if p ∣ modulus then 0 else (p : ℝ) ^ (-(1 - ε)))) ≤
        ∑ p ∈ (y + 1).primesBelow,
          (if p ∣ modulus then 0 else
            (p : ℝ)⁻¹ + ε *
              (Real.log p * (p : ℝ) ^ (-(1 - ε)))) := by
    apply Finset.sum_le_sum
    intro p hp
    split
    · simp
    · exact prime_rpow_one_sub_eps_le_inv_add_log
        (Nat.prime_of_mem_primesBelow hp)
  calc
    (∑ p ∈ (y + 1).primesBelow,
        (if p ∣ modulus then 0 else (p : ℝ) ^ (-(1 - ε)))) ≤
      ∑ p ∈ (y + 1).primesBelow,
        (if p ∣ modulus then 0 else
          (p : ℝ)⁻¹ + ε *
            (Real.log p * (p : ℝ) ^ (-(1 - ε)))) := hfirst
    _ = (∑ p ∈ (y + 1).primesBelow,
          (if p ∣ modulus then 0 else (p : ℝ)⁻¹)) +
        ε * ∑ p ∈ (y + 1).primesBelow,
          (if p ∣ modulus then 0 else
            Real.log p * (p : ℝ) ^ (-(1 - ε))) := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      split <;> simp
    _ ≤ (∑ p ∈ (y + 1).primesBelow,
          (if p ∣ modulus then 0 else (p : ℝ)⁻¹)) +
        ε * primeLogRpowSum y (1 - ε) := by
      gcongr
      rw [primeLogRpowSum, Nat.primesBelow]
      apply Finset.sum_le_sum
      intro p hp
      split
      · have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
        exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hpprime.one_le))
          (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      · exact le_rfl

/-! ## Finite product weld -/

/-- The full finite product at a general exponent `δ ≥ 3/4`, before the
source-specific Chebyshev estimate is inserted. -/
theorem finiteEulerProduct_le_exp_linear_add_three_quadratic
    (k y modulus : ℕ) {δ : ℝ} (hδ : 3 / 4 ≤ δ) :
    (∏ p ∈ (y + 1).primesBelow,
        (if p ∣ modulus then 1
          else 1 / (1 - (p : ℝ) ^ (-δ)) ^ (k * k))) ≤
      Real.exp ((k * k : ℕ) *
        ((∑ p ∈ (y + 1).primesBelow,
            (if p ∣ modulus then 0 else (p : ℝ) ^ (-δ))) +
          3 * localQuadraticConstant)) := by
  have hpoint (p : ℕ) (hp : p ∈ (y + 1).primesBelow) :
      (if p ∣ modulus then 1
        else 1 / (1 - (p : ℝ) ^ (-δ)) ^ (k * k)) ≤
      Real.exp ((k * k : ℕ) *
        (if p ∣ modulus then 0 else
          (p : ℝ) ^ (-δ) +
            localQuadraticConstant * ((p : ℝ) ^ (-δ)) ^ 2)) := by
    have hpprime := Nat.prime_of_mem_primesBelow hp
    by_cases hpm : p ∣ modulus
    · simp [hpm]
    · rw [if_neg hpm, if_neg hpm]
      have hlocal := prime_local_euler_factor_le hpprime hδ
      have hu := prime_rpow_neg_le_localCap hpprime hδ
      have hden : 0 < 1 - (p : ℝ) ^ (-δ) := by
        linarith [localCap_lt_one]
      have hbase_nonneg : 0 ≤ (1 - (p : ℝ) ^ (-δ))⁻¹ :=
        inv_nonneg.mpr hden.le
      calc
        1 / (1 - (p : ℝ) ^ (-δ)) ^ (k * k) =
            ((1 - (p : ℝ) ^ (-δ))⁻¹) ^ (k * k) := by
          simp [one_div]
        _ ≤ (Real.exp ((p : ℝ) ^ (-δ) +
              localQuadraticConstant * ((p : ℝ) ^ (-δ)) ^ 2)) ^ (k * k) := by
          exact pow_le_pow_left₀ hbase_nonneg hlocal (k * k)
        _ = Real.exp ((k * k : ℕ) *
              ((p : ℝ) ^ (-δ) +
                localQuadraticConstant * ((p : ℝ) ^ (-δ)) ^ 2)) := by
          rw [← Real.exp_nat_mul]
  have hnonneg (p : ℕ) (hp : p ∈ (y + 1).primesBelow) :
      0 ≤ (if p ∣ modulus then 1
        else 1 / (1 - (p : ℝ) ^ (-δ)) ^ (k * k)) := by
    by_cases hpm : p ∣ modulus
    · simp [hpm]
    · rw [if_neg hpm]
      have hu := prime_rpow_neg_le_localCap
        (Nat.prime_of_mem_primesBelow hp) hδ
      have hden : 0 < 1 - (p : ℝ) ^ (-δ) := by
        linarith [localCap_lt_one]
      positivity
  calc
    (∏ p ∈ (y + 1).primesBelow,
        (if p ∣ modulus then 1
          else 1 / (1 - (p : ℝ) ^ (-δ)) ^ (k * k))) ≤
      ∏ p ∈ (y + 1).primesBelow,
        Real.exp ((k * k : ℕ) *
          (if p ∣ modulus then 0 else
            (p : ℝ) ^ (-δ) +
              localQuadraticConstant * ((p : ℝ) ^ (-δ)) ^ 2)) := by
        apply Finset.prod_le_prod₀ hnonneg
        exact hpoint
    _ = Real.exp (∑ p ∈ (y + 1).primesBelow,
        (k * k : ℕ) *
          (if p ∣ modulus then 0 else
            (p : ℝ) ^ (-δ) +
              localQuadraticConstant * ((p : ℝ) ^ (-δ)) ^ 2)) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp ((k * k : ℕ) *
        ((∑ p ∈ (y + 1).primesBelow,
            (if p ∣ modulus then 0 else (p : ℝ) ^ (-δ))) +
          3 * localQuadraticConstant)) := by
      apply Real.exp_le_exp.mpr
      rw [← Finset.mul_sum]
      gcongr
      calc
        (∑ p ∈ (y + 1).primesBelow,
            (if p ∣ modulus then 0 else
              (p : ℝ) ^ (-δ) +
                localQuadraticConstant * ((p : ℝ) ^ (-δ)) ^ 2)) =
          (∑ p ∈ (y + 1).primesBelow,
              (if p ∣ modulus then 0 else (p : ℝ) ^ (-δ))) +
            localQuadraticConstant *
              ∑ p ∈ (y + 1).primesBelow,
                (if p ∣ modulus then 0 else ((p : ℝ) ^ (-δ)) ^ 2) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro p hp
          split <;> simp
        _ ≤ (∑ p ∈ (y + 1).primesBelow,
              (if p ∣ modulus then 0 else (p : ℝ) ^ (-δ))) +
            localQuadraticConstant *
              ∑ p ∈ (y + 1).primesBelow,
                ((p : ℝ) ^ (-δ)) ^ 2 := by
          have hsqmask :
              (∑ p ∈ (y + 1).primesBelow,
                (if p ∣ modulus then 0 else ((p : ℝ) ^ (-δ)) ^ 2)) ≤
              ∑ p ∈ (y + 1).primesBelow, ((p : ℝ) ^ (-δ)) ^ 2 := by
            apply Finset.sum_le_sum
            intro p hp
            split
            · exact sq_nonneg _
            · exact le_rfl
          exact add_le_add_right
            (mul_le_mul_of_nonneg_left hsqmask localQuadraticConstant_nonneg) _
        _ ≤ (∑ p ∈ (y + 1).primesBelow,
              (if p ∣ modulus then 0 else (p : ℝ) ^ (-δ))) +
            3 * localQuadraticConstant := by
          have h := mul_le_mul_of_nonneg_left
            (sum_prime_rpow_neg_sq_le_three y hδ)
            localQuadraticConstant_nonneg
          exact add_le_add_right (by simpa [mul_comm] using h) _

/-! ## Source-specific product and unconditional finite endpoint -/

/-- The explicit constant depending only on `k` in the completed distortion
bound. -/
def explicitEulerDistortionConstant (k : ℕ) : ℝ :=
  Real.exp
    (3 * (k * k : ℕ) * localQuadraticConstant +
      10 * (((k * k : ℕ) : ℝ) * Real.log 4) ^ 2 + 1 / 40)

theorem explicitEulerDistortionConstant_pos (k : ℕ) :
    0 < explicitEulerDistortionConstant k := Real.exp_pos _

theorem one_le_explicitEulerDistortionConstant (k : ℕ) :
    1 ≤ explicitEulerDistortionConstant k := by
  exact Real.one_le_exp (by
    have hq := localQuadraticConstant_nonneg
    positivity)

/-- Complete finite Euler-product distortion at Shiu's exact exponent. -/
theorem finiteEulerDistortion_bound
    (k z y modulus : ℕ) (r : ℝ)
    (hz : 3 ≤ z) (hr : 1 ≤ r)
    (hrange : r * Real.log r ≤ Real.log (z : ℝ))
    (hy : 2 ≤ y)
    (hyz : (y : ℝ) ≤ (z : ℝ) ^ r⁻¹) :
    (∏ p ∈ (y + 1).primesBelow,
        (if p ∣ modulus then 1
          else 1 / (1 - (p : ℝ) ^ (-shiuDelta z r)) ^ (k * k))) ≤
      explicitEulerDistortionConstant k * Real.exp
        ((k * k : ℕ) * omittedPrimeInvSum y modulus +
          (1 / 40 : ℝ) * r * Real.log r) := by
  let K : ℝ := (k * k : ℕ)
  let ε : ℝ := r * Real.log r / (4 * Real.log (z : ℝ))
  let U : ℝ := ∑ p ∈ (y + 1).primesBelow,
    (if p ∣ modulus then 0 else (p : ℝ) ^ (-shiuDelta z r))
  let S : ℝ := omittedPrimeInvSum y modulus
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hdelta := shiuDelta_mem_threeQuarter_one hz1 hr hrange
  have hεnonneg : 0 ≤ ε := by
    dsimp [ε]
    have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
    have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos hz1
    positivity
  have hgeneric := finiteEulerProduct_le_exp_linear_add_three_quadratic
    k y modulus hdelta.1
  have hlinear := masked_prime_rpow_sum_le_reciprocal_add_distortion
    y modulus hεnonneg
  have hcheb := shiu_epsilon_mul_primeLogRpowSum_le_quarter_rpow
    hz1 hr hrange hy hyz
  have hU : U ≤ S + Real.log 4 * r ^ (1 / 4 : ℝ) := by
    have hdeltaeps : shiuDelta (z : ℝ) r = 1 - ε := by rfl
    dsimp [U, S]
    rw [hdeltaeps]
    exact hlinear.trans (add_le_add_right hcheb _)
  have hK : 0 ≤ K := by positivity
  have habs :=
    linear_quarter_rpow_le_constant_add_one_fortieth_mul_log
      (A := K * Real.log 4) hr
  have hexponent :
      K * (U + 3 * localQuadraticConstant) ≤
        (3 * K * localQuadraticConstant +
          10 * (K * Real.log 4) ^ 2 + 1 / 40) +
        (K * S + (1 / 40 : ℝ) * r * Real.log r) := by
    calc
      K * (U + 3 * localQuadraticConstant) ≤
          K * ((S + Real.log 4 * r ^ (1 / 4 : ℝ)) +
            3 * localQuadraticConstant) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hU _) hK
      _ = K * S + 3 * K * localQuadraticConstant +
          (K * Real.log 4) * r ^ (1 / 4 : ℝ) := by ring
      _ ≤ (3 * K * localQuadraticConstant +
            10 * (K * Real.log 4) ^ 2 + 1 / 40) +
          (K * S + (1 / 40 : ℝ) * r * Real.log r) := by
        nlinarith
  calc
    (∏ p ∈ (y + 1).primesBelow,
        (if p ∣ modulus then 1
          else 1 / (1 - (p : ℝ) ^ (-shiuDelta z r)) ^ (k * k))) ≤
      Real.exp ((k * k : ℕ) *
        ((∑ p ∈ (y + 1).primesBelow,
            (if p ∣ modulus then 0
              else (p : ℝ) ^ (-shiuDelta z r))) +
          3 * localQuadraticConstant)) := hgeneric
    _ ≤ Real.exp
        ((3 * K * localQuadraticConstant +
            10 * (K * Real.log 4) ^ 2 + 1 / 40) +
          (K * S + (1 / 40 : ℝ) * r * Real.log r)) :=
      Real.exp_le_exp.mpr hexponent
    _ = explicitEulerDistortionConstant k * Real.exp
        ((k * k : ℕ) * omittedPrimeInvSum y modulus +
          (1 / 40 : ℝ) * r * Real.log r) := by
      rw [Real.exp_add]
      rfl

/-- Shiu's finite Lemma-4 tail with the printed `-1/10` exponent, now with
no Euler-distortion premise. -/
theorem tauSquareSmoothTail_le_oneTenth
    (k z y modulus : ℕ) (r : ℝ)
    (hk : 1 ≤ k) (hz : 3 ≤ z) (hr : 1 ≤ r)
    (hrange : r * Real.log r ≤ Real.log (z : ℝ))
    (hy : 2 ≤ y)
    (hyz : (y : ℝ) ≤ (z : ℝ) ^ r⁻¹) :
    tauSquareSmoothTail k z y modulus ≤
      explicitEulerDistortionConstant k * Real.exp
        ((k * k : ℕ) * omittedPrimeInvSum y modulus -
          (1 / 10 : ℝ) * r * Real.log r) := by
  exact tauSquareSmoothTail_le_oneTenth_of_eulerDistortion
    k z y modulus r (explicitEulerDistortionConstant k)
    hk hz hr hrange (explicitEulerDistortionConstant_pos k).le
    (finiteEulerDistortion_bound k z y modulus r hz hr hrange hy hyz)

end
end ShiuFiniteEulerDistortion

#print axioms ShiuFiniteEulerDistortion.finiteEulerDistortion_bound
#print axioms ShiuFiniteEulerDistortion.tauSquareSmoothTail_le_oneTenth
