import MontgomeryTheorem83SmoothHalasz
import GammaMellinInversion

/-!
# Montgomery's smooth positive majorant

This file records the literal weight used in Montgomery's proof of the
large-values theorem (equation (33) of *Mean and Large Values of Dirichlet
Polynomials*, Invent. Math. 8 (1969), 334--345):

`5 * (exp (-(n/(2N))^k) - exp (-(n/N)^k))`.

The first source condition is proved here without an analytic premise: for
`k >= 1` the weight is positive everywhere away from zero and is at least
one on `N < n <= 2N`.  Consequently the hard dyadic coefficient energy is
dominated by the weighted smooth energy appearing in the Halasz argument.
-/

namespace MAPMontgomerySmoothMajorant

open scoped BigOperators
open MAPMontgomeryTheorem83SmoothHalasz
open MontgomeryVaughanFiniteReduction

noncomputable section

/-- Montgomery's equation-(33) weight, with real scale and exponent. -/
def montgomerySmoothWeight (N k : ℝ) (n : ℕ) : ℝ :=
  5 * (Real.exp (-Real.rpow ((n : ℝ) / (2 * N)) k) -
    Real.exp (-Real.rpow ((n : ℝ) / N) k))

/-- The elementary numerical core of Montgomery's condition (20).
Writing `y = exp(-x/2)`, the interval `1 <= x <= 2` puts
`1/3 <= y <= 2/3`, and hence `y-y^2 >= 2/9 > 1/5`. -/
private theorem five_mul_exp_half_sub_exp_ge_one
    {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    1 ≤ 5 * (Real.exp (-(x / 2)) - Real.exp (-x)) := by
  let y : ℝ := Real.exp (-(x / 2))
  have hExpOne : Real.exp 1 ≤ 3 :=
    Real.exp_one_lt_d9.le.trans (by norm_num)
  have hExpHalf : (3 / 2 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by
    have h := Real.add_one_le_exp (1 / 2 : ℝ)
    norm_num at h ⊢
    exact h
  have hyLower : (1 / 3 : ℝ) ≤ y := by
    have hmono : Real.exp (-1) ≤ Real.exp (-(x / 2)) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hbase : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
      rw [Real.exp_neg]
      simpa [one_div] using
        (one_div_le_one_div_of_le (Real.exp_pos 1) hExpOne)
    exact hbase.trans hmono
  have hyUpper : y ≤ (2 / 3 : ℝ) := by
    have hmono : Real.exp (-(x / 2)) ≤ Real.exp (-(1 / 2 : ℝ)) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hbase : Real.exp (-(1 / 2 : ℝ)) ≤ (2 / 3 : ℝ) := by
      rw [Real.exp_neg]
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 2)
        hExpHalf
      norm_num [one_div] at h ⊢
      exact h
    exact hmono.trans hbase
  have hyProduct : (2 / 9 : ℝ) ≤ y - y ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hyLower) (sub_nonneg.mpr hyUpper)]
  have hexpDouble : Real.exp (-x) = y ^ 2 := by
    have hx : -x = -(x / 2) + -(x / 2) := by ring
    rw [hx, Real.exp_add]
    simp [y, pow_two]
  rw [hexpDouble]
  change 1 ≤ 5 * (y - y ^ 2)
  nlinarith

/-- Raising the two bases in Montgomery's weight to any exponent `k >= 1`
only increases the gap between the two exponentials on `1 <= x <= 2`. -/
theorem montgomerySmoothWeight_ge_linearModel
    {N k x : ℝ} (hN : 0 < N) (hk : 1 ≤ k)
    (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    5 * (Real.exp (-Real.rpow (x / 2) k) - Real.exp (-Real.rpow x k)) ≥
      5 * (Real.exp (-(x / 2)) - Real.exp (-x)) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hhalf0 : 0 ≤ x / 2 := div_nonneg hx0 (by norm_num)
  have hhalf1 : x / 2 ≤ 1 := by linarith
  have hleftPow : Real.rpow (x / 2) k ≤ x / 2 :=
    Real.rpow_le_self_of_le_one hhalf0 hhalf1 hk
  have hrightPow : x ≤ Real.rpow x k :=
    Real.self_le_rpow_of_one_le hx1 hk
  have hleftExp : Real.exp (-(x / 2)) ≤
      Real.exp (-Real.rpow (x / 2) k) :=
    Real.exp_le_exp.mpr (neg_le_neg hleftPow)
  have hrightExp : Real.exp (-Real.rpow x k) ≤ Real.exp (-x) :=
    Real.exp_le_exp.mpr (neg_le_neg hrightPow)
  linarith

/-- Montgomery's smooth weight is at least one throughout the hard dyadic
interval.  This is the literal condition (20) used before the weighted
Halasz inequality. -/
theorem montgomerySmoothWeight_ge_one_on_real_dyadic
    {N k x : ℝ} (hN : 0 < N) (hk : 1 ≤ k)
    (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    1 ≤ 5 * (Real.exp (-Real.rpow (x / 2) k) -
      Real.exp (-Real.rpow x k)) := by
  exact (five_mul_exp_half_sub_exp_ge_one hx1 hx2).trans
    (montgomerySmoothWeight_ge_linearModel hN hk hx1 hx2)

/-- Natural-number form consumed by the dyadic character polynomial. -/
theorem montgomerySmoothWeight_ge_one_on_dyadic
    {N : ℕ} (hN : 1 ≤ N) {k : ℝ} (hk : 1 ≤ k)
    {n : ℕ} (hn : n ∈ dyadicSupport N) :
    1 ≤ montgomerySmoothWeight (N : ℝ) k n := by
  have hnBounds := Finset.mem_Ioc.mp hn
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  let x : ℝ := (n : ℝ) / (N : ℝ)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    rw [le_div_iff₀ hNpos]
    simpa using (show (N : ℝ) ≤ n by exact_mod_cast hnBounds.1.le)
  have hx2 : x ≤ 2 := by
    dsimp [x]
    rw [div_le_iff₀ hNpos]
    exact_mod_cast hnBounds.2
  have hmain := montgomerySmoothWeight_ge_one_on_real_dyadic hNpos hk hx1 hx2
  simpa [montgomerySmoothWeight, x, div_div, mul_comm, mul_left_comm,
    mul_assoc] using hmain

/-- The source weight is strictly positive at every positive integer. -/
theorem montgomerySmoothWeight_pos
    {N : ℝ} (hN : 0 < N) {k : ℝ} (hk : 0 < k)
    {n : ℕ} (hn : 0 < n) :
    0 < montgomerySmoothWeight N k n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : (n : ℝ) / (2 * N) < (n : ℝ) / N := by
    have h2N : 0 < 2 * N := mul_pos (by norm_num) hN
    rw [div_lt_div_iff₀ h2N hN]
    nlinarith
  have hpows : Real.rpow ((n : ℝ) / (2 * N)) k <
      Real.rpow ((n : ℝ) / N) k := by
    exact (Real.strictMonoOn_rpow_Ici_of_exponent_pos hk)
      (div_nonneg (le_of_lt hnR) (le_of_lt (mul_pos (by norm_num) hN)))
      (div_nonneg (le_of_lt hnR) hN.le) hbase
  unfold montgomerySmoothWeight
  have hexp : Real.exp (-Real.rpow ((n : ℝ) / N) k) <
      Real.exp (-Real.rpow ((n : ℝ) / (2 * N)) k) :=
    Real.exp_lt_exp.mpr (neg_lt_neg hpows)
  nlinarith

/-! ## Exact Mellin representation -/

/-- The normalized Gamma-line integral used twice in Montgomery's smooth
weight. -/
def gammaPowerLineIntegral (sigma x : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ,
      Complex.Gamma ((sigma : ℂ) + t * Complex.I) *
        (x : ℂ) ^ (-((sigma : ℂ) + t * Complex.I)))

/-- A source-equivalent form of Montgomery's equation (35), before the
change of vertical variable `w = k z`.  Keeping the standard Gamma line
avoids any hidden contour-orientation or Jacobian convention: both
exponentials in equation (33) are expanded by the already-certified inverse
Mellin theorem. -/
theorem montgomerySmoothWeight_eq_gamma_vertical_integrals
    {N sigma : ℝ} (hN : 0 < N) (hsigma : 0 < sigma)
    (k : ℝ) {n : ℕ} (hn : 0 < n) :
    (montgomerySmoothWeight N k n : ℂ) =
      5 *
        (gammaPowerLineIntegral sigma
            (Real.rpow ((n : ℝ) / (2 * N)) k) -
          gammaPowerLineIntegral sigma
            (Real.rpow ((n : ℝ) / N) k)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hleftBase : 0 < (n : ℝ) / (2 * N) :=
    div_pos hnR (mul_pos (by norm_num) hN)
  have hrightBase : 0 < (n : ℝ) / N := div_pos hnR hN
  have hleftPow : 0 < Real.rpow ((n : ℝ) / (2 * N)) k :=
    Real.rpow_pos_of_pos hleftBase k
  have hrightPow : 0 < Real.rpow ((n : ℝ) / N) k :=
    Real.rpow_pos_of_pos hrightBase k
  have hleft := MAPGammaMellinInversion.exp_neg_eq_gamma_vertical_integral
    hsigma hleftPow
  have hright := MAPGammaMellinInversion.exp_neg_eq_gamma_vertical_integral
    hsigma hrightPow
  unfold montgomerySmoothWeight
  rw [Complex.ofReal_mul, Complex.ofReal_sub]
  unfold gammaPowerLineIntegral
  rw [hleft, hright]
  norm_num

/-- Exact hard-to-smooth coefficient-energy domination for Montgomery's
equation-(33) majorant on any finite positive carrier. -/
theorem padded_montgomery_weightedEnergy_le
    {N : ℕ} (hN : 1 ≤ N) (tail : Finset ℕ)
    (htailPos : ∀ n ∈ smoothCarrier N tail, 0 < n)
    (a : ℕ → ℂ) {k : ℝ} (hk : 1 ≤ k) :
    (∑ n ∈ smoothCarrier N tail,
        ‖paddedDyadicCoefficient N a n‖ ^ 2 /
          montgomerySmoothWeight (N : ℝ) k n) ≤
      coefficientEnergy a N := by
  apply padded_weightedCoefficientEnergy_le tail a
    (montgomerySmoothWeight (N : ℝ) k)
  · intro n hn
    exact montgomerySmoothWeight_pos
      (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN))
      (zero_lt_one.trans_le hk) (htailPos n hn)
  · intro n hn
    exact montgomerySmoothWeight_ge_one_on_dyadic hN hk hn

end
end MAPMontgomerySmoothMajorant

#print axioms MAPMontgomerySmoothMajorant.montgomerySmoothWeight_ge_one_on_dyadic
#print axioms MAPMontgomerySmoothMajorant.montgomerySmoothWeight_pos
#print axioms MAPMontgomerySmoothMajorant.montgomerySmoothWeight_eq_gamma_vertical_integrals
#print axioms MAPMontgomerySmoothMajorant.padded_montgomery_weightedEnergy_le
