import ShiuAnalyticLayer
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Elementary Euler-product leaves for the coefficient-one Mertens bound

This module does not assert Mertens' theorem.  It builds the positive real
Euler product and the p-series upper estimate used in a direct proof.
-/

namespace MAPMertensAnalyticLeaf

open Set
open scoped BigOperators

noncomputable section

/-- The positive real completely multiplicative summand `n ↦ n^{-s}`. -/
def realRpowSummandHom (s : ℝ) (hs : s ≠ 0) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    simpa only [Nat.cast_mul] using
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)

@[simp] theorem realRpowSummandHom_apply (s : ℝ) (hs : s ≠ 0) (n : ℕ) :
    realRpowSummandHom s hs n = (n : ℝ) ^ (-s) := by
  simp [realRpowSummandHom]

/-- Absolute summability of the real p-series summand. -/
theorem summable_realRpowSummandHom {s : ℝ} (hs : 1 < s) :
    Summable (realRpowSummandHom s (by linarith)) := by
  simpa [realRpowSummandHom] using
    Real.summable_nat_rpow.mpr (by linarith : -s < -1)

/-- Every finite positive Euler product equals the sum over the corresponding
smooth positive integers. -/
theorem finiteEulerProduct_eq_smooth_tsum
    {s : ℝ} (hs : 1 < s) (P : Finset ℕ) :
    ∏ p ∈ P with p.Prime,
        (1 - realRpowSummandHom s (by linarith) p)⁻¹ =
      ∑' m : Nat.factoredNumbers P,
        realRpowSummandHom s (by linarith) m :=
  EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers
    (summable_realRpowSummandHom hs) P

/-- A finite Euler product is bounded by the full positive p-series. -/
theorem finiteEulerProduct_le_pSeries
    {s : ℝ} (hs : 1 < s) (P : Finset ℕ) :
    ∏ p ∈ P with p.Prime,
        (1 - realRpowSummandHom s (by linarith) p)⁻¹ ≤
      ∑' n : ℕ, realRpowSummandHom s (by linarith) n := by
  rw [finiteEulerProduct_eq_smooth_tsum hs P]
  apply Summable.tsum_le_tsum_of_inj
    (fun m : Nat.factoredNumbers P => (m : ℕ))
    Subtype.coe_injective
  · intro n hn
    simpa [realRpowSummandHom] using Real.rpow_nonneg (Nat.cast_nonneg n) (-s)
  · intro m
    exact le_rfl
  · exact (summable_realRpowSummandHom hs).comp_injective Subtype.coe_injective
  · exact summable_realRpowSummandHom hs

/-- A completely explicit integral-test upper bound for the full positive
`p`-series.  The coefficient of `(s - 1)⁻¹` is exactly one. -/
theorem pSeries_le_one_add_inv_sub_one {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, (n : ℝ) ^ (-s)) ≤ 1 + (s - 1)⁻¹ := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  · intro n
    by_cases hn : n ≤ 1
    · have hrhs : 0 ≤ 1 + (s - 1)⁻¹ := by positivity
      interval_cases n
      · simpa using hrhs
      · simpa [Real.zero_rpow (by linarith : -s ≠ 0)] using hrhs
    · have h2 : 2 ≤ n := by omega
      have hsplit :
          (∑ i ∈ Finset.range n, (i : ℝ) ^ (-s)) =
            1 + ∑ i ∈ Finset.Ico 2 n, (i : ℝ) ^ (-s) := by
        rw [← Finset.sum_range_add_sum_Ico
          (f := fun i : ℕ => (i : ℝ) ^ (-s)) h2]
        norm_num [Finset.sum_range_succ,
          Real.zero_rpow (by linarith : -s ≠ 0)]
      rw [hsplit]
      gcongr
      have hshift :
          (∑ i ∈ Finset.Ico 2 n, (i : ℝ) ^ (-s)) =
            ∑ i ∈ Finset.Ico 1 (n - 1), ((i + 1 : ℕ) : ℝ) ^ (-s) := by
        symm
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ n), add_comm] using
          (Finset.sum_Ico_add (fun i : ℕ => (i : ℝ) ^ (-s)) 1 (n - 1) 1)
      rw [hshift]
      calc
        (∑ i ∈ Finset.Ico 1 (n - 1), ((i + 1 : ℕ) : ℝ) ^ (-s)) ≤
            ∫ x in (1 : ℝ)..(n - 1 : ℕ), x ^ (-s) := by
          have hanti : AntitoneOn (fun x : ℝ => x ^ (-s))
              (Set.Icc (((1 : ℕ) : ℝ)) (((n - 1 : ℕ) : ℝ))) :=
            (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
              (by linarith : -s ≤ 0)).mono
              (by
                intro x hx
                exact hx.1.trans_lt' (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ)))
          simpa only [Nat.cast_add, Nat.cast_one] using
            (AntitoneOn.sum_le_integral_Ico
              (f := fun x : ℝ => x ^ (-s))
              (by omega : 1 ≤ n - 1) hanti)
        _ = (((n - 1 : ℕ) : ℝ) ^ (-s + 1) - 1) / (-s + 1) := by
          rw [integral_rpow]
          · simp
          · right
            constructor
            · linarith
            · rw [uIcc_of_le (by exact_mod_cast (show 1 ≤ n - 1 by omega))]
              simp
        _ ≤ (s - 1)⁻¹ := by
          have hden : 0 < s - 1 := by linarith
          have hpow : 0 ≤ (((n - 1 : ℕ) : ℝ) ^ (-(s - 1))) :=
            Real.rpow_nonneg (by positivity) _
          rw [show -s + 1 = -(s - 1) by ring, div_neg]
          rw [← neg_div, neg_sub]
          rw [inv_eq_one_div]
          have hnum : 1 - (((n - 1 : ℕ) : ℝ) ^ (-(s - 1))) ≤ 1 := by
            linarith
          exact div_le_div_of_nonneg_right hnum hden.le

/-- The finite smooth-number Euler product has the expected simple-pole
upper bound, with no analytic continuation and no number-theoretic input. -/
theorem finiteEulerProduct_le_one_add_inv_sub_one
    {s : ℝ} (hs : 1 < s) (P : Finset ℕ) :
    ∏ p ∈ P with p.Prime,
        (1 - realRpowSummandHom s (by linarith) p)⁻¹ ≤
      1 + (s - 1)⁻¹ :=
  (finiteEulerProduct_le_pSeries hs P).trans
    (by simpa [realRpowSummandHom] using pSeries_le_one_add_inv_sub_one hs)

/-! ## A coefficient-preserving Chebyshev--Abel estimate -/

/-- The weighted prime sum needed to compare `p⁻¹` with a nearby convergent
Euler product. -/
def primeLogReciprocalSum (x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime,
    Real.log p / (p : ℝ)

/-- Abel summation for the weighted prime reciprocal sum, with literal
endpoints. -/
theorem primeLogReciprocalSum_eq_theta_div_add_integral
    {x : ℕ} (hx : 2 ≤ x) :
    primeLogReciprocalSum x =
      Chebyshev.theta (x : ℝ) / x +
        ∫ t in (2 : ℝ)..x, Chebyshev.theta t / t ^ 2 := by
  let a : ℕ → ℝ := Set.indicator (setOf Nat.Prime) (fun n ↦ Real.log n)
  rw [primeLogReciprocalSum]
  trans ∑ n ∈ Finset.Icc 0 x, (n : ℝ)⁻¹ * a n
  · rw [Nat.range_succ_eq_Icc_zero, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : n.Prime
    · have ha : a n = Real.log n :=
        Set.indicator_of_mem (s := setOf Nat.Prime) (f := fun m => Real.log m) h
      rw [if_pos h, ha, div_eq_mul_inv, mul_comm]
    · have ha : a n = 0 :=
        Set.indicator_of_notMem (s := setOf Nat.Prime) (f := fun m => Real.log m) h
      rw [if_neg h, ha, mul_zero]
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x,
      DifferentiableAt ℝ (fun z : ℝ => z⁻¹) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact differentiableAt_inv ht0
  have hderivfun : deriv (fun z : ℝ => z⁻¹) = fun t => -(t ^ 2)⁻¹ := by
    funext t
    exact deriv_inv
  have hint : MeasureTheory.IntegrableOn (deriv (fun z : ℝ => z⁻¹))
      (Set.Icc (2 : ℝ) x) := by
    rw [hderivfun]
    exact ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousAt.continuousWithinAt (by
        have ht0 : t ≠ 0 := by linarith [ht.1]
        exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).neg)
  have habel := sum_mul_eq_sub_integral_mul₁ a (by simp [a]) (by simp [a])
    (x : ℝ) hdiff hint
  rw [Nat.floor_natCast] at habel
  have hsum (y : ℝ) :
      (∑ k ∈ Finset.Icc 0 ⌊y⌋₊, a k) = Chebyshev.theta y := by
    rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : n.Prime
    · have ha : a n = Real.log n :=
        Set.indicator_of_mem (s := setOf Nat.Prime) (f := fun m => Real.log m) h
      rw [if_pos h, ha]
    · have ha : a n = 0 :=
        Set.indicator_of_notMem (s := setOf Nat.Prime) (f := fun m => Real.log m) h
      rw [if_neg h, ha]
  have hsumx : (∑ k ∈ Finset.Icc 0 x, a k) = Chebyshev.theta (x : ℝ) := by
    simpa using hsum (x : ℝ)
  rw [habel, hsumx, ← intervalIntegral.integral_of_le (by exact_mod_cast hx)]
  simp_rw [hsum]
  rw [hderivfun]
  have hintegrand :
      (fun t : ℝ => -(t ^ 2)⁻¹ * Chebyshev.theta t) =
        fun t : ℝ => -(Chebyshev.theta t / t ^ 2) := by
    funext t
    ring
  rw [hintegrand, intervalIntegral.integral_neg, inv_mul_eq_div]
  ring

/-- Local integrability of the Chebyshev integrand in the preceding Abel
identity. -/
theorem integrableOn_theta_div_sq (x : ℝ) :
    MeasureTheory.IntegrableOn (fun t => Chebyshev.theta t / t ^ 2)
      (Set.Icc 2 x) MeasureTheory.volume := by
  conv =>
    arg 1
    ext
    rw [Chebyshev.theta, div_eq_mul_one_div, mul_comm, Finset.sum_filter]
  refine integrableOn_mul_sum_Icc _ (by norm_num) <|
    ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousAt.continuousWithinAt ?_
  have ht0 : t ≠ 0 := by linarith [ht.1]
  exact continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 ht0)

/-- An explicit Chebyshev-level `O(log x)` bound for the weighted prime sum.
The exact constant is not optimized. -/
theorem primeLogReciprocalSum_le
    {x : ℕ} (hx : 2 ≤ x) :
    primeLogReciprocalSum x ≤ Real.log 4 * (1 + Real.log (x : ℝ)) := by
  rw [primeLogReciprocalSum_eq_theta_div_add_integral hx]
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hx)
  have hxreal : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hfirst : Chebyshev.theta (x : ℝ) / x ≤ Real.log 4 := by
    apply (div_le_iff₀ hxpos).2
    simpa [mul_comm] using Chebyshev.theta_le_log4_mul_x hxpos.le
  have hsource : IntervalIntegrable (fun t => Chebyshev.theta t / t ^ 2)
      MeasureTheory.volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxreal,
      ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact integrableOn_theta_div_sq (x : ℝ)
  have htarget : IntervalIntegrable (fun t : ℝ => Real.log 4 / t)
      MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : t ≠ 0 := by
      rw [Set.uIcc_of_le hxreal] at ht
      linarith [ht.1]
    exact ContinuousAt.continuousWithinAt
      (continuousAt_const.div continuousAt_id ht0)
  have hintegral :
      (∫ t in (2 : ℝ)..x, Chebyshev.theta t / t ^ 2) ≤
        ∫ t in (2 : ℝ)..x, Real.log 4 / t := by
    apply intervalIntegral.integral_mono_on hxreal hsource htarget
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    calc
      Chebyshev.theta t / t ^ 2 ≤ (Real.log 4 * t) / t ^ 2 :=
        div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x htpos.le)
          (sq_nonneg t)
      _ = Real.log 4 / t := by field_simp
  calc
    Chebyshev.theta (x : ℝ) / x +
        ∫ t in (2 : ℝ)..x, Chebyshev.theta t / t ^ 2 ≤
      Real.log 4 + ∫ t in (2 : ℝ)..x, Real.log 4 / t :=
        add_le_add hfirst hintegral
    _ = Real.log 4 + Real.log 4 * Real.log ((x : ℝ) / 2) := by
      rw [show (fun t : ℝ => Real.log 4 / t) =
          fun t => Real.log 4 * t⁻¹ by
        funext t
        rw [div_eq_mul_inv], intervalIntegral.integral_const_mul,
        integral_inv_of_pos (by norm_num) hxpos]
    _ ≤ Real.log 4 * (1 + Real.log (x : ℝ)) := by
      have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      have hdivle : (x : ℝ) / 2 ≤ x := by linarith
      have hdivpos : 0 < (x : ℝ) / 2 := div_pos hxpos (by norm_num)
      have hlogle : Real.log ((x : ℝ) / 2) ≤ Real.log (x : ℝ) :=
        Real.log_le_log hdivpos hdivle
      nlinarith

/-! ## Nearby Euler product and the coefficient-one comparison -/

/-- The convergent prime-power sum at exponent `s`. -/
def primeRpowSum (x : ℕ) (s : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (p : ℝ) ^ (-s)

/-- The elementary inequality `exp u ≤ (1-u)⁻¹` for `u < 1`. -/
theorem exp_le_inv_one_sub {u : ℝ} (hu1 : u < 1) :
    Real.exp u ≤ (1 - u)⁻¹ := by
  have h := (inv_le_inv₀ (Real.exp_pos (-u)) (sub_pos.mpr hu1)).2
    (Real.one_sub_le_exp_neg u)
  simpa [Real.exp_neg] using h

/-- Exponentiating the prime sum is dominated termwise by its finite Euler
product. -/
theorem exp_primeRpowSum_le_finiteEulerProduct
    {x : ℕ} {s : ℝ} (hs : 1 < s) :
    Real.exp (primeRpowSum x s) ≤
      ∏ p ∈ Finset.range (x + 1) with p.Prime,
        (1 - realRpowSummandHom s (by linarith) p)⁻¹ := by
  rw [primeRpowSum, Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro p hp
    exact (Real.exp_pos _).le
  · intro p hp
    have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
    have hpone : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
    have hu1 : (p : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hpone (by linarith)
    simpa [realRpowSummandHom] using exp_le_inv_one_sub hu1

/-- The nearby prime sum has a logarithmic simple-pole bound. -/
theorem primeRpowSum_le_log_one_add_inv
    {x : ℕ} {s : ℝ} (hs : 1 < s) :
    primeRpowSum x s ≤ Real.log (1 + (s - 1)⁻¹) := by
  have hprod := (exp_primeRpowSum_le_finiteEulerProduct (x := x) hs).trans
    (finiteEulerProduct_le_one_add_inv_sub_one hs (Finset.range (x + 1)))
  have hrhs : 0 < 1 + (s - 1)⁻¹ := by positivity
  exact (Real.le_log_iff_exp_le hrhs).2 hprod

/-- Pointwise comparison of a prime reciprocal with a nearby convergent
power, retaining the coefficient one on the reciprocal. -/
theorem prime_inv_le_nearby_rpow_add
    {p : ℕ} (hp : p.Prime) (δ : ℝ) :
    (p : ℝ)⁻¹ ≤ (p : ℝ) ^ (-(1 + δ)) +
      δ * (Real.log p / (p : ℝ)) := by
  have hpreal : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hone : 1 ≤ Real.exp (-(δ * Real.log p)) + δ * Real.log p := by
    linarith [Real.one_sub_le_exp_neg (δ * Real.log p)]
  have hmul := mul_le_mul_of_nonneg_left hone (inv_nonneg.mpr hpreal.le)
  calc
    (p : ℝ)⁻¹ = (p : ℝ)⁻¹ * 1 := by ring
    _ ≤ (p : ℝ)⁻¹ * (Real.exp (-(δ * Real.log p)) + δ * Real.log p) :=
      hmul
    _ = (p : ℝ) ^ (-(1 + δ)) + δ * (Real.log p / (p : ℝ)) := by
      rw [mul_add]
      have hrpow : (p : ℝ) ^ (-(1 + δ)) =
          (p : ℝ)⁻¹ * Real.exp (-(δ * Real.log p)) := by
        rw [show -(1 + δ) = -1 + -δ by ring,
          Real.rpow_add hpreal, Real.rpow_neg_one,
          Real.rpow_def_of_pos hpreal]
        congr 2
        ring
      rw [hrpow]
      ring

/-- Finite summation of the pointwise nearby-Euler-product comparison. -/
theorem primeReciprocalSum_le_nearbyRpow_add
    {x : ℕ} (δ : ℝ) :
    ShiuAnalyticLayer.primeReciprocalSum x ≤
      primeRpowSum x (1 + δ) + δ * primeLogReciprocalSum x := by
  classical
  rw [ShiuAnalyticLayer.primeReciprocalSum, primeRpowSum,
    primeLogReciprocalSum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  exact prime_inv_le_nearby_rpow_add (Finset.mem_filter.mp hp).2 δ

/-- A fully kernel-checked coefficient-one Mertens upper bound, with an
explicit nonoptimized constant and no prime number theorem. -/
theorem primeReciprocalSum_le_loglog_add_explicit
    {x : ℕ} (hx : 3 ≤ x) :
    ShiuAnalyticLayer.primeReciprocalSum x ≤
      Real.log (Real.log (x : ℝ)) + (1 + 2 * Real.log 4) := by
  let L : ℝ := Real.log (x : ℝ)
  let δ : ℝ := L⁻¹
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 3) hx)
  have hthree : (3 : ℝ) ≤ x := by exact_mod_cast hx
  have hLone : 1 < L := by
    rw [show L = Real.log (x : ℝ) by rfl, ← Real.exp_lt_exp]
    rw [Real.exp_log hxpos]
    exact Real.exp_one_lt_three.trans_le hthree
  have hLpos : 0 < L := zero_lt_one.trans hLone
  have hδpos : 0 < δ := inv_pos.mpr hLpos
  have hs : 1 < 1 + δ := by linarith
  have hcompare := primeReciprocalSum_le_nearbyRpow_add (x := x) δ
  have hrpow : primeRpowSum x (1 + δ) ≤ Real.log (1 + L) := by
    have h := primeRpowSum_le_log_one_add_inv (x := x) hs
    have hδinv : δ⁻¹ = L := by simp [δ]
    simpa [hδinv] using h
  have hweighted : primeLogReciprocalSum x ≤ Real.log 4 * (1 + L) := by
    simpa [L] using primeLogReciprocalSum_le (show 2 ≤ x by omega)
  have hdeltaWeighted : δ * primeLogReciprocalSum x ≤ 2 * Real.log 4 := by
    calc
      δ * primeLogReciprocalSum x ≤ δ * (Real.log 4 * (1 + L)) :=
        mul_le_mul_of_nonneg_left hweighted hδpos.le
      _ = Real.log 4 * (1 + L⁻¹) := by
        rw [show δ = L⁻¹ by rfl]
        field_simp
        ring
      _ ≤ 2 * Real.log 4 := by
        have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        have hLinv : L⁻¹ ≤ 1 := (inv_le_one₀ hLpos).2 hLone.le
        nlinarith
  have hlognear : Real.log (1 + L) ≤ Real.log L + 1 := by
    apply (Real.log_le_iff_le_exp (by linarith)).2
    rw [Real.exp_add, Real.exp_log hLpos]
    nlinarith [Real.exp_one_gt_two]
  calc
    ShiuAnalyticLayer.primeReciprocalSum x ≤
        primeRpowSum x (1 + δ) + δ * primeLogReciprocalSum x := hcompare
    _ ≤ Real.log (1 + L) + 2 * Real.log 4 :=
      add_le_add hrpow hdeltaWeighted
    _ ≤ Real.log L + (1 + 2 * Real.log 4) := by linarith
    _ = Real.log (Real.log (x : ℝ)) + (1 + 2 * Real.log 4) := by rfl

/-- The divisor-square Euler exponential with an explicit constant, obtained
by feeding the certified coefficient-one Mertens bound into the exact Shiu
weight identity. -/
theorem exp_tauAFSquarePrimeReciprocalSum_le_explicit
    (k x : ℕ) (hx : 3 ≤ x) :
    Real.exp (ShiuAnalyticLayer.tauAFSquarePrimeReciprocalSum k x) ≤
      Real.exp ((k ^ 2 : ℕ) * (1 + 2 * Real.log 4)) *
        (Real.log (x : ℝ)) ^ (k ^ 2) := by
  exact ShiuAnalyticLayer.exp_tauAFSquarePrimeReciprocalSum_le_of_mertensAt
    k x (show 1 < x by omega) (primeReciprocalSum_le_loglog_add_explicit hx)

end
end MAPMertensAnalyticLeaf
