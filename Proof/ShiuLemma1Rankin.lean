import MertensAnalyticLeaf
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.SmoothNumbers

/-!
# Shiu's Lemma 1: the elementary Rankin layer

Shiu writes `Ψ(x,y)` for the number of positive integers `n ≤ x` whose
prime factors are all at most `y`.  The primary-source statement is

`Ψ(x, log x * log log x) ≤ exp (3 * log x / sqrt (log log x))`

for all sufficiently large real `x`.  The proof has two logically separate
parts:

* the finite Rankin injection and the Euler product, proved below;
* an upper bound for `∑_{p ≤ y} 1 / log p` and elementary real asymptotics.

The definitions here use natural endpoints, but the inequalities are in
`ℝ`.  `Nat.smoothNumbers (y+1)` is exactly the set of nonzero integers all
of whose prime factors are `< y+1`, hence at most `y`.
-/

namespace ShiuLemma1Rankin

open Set
open scoped BigOperators

noncomputable section

/-- The literal finite version of Shiu's `Ψ(x,y)`. -/
def smoothCount (x y : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter fun n => n ∈ Nat.smoothNumbers (y + 1)).card

/-- The finite set counted by `smoothCount`. -/
def smoothFinset (x y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n => n ∈ Nat.smoothNumbers (y + 1)

@[simp] theorem card_smoothFinset (x y : ℕ) :
    (smoothFinset x y).card = smoothCount x y := rfl

/-- Shiu's prime sum in equation (4.1), with the endpoint made finite and
natural. -/
def primeInvLogSum (y : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (y + 1)).filter Nat.Prime,
    (Real.log (p : ℝ))⁻¹

/-- A counted smooth integer, regarded as an integer factored over the finite
set `range (y+1)`. -/
def smoothEmbedding (x y : ℕ) :
    {n // n ∈ smoothFinset x y} ↪ Nat.factoredNumbers (Finset.range (y + 1)) where
  toFun n := ⟨n, by
    have hn : (n : ℕ) ∈ Nat.smoothNumbers (y + 1) :=
      (Finset.mem_filter.mp n.property).2
    simpa only [Nat.smoothNumbers_eq_factoredNumbers] using hn⟩
  inj' := by
    intro m n h
    apply Subtype.ext
    exact congrArg
      (fun z : Nat.factoredNumbers (Finset.range (y + 1)) => (z : ℕ)) h

/-- At every positive exponent, the finite Euler product over primes at most
`y` is the sum of `n^{-δ}` over all `y`-smooth positive integers.  Unlike a
full Dirichlet series, this needs no hypothesis `δ > 1`. -/
theorem finiteEulerProduct_eq_smoothTsum
    {δ : ℝ} (hδ : 0 < δ) (y : ℕ) :
    ∏ p ∈ Finset.range (y + 1) with p.Prime,
        (1 - MAPMertensAnalyticLeaf.realRpowSummandHom δ hδ.ne' p)⁻¹ =
      ∑' m : Nat.factoredNumbers (Finset.range (y + 1)),
        MAPMertensAnalyticLeaf.realRpowSummandHom δ hδ.ne' m := by
  have hlocal : ∀ {p : ℕ}, p.Prime →
      ‖MAPMertensAnalyticLeaf.realRpowSummandHom δ hδ.ne' p‖ < 1 := by
    intro p hp
    have hpone : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    rw [MAPMertensAnalyticLeaf.realRpowSummandHom_apply,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hpone (by linarith)
  exact (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    hlocal (Finset.range (y + 1))).2.tsum_eq.symm

/-- A local Euler factor is bounded by the exponential used in Rankin's
argument. -/
theorem inv_one_sub_prime_rpow_le_exp
    {δ : ℝ} (hδ : 0 < δ) {p : ℕ} (hp : p.Prime) :
    (1 - (p : ℝ) ^ (-δ))⁻¹ ≤
      Real.exp ((((p : ℝ) ^ δ) - 1)⁻¹) := by
  have hpone : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  let a : ℝ := (p : ℝ) ^ δ
  have ha1 : 1 < a := Real.one_lt_rpow hpone hδ
  have ha0 : 0 < a := lt_trans (by norm_num) ha1
  have hsub : 0 < a - 1 := sub_pos.mpr ha1
  have hinvlt : a⁻¹ < 1 := (inv_lt_one₀ ha0).2 ha1
  have hone : 1 - a⁻¹ ≠ 0 := ne_of_gt (sub_pos.mpr hinvlt)
  have ha0' : a ≠ 0 := ha0.ne'
  have hsub' : a - 1 ≠ 0 := hsub.ne'
  have hid : (1 - a⁻¹)⁻¹ = 1 + (a - 1)⁻¹ := by
    field_simp
    ring
  rw [Real.rpow_neg hp0.le, show (p : ℝ) ^ δ = a by rfl, hid]
  simpa [add_comm] using Real.add_one_le_exp ((a - 1)⁻¹)

/-- The elementary denominator comparison
`(p^δ-1)⁻¹ ≤ δ⁻¹ (log p)⁻¹`. -/
theorem inv_prime_rpow_sub_one_le
    {δ : ℝ} (hδ : 0 < δ) {p : ℕ} (hp : p.Prime) :
    ((((p : ℝ) ^ δ) - 1)⁻¹) ≤
      δ⁻¹ * (Real.log (p : ℝ))⁻¹ := by
  have hpone : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hpone
  have hprod : 0 < δ * Real.log (p : ℝ) := mul_pos hδ hlog
  have hden : δ * Real.log (p : ℝ) ≤ (p : ℝ) ^ δ - 1 := by
    rw [Real.rpow_def_of_pos hp0]
    rw [show Real.log (p : ℝ) * δ = δ * Real.log (p : ℝ) by ring]
    linarith [Real.add_one_le_exp (δ * Real.log (p : ℝ))]
  calc
    ((((p : ℝ) ^ δ) - 1)⁻¹) ≤ (δ * Real.log (p : ℝ))⁻¹ :=
      (inv_le_inv₀ (sub_pos.mpr (Real.one_lt_rpow hpone hδ)) hprod).2 hden
    _ = δ⁻¹ * (Real.log (p : ℝ))⁻¹ := by rw [mul_inv_rev, mul_comm]

/-- The finite Euler product is bounded by the exponential of Shiu's
weighted prime count. -/
theorem finiteEulerProduct_le_exp_primeInvLogSum
    {δ : ℝ} (hδ : 0 < δ) (y : ℕ) :
    ∏ p ∈ Finset.range (y + 1) with p.Prime,
        (1 - MAPMertensAnalyticLeaf.realRpowSummandHom δ hδ.ne' p)⁻¹ ≤
      Real.exp (δ⁻¹ * primeInvLogSum y) := by
  rw [primeInvLogSum, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro p hp
    have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
    have hpone : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
    have hlt : (p : ℝ) ^ (-δ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hpone (by linarith)
    rw [MAPMertensAnalyticLeaf.realRpowSummandHom_apply]
    positivity
  · intro p hp
    have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
    calc
      (1 - MAPMertensAnalyticLeaf.realRpowSummandHom δ hδ.ne' p)⁻¹ ≤
          Real.exp ((((p : ℝ) ^ δ) - 1)⁻¹) := by
        simpa [MAPMertensAnalyticLeaf.realRpowSummandHom_apply] using
          inv_one_sub_prime_rpow_le_exp hδ hpprime
      _ ≤ Real.exp (δ⁻¹ * (Real.log (p : ℝ))⁻¹) :=
        Real.exp_le_exp.mpr (inv_prime_rpow_sub_one_le hδ hpprime)

/-- The load-bearing finite Rankin inequality in Shiu's Lemma 1.  This is the
whole smooth-number argument before the prime-sum estimate is inserted. -/
theorem smoothCount_le_rankinEulerProduct
    {δ : ℝ} (hδ : 0 < δ) (x y : ℕ) :
    (smoothCount x y : ℝ) ≤
      (x : ℝ) ^ δ *
        ∏ p ∈ Finset.range (y + 1) with p.Prime,
          (1 - MAPMertensAnalyticLeaf.realRpowSummandHom δ hδ.ne' p)⁻¹ := by
  let F := smoothFinset x y
  let e := smoothEmbedding x y
  let g : Nat.factoredNumbers (Finset.range (y + 1)) → ℝ := fun m =>
    MAPMertensAnalyticLeaf.realRpowSummandHom δ hδ.ne' m
  have hlocal : ∀ {p : ℕ}, p.Prime →
      ‖MAPMertensAnalyticLeaf.realRpowSummandHom δ hδ.ne' p‖ < 1 := by
    intro p hp
    have hpone : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    rw [MAPMertensAnalyticLeaf.realRpowSummandHom_apply,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hpone (by linarith)
  have hEuler :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      hlocal (Finset.range (y + 1))
  have hsum_le :
      (∑ n : {n // n ∈ smoothFinset x y},
          ((n : ℕ) : ℝ) ^ (-δ)) ≤ ∑' m, g m := by
    have hfinite : Summable (fun n : {n // n ∈ smoothFinset x y} =>
        (((n : ℕ) : ℝ) ^ (-δ))) :=
      (hasSum_fintype fun n : {n // n ∈ smoothFinset x y} =>
        (((n : ℕ) : ℝ) ^ (-δ))).summable
    have hg : Summable g := by
      exact hEuler.2.summable
    have hge (n : {n // n ∈ smoothFinset x y}) :
        g (e n) = ((n : ℕ) : ℝ) ^ (-δ) := by
      change MAPMertensAnalyticLeaf.realRpowSummandHom δ hδ.ne' (n : ℕ) = _
      exact MAPMertensAnalyticLeaf.realRpowSummandHom_apply δ hδ.ne' (n : ℕ)
    have hinj : (∑' n : {n // n ∈ smoothFinset x y},
        ((n : ℕ) : ℝ) ^ (-δ)) ≤ ∑' m, g m :=
      Summable.tsum_le_tsum_of_inj e e.injective
        (fun m _ => by
          change 0 ≤ MAPMertensAnalyticLeaf.realRpowSummandHom δ hδ.ne' (m : ℕ)
          rw [MAPMertensAnalyticLeaf.realRpowSummandHom_apply]
          exact Real.rpow_nonneg (Nat.cast_nonneg (m : ℕ)) (-δ))
        (fun n => (hge n).symm.le) hfinite hg
    simpa only [tsum_fintype] using hinj
  have hpoint (n : {n // n ∈ smoothFinset x y}) :
      (1 : ℝ) ≤ (x : ℝ) ^ δ * (((n : ℕ) : ℝ) ^ (-δ)) := by
    have hnmem := (Finset.mem_filter.mp n.property).1
    have hn1 : 1 ≤ (n : ℕ) := (Finset.mem_Icc.mp hnmem).1
    have hnx : (n : ℕ) ≤ x := (Finset.mem_Icc.mp hnmem).2
    have hnpos : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    have hpow : (((n : ℕ) : ℝ) ^ δ) ≤ (x : ℝ) ^ δ :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnx) hδ.le
    calc
      (1 : ℝ) = (((n : ℕ) : ℝ) ^ δ) * (((n : ℕ) : ℝ) ^ (-δ)) := by
        rw [← Real.rpow_add hnpos]
        norm_num
      _ ≤ (x : ℝ) ^ δ * (((n : ℕ) : ℝ) ^ (-δ)) := by
        exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by positivity) _)
  have hcard : (smoothCount x y : ℝ) =
      ∑ n : {n // n ∈ smoothFinset x y}, (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_coe]
    rfl
  rw [hcard]
  calc
    (∑ n : {n // n ∈ smoothFinset x y}, (1 : ℝ)) ≤
        ∑ n : {n // n ∈ smoothFinset x y},
          (x : ℝ) ^ δ * (((n : ℕ) : ℝ) ^ (-δ)) := by
      exact Finset.sum_le_sum fun n _ => hpoint n
    _ = (x : ℝ) ^ δ * ∑ n : {n // n ∈ smoothFinset x y},
          (((n : ℕ) : ℝ) ^ (-δ)) := by rw [Finset.mul_sum]
    _ ≤ (x : ℝ) ^ δ * ∑' m, g m := by
      exact mul_le_mul_of_nonneg_left hsum_le (Real.rpow_nonneg (by positivity) _)
    _ = (x : ℝ) ^ δ *
        ∏ p ∈ Finset.range (y + 1) with p.Prime,
          (1 - MAPMertensAnalyticLeaf.realRpowSummandHom δ hδ.ne' p)⁻¹ := by
      rw [show (∑' m, g m) =
          ∏ p ∈ Finset.range (y + 1) with p.Prime,
            (1 - MAPMertensAnalyticLeaf.realRpowSummandHom δ hδ.ne' p)⁻¹ by
        exact hEuler.2.tsum_eq]

/-- Rankin's inequality after eliminating the finite Euler product.  The only
remaining input for Shiu's displayed Lemma 1 is an upper bound for
`primeInvLogSum`. -/
theorem smoothCount_le_rankinExponential
    {δ : ℝ} (hδ : 0 < δ) {x : ℕ} (hx : 0 < x) (y : ℕ) :
    (smoothCount x y : ℝ) ≤
      Real.exp
        (δ * Real.log (x : ℝ) + δ⁻¹ * primeInvLogSum y) := by
  have hxreal : (0 : ℝ) < x := by exact_mod_cast hx
  calc
    (smoothCount x y : ℝ) ≤
        (x : ℝ) ^ δ *
          ∏ p ∈ Finset.range (y + 1) with p.Prime,
            (1 - MAPMertensAnalyticLeaf.realRpowSummandHom δ hδ.ne' p)⁻¹ :=
      smoothCount_le_rankinEulerProduct hδ x y
    _ ≤ (x : ℝ) ^ δ * Real.exp (δ⁻¹ * primeInvLogSum y) := by
      exact mul_le_mul_of_nonneg_left
        (finiteEulerProduct_le_exp_primeInvLogSum hδ y)
        (Real.rpow_nonneg (Nat.cast_nonneg x) δ)
    _ = Real.exp
        (δ * Real.log (x : ℝ) + δ⁻¹ * primeInvLogSum y) := by
      rw [Real.rpow_def_of_pos hxreal, Real.exp_add]
      congr 2
      ring

/-! ## A Chebyshev-level substitute for Shiu's PNT input -/

/-- An explicit weighted-prime bound obtained from Mathlib's Chebyshev
inequality `θ(t) ≤ log 4 * t`.  Splitting at `sqrt y` supplies the two powers
of `log y` that Shiu obtains from the prime number theorem.  The first term is
lower order and the constant in the second term is deliberately unoptimized.
-/
theorem primeInvLogSum_le_sqrt_add_chebyshev
    {y : ℕ} (hy : 2 ≤ y) :
    primeInvLogSum y ≤
      ((Nat.sqrt y + 1 : ℕ) : ℝ) * (Real.log 2)⁻¹ +
        (4 * Real.log 4 * (y : ℝ)) / (Real.log (y : ℝ)) ^ 2 := by
  classical
  let P : Finset ℕ := (Finset.range (y + 1)).filter Nat.Prime
  let small : Finset ℕ := P.filter fun p => p ≤ Nat.sqrt y
  let large : Finset ℕ := P.filter fun p => ¬p ≤ Nat.sqrt y
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hyreal : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hyreal
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (lt_of_lt_of_le (by norm_num) hyreal)
  have hsmall_subset : small ⊆ Finset.range (Nat.sqrt y + 1) := by
    intro p hp
    have hpsmall : p ≤ Nat.sqrt y := (Finset.mem_filter.mp hp).2
    exact Finset.mem_range.mpr (by omega)
  have hsmall_card : small.card ≤ Nat.sqrt y + 1 := by
    simpa using Finset.card_le_card hsmall_subset
  have hsmall_term :
      (∑ p ∈ small, (Real.log (p : ℝ))⁻¹) ≤
        ((Nat.sqrt y + 1 : ℕ) : ℝ) * (Real.log 2)⁻¹ := by
    calc
      (∑ p ∈ small, (Real.log (p : ℝ))⁻¹) ≤
          small.card • (Real.log 2)⁻¹ := by
        apply Finset.sum_le_card_nsmul
        intro p hp
        have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
        have hpprime : p.Prime := (Finset.mem_filter.mp hpP).2
        have hpone : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
        have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpone
        have hlogle : Real.log 2 ≤ Real.log (p : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hpprime.two_le)
        exact (inv_le_inv₀ hlogp hlog2).2 hlogle
      _ = (small.card : ℝ) * (Real.log 2)⁻¹ := by rw [nsmul_eq_mul]
      _ ≤ ((Nat.sqrt y + 1 : ℕ) : ℝ) * (Real.log 2)⁻¹ := by
        gcongr
  have hlarge_pointwise (p : ℕ) (hp : p ∈ large) :
      (Real.log (p : ℝ))⁻¹ ≤
        4 * Real.log (p : ℝ) / (Real.log (y : ℝ)) ^ 2 := by
    have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
    have hpprime : p.Prime := (Finset.mem_filter.mp hpP).2
    have hpone : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpone
    have hnot : ¬p ≤ Nat.sqrt y := (Finset.mem_filter.mp hp).2
    have hsq : y < p * p := (Nat.sqrt_lt).mp (by omega)
    have hsqreal : (y : ℝ) < (p : ℝ) ^ 2 := by
      exact_mod_cast (show y < p ^ 2 by simpa [pow_two] using hsq)
    have hloglt : Real.log (y : ℝ) < 2 * Real.log (p : ℝ) := by
      have h := Real.log_lt_log hypos hsqreal
      rw [Real.log_pow] at h
      norm_num at h ⊢
      exact h
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hlogp (sq_pos_of_pos hlogy)).2
    nlinarith [sq_nonneg (2 * Real.log (p : ℝ) - Real.log (y : ℝ))]
  have hlarge_sum :
      (∑ p ∈ large, (Real.log (p : ℝ))⁻¹) ≤
        (4 * Real.log 4 * (y : ℝ)) / (Real.log (y : ℝ)) ^ 2 := by
    calc
      (∑ p ∈ large, (Real.log (p : ℝ))⁻¹) ≤
          ∑ p ∈ large,
            4 * Real.log (p : ℝ) / (Real.log (y : ℝ)) ^ 2 := by
        exact Finset.sum_le_sum fun p hp => hlarge_pointwise p hp
      _ = (4 / (Real.log (y : ℝ)) ^ 2) *
          ∑ p ∈ large, Real.log (p : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ ≤ (4 / (Real.log (y : ℝ)) ^ 2) * Chebyshev.theta (y : ℝ) := by
        gcongr
        have hsubset : large ⊆ P := Finset.filter_subset _ _
        calc
          (∑ p ∈ large, Real.log (p : ℝ)) ≤
              ∑ p ∈ P, Real.log (p : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
            intro p hpP hpnot
            have hpprime : p.Prime := (Finset.mem_filter.mp hpP).2
            exact Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le)
          _ = Chebyshev.theta (y : ℝ) := by
            rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast,
              ← Nat.range_succ_eq_Icc_zero]
      _ ≤ (4 / (Real.log (y : ℝ)) ^ 2) * (Real.log 4 * (y : ℝ)) := by
        gcongr
        exact Chebyshev.theta_le_log4_mul_x hypos.le
      _ = (4 * Real.log 4 * (y : ℝ)) / (Real.log (y : ℝ)) ^ 2 := by ring
  have hpartition :
      (∑ p ∈ small, (Real.log (p : ℝ))⁻¹) +
          ∑ p ∈ large, (Real.log (p : ℝ))⁻¹ =
        ∑ p ∈ P, (Real.log (p : ℝ))⁻¹ := by
    simpa [small, large] using
      (Finset.sum_filter_add_sum_filter_not P (fun p => p ≤ Nat.sqrt y)
        (fun p => (Real.log (p : ℝ))⁻¹))
  rw [primeInvLogSum, show (Finset.range (y + 1)).filter Nat.Prime = P by rfl,
    ← hpartition]
  exact add_le_add hsmall_term hlarge_sum

/-- The explicit right side of the preceding theorem. -/
def chebyshevPrimeBudget (y : ℕ) : ℝ :=
  ((Nat.sqrt y + 1 : ℕ) : ℝ) * (Real.log 2)⁻¹ +
    (4 * Real.log 4 * (y : ℝ)) / (Real.log (y : ℝ)) ^ 2

/-- A completely explicit, PNT-free Rankin estimate. -/
theorem smoothCount_le_rankinChebyshev
    {δ : ℝ} (hδ : 0 < δ) {x : ℕ} (hx : 0 < x)
    {y : ℕ} (hy : 2 ≤ y) :
    (smoothCount x y : ℝ) ≤
      Real.exp
        (δ * Real.log (x : ℝ) + δ⁻¹ * chebyshevPrimeBudget y) := by
  calc
    (smoothCount x y : ℝ) ≤
        Real.exp
          (δ * Real.log (x : ℝ) + δ⁻¹ * primeInvLogSum y) :=
      smoothCount_le_rankinExponential hδ hx y
    _ ≤ Real.exp
        (δ * Real.log (x : ℝ) + δ⁻¹ * chebyshevPrimeBudget y) := by
      apply Real.exp_le_exp.mpr
      gcongr
      exact primeInvLogSum_le_sqrt_add_chebyshev hy

/-- A finite/natural conclusion tailored to the exponent used in Shiu's
class-III estimate.  Once the displayed real budget inequality is checked,
the fourth power of the smooth count is at most the ambient endpoint.  No
asymptotic or number-theoretic hypothesis is concealed in this statement. -/
theorem smoothCount_pow_four_le_of_chebyshevBudget
    {δ : ℝ} (hδ : 0 < δ) {x : ℕ} (hx : 0 < x)
    {y : ℕ} (hy : 2 ≤ y)
    (hbudget :
      4 * (δ * Real.log (x : ℝ) + δ⁻¹ * chebyshevPrimeBudget y) ≤
        Real.log (x : ℝ)) :
    smoothCount x y ^ 4 ≤ x := by
  have hxreal : (0 : ℝ) < x := by exact_mod_cast hx
  have hcount := smoothCount_le_rankinChebyshev hδ hx hy
  have hreal : ((smoothCount x y : ℝ) ^ 4) ≤ (x : ℝ) := by
    calc
      (smoothCount x y : ℝ) ^ 4 ≤
          (Real.exp
            (δ * Real.log (x : ℝ) + δ⁻¹ * chebyshevPrimeBudget y)) ^ 4 := by
        gcongr
      _ = Real.exp
          (4 * (δ * Real.log (x : ℝ) + δ⁻¹ * chebyshevPrimeBudget y)) := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ ≤ Real.exp (Real.log (x : ℝ)) := Real.exp_le_exp.mpr hbudget
      _ = (x : ℝ) := Real.exp_log hxreal
  exact_mod_cast hreal

end

end ShiuLemma1Rankin
