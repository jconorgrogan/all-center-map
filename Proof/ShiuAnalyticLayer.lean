import ShiuFoundation
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Kernel-checked analytic hypotheses for the divisor-square weight

This file proves elementary growth facts which are genuine hypotheses in
Shiu's theorem.  It does not postulate or claim the progression estimate or
Mertens' theorem.
-/

namespace ShiuAnalyticLayer

open ArithmeticFunction MixedMellinCert ShiuFoundation
open scoped ArithmeticFunction.zeta BigOperators

noncomputable section

/-- A polynomial bound in the prime-power exponent. -/
theorem multichoose_le_add_pow (k e : ℕ) (hk : 1 ≤ k) :
    k.multichoose e ≤ (e + k) ^ k := by
  rw [Nat.multichoose_eq]
  have htop : k + e - 1 = e + (k - 1) := by omega
  rw [htop, Nat.choose_symm_add]
  refine (Nat.choose_le_pow _ _).trans ?_
  calc
    (e + (k - 1)) ^ (k - 1) ≤ (e + k) ^ (k - 1) :=
      Nat.pow_le_pow_left (by omega) _
    _ ≤ (e + k) ^ k := Nat.pow_le_pow_right (by omega) (by omega)

/-- A fully explicit form of polynomial-versus-exponential domination. -/
theorem add_pow_le_exp (k m e : ℕ) (hk : 1 ≤ k) :
    (e + k) ^ m ≤
      (k ^ m * m.factorial * 2 ^ m) * 2 ^ e := by
  calc
    (e + k) ^ m ≤ (k * (e + 1)) ^ m :=
      Nat.pow_le_pow_left (by nlinarith) _
    _ = k ^ m * (e + 1) ^ m := by rw [mul_pow]
    _ ≤ k ^ m * (e + 1).ascFactorial m := by
      gcongr
      exact Nat.pow_succ_le_ascFactorial (e + 1) m
    _ = k ^ m * (m.factorial * (e + m).choose m) := by
      rw [Nat.ascFactorial_eq_factorial_mul_choose]
    _ ≤ k ^ m * (m.factorial * 2 ^ (e + m)) := by
      gcongr
      exact Nat.choose_le_two_pow _ _
    _ = (k ^ m * m.factorial * 2 ^ m) * 2 ^ e := by
      rw [pow_add]
      ring

/-- Uniform local domination by `2^e`; unlike the earlier `k^(2e)` bound,
the constant here is independent of the exponent. -/
theorem multichoose_square_pow_le_const_mul_two_pow
    (k d e : ℕ) (hk : 1 ≤ k) :
    (k.multichoose e ^ 2) ^ d ≤
      (k ^ (2 * k * d) * (2 * k * d).factorial * 2 ^ (2 * k * d)) * 2 ^ e := by
  calc
    (k.multichoose e ^ 2) ^ d = k.multichoose e ^ (2 * d) := by
      rw [← pow_mul]
    _ ≤ ((e + k) ^ k) ^ (2 * d) :=
      Nat.pow_le_pow_left (multichoose_le_add_pow k e hk) _
    _ = (e + k) ^ (2 * k * d) := by
      rw [← pow_mul]
      congr 1
      ring
    _ ≤ (k ^ (2 * k * d) * (2 * k * d).factorial * 2 ^ (2 * k * d)) * 2 ^ e :=
      add_pow_le_exp k (2 * k * d) e hk

/-- Termwise ascending-factorial inequality underlying the content envelope
`tau_k(n)^2 ≤ tau_{k^2}(n)`. -/
theorem ascFactorial_sq_le_factorial_mul_ascFactorial (k e : ℕ) :
    k.ascFactorial e ^ 2 ≤ e.factorial * (k * k).ascFactorial e := by
  rw [Nat.ascFactorial_eq_prod_range, Nat.factorial_eq_prod_range_add_one,
    Nat.ascFactorial_eq_prod_range, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro j hj
  cases k with
  | zero => simp; nlinarith
  | succ k => nlinarith [sq_nonneg k]

/-- Prime-local square domination with the exact order `k^2`. -/
theorem multichoose_sq_le_multichoose_mul (k e : ℕ) :
    k.multichoose e ^ 2 ≤ (k * k).multichoose e := by
  have h := ascFactorial_sq_le_factorial_mul_ascFactorial k e
  rw [Nat.ascFactorial_eq_factorial_mul_choose',
    Nat.ascFactorial_eq_factorial_mul_choose'] at h
  simp only [← Nat.multichoose_eq] at h
  have hfac : 0 < e.factorial ^ 2 := by positivity
  apply (Nat.mul_le_mul_left_iff hfac).mp
  calc
    e.factorial ^ 2 * k.multichoose e ^ 2 =
        (e.factorial * k.multichoose e) ^ 2 := by ring
    _ ≤ e.factorial * (e.factorial * (k * k).multichoose e) := h
    _ = e.factorial ^ 2 * (k * k).multichoose e := by ring

/-- Global content envelope obtained by multiplying the prime-local square
domination over the exact factorization of `n`. -/
theorem tauAF_square_le_tauAF_mul (k n : ℕ) :
    tauAF k n ^ 2 ≤ tauAF (k * k) n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [tauAF_eq_factorization_prod k n hn,
    tauAF_eq_factorization_prod (k * k) n hn]
  change (∏ p ∈ n.factorization.support,
    k.multichoose (n.factorization p)) ^ 2 ≤
      ∏ p ∈ n.factorization.support,
        (k * k).multichoose (n.factorization p)
  rw [← Finset.prod_pow]
  exact Finset.prod_le_prod' fun p hp ↦
    multichoose_sq_le_multichoose_mul k (n.factorization p)

/-- Monotonicity of multichoose in its number of symbols. -/
theorem multichoose_mono_left {r s : ℕ} (hrs : r ≤ s) (e : ℕ) :
    r.multichoose e ≤ s.multichoose e := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrs
  induction t with
  | zero => simp
  | succ t iht =>
      exact (iht (by omega)).trans
        (by simpa [Nat.add_assoc] using multichoose_le_succ (r + t) e)

/-- Increasing the divisor order increases the divisor function pointwise. -/
theorem tauAF_mono_order {r s : ℕ} (hrs : r ≤ s) (n : ℕ) :
    tauAF r n ≤ tauAF s n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [tauAF_eq_factorization_prod r n hn, tauAF_eq_factorization_prod s n hn]
  exact Finset.prod_le_prod' fun p hp ↦
    multichoose_mono_left hrs (n.factorization p)

/-- The exact content majorant used in the paper's convention
`R = max 2 (k^2)`. -/
theorem tauAF_square_le_tauAF_max (k n : ℕ) :
    tauAF k n ^ 2 ≤ tauAF (max 2 (k * k)) n :=
  (tauAF_square_le_tauAF_mul k n).trans
    (tauAF_mono_order (Nat.le_max_right 2 (k * k)) n)

/-- Exact value of the square weight at a prime.  This is the coefficient
`k^2` in the prime-reciprocal sum appearing in Shiu's exponential factor. -/
theorem tauAF_square_at_prime (k p : ℕ) (hp : p.Prime) :
    tauAF k p ^ 2 = k ^ 2 := by
  simpa using tauAF_prime_pow_eq_multichoose k 1 p hp

/-- Prime-local domination for the `d`-th power of the square weight.  Above
the explicit cutoff `(k*k)^d`, the multiplicative constant is exactly one. -/
theorem tauAF_square_prime_pow_pow_le
    (k d p e : ℕ) (hp : p.Prime) (hlarge : (k * k) ^ d ≤ p) :
    (tauAF k (p ^ e) ^ 2) ^ d ≤ p ^ e := by
  calc
    (tauAF k (p ^ e) ^ 2) ^ d ≤ (((k * k) ^ e) ^ d) :=
      Nat.pow_le_pow_left (tauAF_square_prime_pow_le k e p hp) _
    _ = ((k * k) ^ d) ^ e := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    _ ≤ p ^ e := Nat.pow_le_pow_left hlarge _

/-- At most `T` members of a finite set can lie below `T`; consequently a
constant paid only at those members contributes at most its `T`-th power. -/
theorem prod_if_lt_le_pow (s : Finset ℕ) (A T : ℕ) (hA : 0 < A) :
    (∏ p ∈ s, if p < T then A else 1) ≤ A ^ T := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one]
  apply Nat.pow_le_pow_right hA
  have hsubset : {p ∈ s | p < T} ⊆ Finset.range T := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    simpa using hp.2
  simpa using Finset.card_le_card hsubset

/-- Rational-moment form of fixed-`k` subpower growth.  For every positive
denominator `d`, the `d`-th power of `tau_k(n)^2` is bounded by a constant
times `n`.  This is the integer statement behind the condition
`tau_k(n)^2 ≪_{k,ε} n^ε`. -/
theorem tauAF_square_subpower_moment (k d : ℕ) (hk : 1 ≤ k) (_hd : 1 ≤ d) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → (tauAF k n ^ 2) ^ d ≤ C * n := by
  classical
  let m : ℕ := 2 * k * d
  let A : ℕ := k ^ m * m.factorial * 2 ^ m
  let T : ℕ := (k * k) ^ d
  refine ⟨A ^ T, pow_pos ?_ _, ?_⟩
  · dsimp [A]
    positivity
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  rw [tauAF_eq_factorization_prod k n hn0]
  change ((∏ p ∈ n.factorization.support,
    k.multichoose (n.factorization p)) ^ 2) ^ d ≤ A ^ T * n
  rw [← pow_mul, ← Finset.prod_pow]
  calc
    (∏ p ∈ n.factorization.support,
        k.multichoose (n.factorization p) ^ (2 * d)) =
        ∏ p ∈ n.factorization.support,
          (k.multichoose (n.factorization p) ^ 2) ^ d := by
            apply Finset.prod_congr rfl
            intro p hp
            rw [← pow_mul]
    _ ≤ ∏ p ∈ n.factorization.support,
          (if p < T then A else 1) * p ^ n.factorization p := by
      apply Finset.prod_le_prod'
      intro p hp
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (by
        simpa [Nat.support_factorization] using hp)
      split_ifs with hsmall
      · calc
          (k.multichoose (n.factorization p) ^ 2) ^ d ≤
              A * 2 ^ n.factorization p := by
                simpa [A, m] using
                  multichoose_square_pow_le_const_mul_two_pow
                    k d (n.factorization p) hk
          _ ≤ A * p ^ n.factorization p := by
                exact Nat.mul_le_mul_left A
                  (Nat.pow_le_pow_left hpprime.two_le _)
      · rw [← tauAF_prime_pow_eq_multichoose k (n.factorization p) p hpprime]
        simpa only [one_mul] using
          tauAF_square_prime_pow_pow_le k d p (n.factorization p) hpprime
            (by simpa [T] using Nat.le_of_not_gt hsmall)
    _ = (∏ p ∈ n.factorization.support, if p < T then A else 1) *
          (∏ p ∈ n.factorization.support, p ^ n.factorization p) := by
      rw [Finset.prod_mul_distrib]
    _ ≤ A ^ T * (∏ p ∈ n.factorization.support, p ^ n.factorization p) := by
      gcongr
      exact prod_if_lt_le_pow n.factorization.support A T (by
        dsimp [A]
        positivity)
    _ = A ^ T * n := by
      rw [← Finsupp.prod]
      exact congrArg (A ^ T * ·) (Nat.prod_factorization_pow_eq_self hn0)

/-- The usual real-exponent form of Shiu's subpower hypothesis for the
literal square weight.  Its proof is reduced to the preceding integer moment
bound, so no analytic number-theory estimate is hidden here. -/
theorem tauAF_square_subpolynomial (k : ℕ) (hk : 1 ≤ k) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
        (tauAF k n ^ 2 : ℝ) ≤ C * (n : ℝ) ^ ε := by
  intro ε hε
  obtain ⟨q, hq⟩ := exists_nat_one_div_lt hε
  let d : ℕ := q + 1
  have hd : 1 ≤ d := by simp [d]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  have hinv : ((d : ℝ)⁻¹) ≤ ε := by
    have : (1 : ℝ) / (d : ℝ) < ε := by
      simpa [d, Nat.cast_add] using hq
    simpa [one_div] using this.le
  obtain ⟨C₀, hC₀, hbound⟩ := tauAF_square_subpower_moment k d hk hd
  let C : ℝ := (C₀ : ℝ) ^ ((d : ℝ)⁻¹)
  have hC : 0 < C := Real.rpow_pos_of_pos (by exact_mod_cast hC₀) _
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hnat := hbound n hn
  have hroot : (tauAF k n ^ 2 : ℝ) ≤
      ((C₀ : ℝ) * (n : ℝ)) ^ ((d : ℝ)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) hdpos).2
    rw [Real.rpow_natCast]
    exact_mod_cast hnat
  calc
    (tauAF k n ^ 2 : ℝ) ≤ ((C₀ : ℝ) * (n : ℝ)) ^ ((d : ℝ)⁻¹) := hroot
    _ = C * (n : ℝ) ^ ((d : ℝ)⁻¹) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ C * (n : ℝ) ^ ε := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact Real.rpow_le_rpow_of_exponent_le (by
        exact_mod_cast (show 1 ≤ n by omega)) hinv

/-! ## Exact Shiu weight hypotheses -/

/-- The three weight-side hypotheses used by Shiu's theorem, stated for a
natural-valued arithmetic function.  Nonnegativity needs no separate field
because it follows from the codomain.  This definition contains no
progression estimate. -/
def ShiuNatWeightHypotheses (f : ArithmeticFunction ℕ) (A : ℕ) : Prop :=
  f.IsMultiplicative ∧
  (∀ p e : ℕ, p.Prime → f (p ^ e) ≤ A ^ e) ∧
  (∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (f n : ℝ) ≤ C * (n : ℝ) ^ ε)

/-- The literal weight in `DyadicTauSquareShiuTarget` satisfies every
weight-side hypothesis of Shiu, with the exact prime-power parameter `k^2`.
The remaining work is the analytic progression theorem, not verification of
its growth assumptions. -/
theorem tauAF_square_shiuWeightHypotheses (k : ℕ) (hk : 1 ≤ k) :
    ShiuNatWeightHypotheses ((tauAF k).pmul (tauAF k)) (k * k) := by
  refine ⟨tauAF_square_isMultiplicative k, ?_, ?_⟩
  · intro p e hp
    simpa [ArithmeticFunction.pmul_apply, pow_two] using
      tauAF_square_prime_pow_le k e p hp
  · intro ε hε
    simpa [ArithmeticFunction.pmul_apply, pow_two] using
      tauAF_square_subpolynomial k hk ε hε

/-! ## Coefficient-one prime-reciprocal interface -/

/-- The finite sum of prime reciprocals up to `x`, with coefficient exactly
one.  A Mertens upper bound for this quantity remains to be proved. -/
def primeReciprocalSum (x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (p : ℝ)⁻¹

/-- The prime sum occurring for the divisor-square weight. -/
def tauAFSquarePrimeReciprocalSum (k x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime,
    (tauAF k p ^ 2 : ℝ) * (p : ℝ)⁻¹

/-- Exact extraction of the coefficient `k^2` from the prime sum. -/
theorem tauAFSquarePrimeReciprocalSum_eq (k x : ℕ) :
    tauAFSquarePrimeReciprocalSum k x =
      (k ^ 2 : ℕ) * primeReciprocalSum x := by
  classical
  unfold tauAFSquarePrimeReciprocalSum primeReciprocalSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpprime : p.Prime := by simpa using (Finset.mem_filter.mp hp).2
  rw [← Nat.cast_pow, tauAF_square_at_prime k p hpprime]

/-- Any coefficient-one upper bound transfers to the divisor-square prime
sum without worsening its leading coefficient. -/
theorem tauAFSquarePrimeReciprocalSum_le
    (k x : ℕ) {L : ℝ} (hL : primeReciprocalSum x ≤ L) :
    tauAFSquarePrimeReciprocalSum k x ≤ (k ^ 2 : ℕ) * L := by
  rw [tauAFSquarePrimeReciprocalSum_eq]
  exact mul_le_mul_of_nonneg_left hL (by positivity)

/-- Pointwise interface from a coefficient-one Mertens bound to the exact
Euler exponential needed for `tau_k^2`.  The Mertens inequality is an explicit
argument at `x`; this theorem does not assert it. -/
theorem exp_tauAFSquarePrimeReciprocalSum_le_of_mertensAt
    (k x : ℕ) {B : ℝ} (hx : 1 < x)
    (hM : primeReciprocalSum x ≤
      Real.log (Real.log (x : ℝ)) + B) :
    Real.exp (tauAFSquarePrimeReciprocalSum k x) ≤
      Real.exp ((k ^ 2 : ℕ) * B) * (Real.log (x : ℝ)) ^ (k ^ 2) := by
  rw [tauAFSquarePrimeReciprocalSum_eq]
  calc
    Real.exp ((k ^ 2 : ℕ) * primeReciprocalSum x) ≤
        Real.exp ((k ^ 2 : ℕ) *
          (Real.log (Real.log (x : ℝ)) + B)) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hM (by positivity))
    _ = Real.exp ((k ^ 2 : ℕ) * B) *
          (Real.log (x : ℝ)) ^ (k ^ 2) := by
      rw [mul_add, Real.exp_add, Real.exp_nat_mul,
        Real.exp_log (Real.log_pos (by exact_mod_cast hx))]
      ring

end

end ShiuAnalyticLayer
