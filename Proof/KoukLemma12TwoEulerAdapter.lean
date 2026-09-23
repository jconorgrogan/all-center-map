import PrincipalLogDerivativeRemainderUnconditional
import PrimitiveEulerZeroTransport

/-!
# The imprimitive Euler-factor part of Koukoulopoulos Lemma 12.2

This is the quantitative change-of-level estimate needed when the `3-4-1`
argument applies Lemma 12.2 to `chi^2`.
-/

namespace MAPKoukLemma12TwoEulerAdapter

open Complex Filter Topology
open PrimitiveEulerZeroTransport
open scoped BigOperators

noncomputable section

variable {q : ℕ} [NeZero q]

def eulerFactor (chi : DirichletCharacter ℂ q) (p : ℕ) (s : ℂ) : ℂ :=
  1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s)

theorem norm_cpow_neg_le_inv
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ)⁻¹ := by
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  change ‖((p : ℝ) : ℂ) ^ (-s)‖ ≤ (p : ℝ)⁻¹
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpPos]
  have hbase : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hexp : (-s).re ≤ (-1 : ℝ) := by simp; linarith
  calc
    (p : ℝ) ^ (-s).re ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase hexp
    _ = (p : ℝ)⁻¹ := Real.rpow_neg_one _

theorem half_le_norm_eulerFactor
    (chi : DirichletCharacter ℂ q) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1 < s.re) :
    (1 / 2 : ℝ) ≤ ‖eulerFactor chi p s‖ := by
  have hpow := norm_cpow_neg_le_inv hp hs
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2)
  have hchar := chi.primitiveCharacter.norm_le_one p
  have hprod :
      ‖chi.primitiveCharacter p * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    rw [norm_mul]
    calc
      ‖chi.primitiveCharacter p‖ * ‖(p : ℂ) ^ (-s)‖ ≤
          1 * ‖(p : ℂ) ^ (-s)‖ :=
        mul_le_mul_of_nonneg_right hchar (norm_nonneg _)
      _ ≤ 1 / 2 := by simpa using hpow.trans hinv
  unfold eulerFactor
  have hrev := norm_sub_norm_le (1 : ℂ)
    (chi.primitiveCharacter p * (p : ℂ) ^ (-s))
  rw [norm_one] at hrev
  exact le_trans (by linarith) hrev

theorem deriv_eulerFactor
    (chi : DirichletCharacter ℂ q) {p : ℕ} (hp : p.Prime) (s : ℂ) :
    deriv (eulerFactor chi p) s =
      chi.primitiveCharacter p * Complex.log (p : ℂ) * (p : ℂ) ^ (-s) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpowDiff : DifferentiableAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s := by
    apply DifferentiableAt.const_cpow differentiableAt_id.neg
    exact Or.inl hp0
  have hconst : DifferentiableAt ℂ (fun _ : ℂ => (1 : ℂ)) s :=
    differentiableAt_const _
  have hprodDiff : DifferentiableAt ℂ
      (fun z : ℂ => chi.primitiveCharacter p * (p : ℂ) ^ (-z)) s :=
    (differentiableAt_const _).mul hpowDiff
  unfold eulerFactor
  change deriv ((fun _ : ℂ => 1) -
    fun z : ℂ => chi.primitiveCharacter p * (p : ℂ) ^ (-z)) s = _
  rw [deriv_sub hconst hprodDiff, deriv_const,
    deriv_const_mul _ hpowDiff]
  rw [Complex.deriv_const_cpow (f := fun z : ℂ => -z)
    differentiableAt_id.neg (p : ℂ)]
  simp only [deriv_neg, deriv_id, neg_one_mul]
  ring

theorem norm_logDeriv_eulerFactor_le
    (chi : DirichletCharacter ℂ q) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1 < s.re) :
    ‖logDeriv (eulerFactor chi p) s‖ ≤ 2 * Real.log p := by
  have hden := half_le_norm_eulerFactor chi hp hs
  have hdenPos : 0 < ‖eulerFactor chi p s‖ := by linarith
  have hpow := norm_cpow_neg_le_inv hp hs
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hchar := chi.primitiveCharacter.norm_le_one p
  have hlog : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    have hc : (p : ℂ) = ((p : ℝ) : ℂ) := by norm_num
    rw [hc, ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ p),
      norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))]
  rw [logDeriv_apply, deriv_eulerFactor chi hp, norm_div,
    norm_mul, norm_mul, hlog]
  apply (div_le_iff₀ hdenPos).2
  have hnum :
      ‖chi.primitiveCharacter p‖ * Real.log p * ‖(p : ℂ) ^ (-s)‖ ≤
        Real.log p := by
    have hinvOne : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
      (by exact_mod_cast hp.one_lt.le)
    have hpowOne := hpow.trans hinvOne
    have hlogNonneg : 0 ≤ Real.log p :=
      Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    calc
      ‖chi.primitiveCharacter p‖ * Real.log p * ‖(p : ℂ) ^ (-s)‖ ≤
          1 * Real.log p * 1 := by gcongr
      _ = Real.log p := by ring
  nlinarith [Real.log_nonneg (by exact_mod_cast hp.one_lt.le : (1 : ℝ) ≤ p)]

theorem sum_log_primeFactors_le_log (q : ℕ) [NeZero q] :
    (∑ p ∈ q.primeFactors, Real.log p) ≤ Real.log q := by
  let P : ℕ := ∏ p ∈ q.primeFactors, p
  have hPdvd : P ∣ q := by
    simpa [P] using Nat.prod_primeFactors_dvd q
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hPleNat : P ≤ q := Nat.le_of_dvd hqpos hPdvd
  have hPpos : 0 < P := by
    dsimp [P]
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).pos
  have hPle : (P : ℝ) ≤ q := by exact_mod_cast hPleNat
  have hlogle : Real.log (P : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by exact_mod_cast hPpos) hPle
  have hlogP : Real.log (P : ℝ) =
      ∑ p ∈ q.primeFactors, Real.log p := by
    dsimp [P]
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [hlogP] at hlogle
  exact hlogle

/-- The complete change-of-level correction costs at most `2 log q` on
`Re s > 1`.  This is the exact quantitative adapter required for `chi^2` in
Koukoulopoulos Theorem 12.3. -/
theorem norm_logDeriv_eulerCorrection_le
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖logDeriv (eulerCorrection chi) s‖ ≤ 2 * Real.log q := by
  have heq : logDeriv (eulerCorrection chi) s =
      ∑ p ∈ q.primeFactors, logDeriv (eulerFactor chi p) s := by
    unfold eulerCorrection eulerFactor
    rw [logDeriv_fun_prod]
    · intro p hp
      exact PrimitiveEulerZeroTransport.eulerFactor_ne_zero chi hp (by linarith)
    · intro p hp
      apply DifferentiableAt.sub (differentiableAt_const _)
      apply DifferentiableAt.mul (differentiableAt_const _)
      apply DifferentiableAt.const_cpow differentiableAt_id.neg
      exact Or.inl (by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)
  rw [heq]
  calc
    ‖∑ p ∈ q.primeFactors, logDeriv (eulerFactor chi p) s‖ ≤
        ∑ p ∈ q.primeFactors, ‖logDeriv (eulerFactor chi p) s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ q.primeFactors, 2 * Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      exact norm_logDeriv_eulerFactor_le chi
        (Nat.prime_of_mem_primeFactors hp) hs
    _ = 2 * ∑ p ∈ q.primeFactors, Real.log p := by
      rw [Finset.mul_sum]
    _ ≤ 2 * Real.log q := by
      gcongr
      exact sum_log_primeFactors_le_log q

end

end MAPKoukLemma12TwoEulerAdapter

#print axioms MAPKoukLemma12TwoEulerAdapter.norm_logDeriv_eulerFactor_le
#print axioms MAPKoukLemma12TwoEulerAdapter.sum_log_primeFactors_le_log
#print axioms MAPKoukLemma12TwoEulerAdapter.norm_logDeriv_eulerCorrection_le
