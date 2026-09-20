import KhaleAppendixBZetaPrimePowerCertified
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Absolute prime-power expansion of `log |L(s,chi)|`

This is the Euler-product component of Khale Lemma 5.1, separated from the
later Fubini and Fourier-kernel steps.
-/

namespace MAPKhaleAppendixBLFunctionEulerCertified

open MAPKhaleAppendixBLemma51ExpansionReduction

noncomputable section

/-- The complex prime-power term in `log L(s,chi)`, with positive exponent
represented by `k.2+1`. -/
def appendixBLPrimePowerTerm {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (s : ℂ)
    (k : PrimePowerIndex) : ℂ :=
  (chi k.1 * (k.1 : ℂ) ^ (-s)) ^ ppExponent k / (ppExponent k : ℕ)

theorem primePowerTerm_norm_le_zetaTerm
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) (k : PrimePowerIndex) :
    ‖appendixBLPrimePowerTerm chi s k‖ ≤
      appendixBZetaPrimePowerTerm (s.re - 1) k := by
  have hmNat : 0 < ppExponent k := by simp [ppExponent]
  have hm : (0 : ℝ) < (ppExponent k : ℝ) := by exact_mod_cast hmNat
  have hsne : (-s).re ≠ 0 := by simp; linarith
  have hchi : ‖chi k.1‖ ≤ 1 := chi.norm_le_one k.1
  have hpowchi : ‖chi k.1‖ ^ ppExponent k ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) hchi
  have hp0 : (0 : ℝ) ≤ (k.1 : ℝ) := by positivity
  have hpNorm : ‖(k.1 : ℂ) ^ (-s)‖ =
      Real.rpow (k.1 : ℝ) (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_re_ne_zero k.1 hsne]
    simp
  have hpPow0 : 0 ≤ Real.rpow (k.1 : ℝ) (-s.re) ^ ppExponent k :=
    pow_nonneg (Real.rpow_nonneg hp0 _) _
  have hmul :
      (‖chi k.1‖ * Real.rpow (k.1 : ℝ) (-s.re)) ^ ppExponent k ≤
        Real.rpow (k.1 : ℝ) (-s.re) ^ ppExponent k := by
    rw [mul_pow]
    nlinarith
  have hrpow := Real.rpow_mul_natCast hp0 (-s.re) (ppExponent k)
  unfold appendixBLPrimePowerTerm appendixBZetaPrimePowerTerm
  rw [norm_div, norm_pow, norm_mul, hpNorm]
  have hden : ‖((ppExponent k : ℕ) : ℂ)‖ = (ppExponent k : ℝ) := by
    simp [abs_of_pos hm]
  rw [hden]
  apply (div_le_div_iff_of_pos_right hm).2
  calc
    (‖chi k.1‖ * Real.rpow (k.1 : ℝ) (-s.re)) ^ ppExponent k ≤
        Real.rpow (k.1 : ℝ) (-s.re) ^ ppExponent k := hmul
    _ = Real.rpow (k.1 : ℝ) (-s.re * (ppExponent k : ℝ)) := hrpow.symm
    _ = Real.rpow (k.1 : ℝ)
        (-((ppExponent k : ℝ) * (1 + (s.re - 1)))) := by
      congr 1
      ring

/-- Absolute convergence of the prime-power logarithm expansion. -/
theorem appendixBLPrimePowerTerm_summable
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (appendixBLPrimePowerTerm chi s) := by
  have heta : 0 < s.re - 1 := by linarith
  have hz := MAPKhaleAppendixBZetaPrimePowerCertified.appendixBZetaPrimePowerIdentity
    (s.re - 1) heta
  exact hz.1.of_norm_bounded (primePowerTerm_norm_le_zetaTerm chi hs)

private theorem primeLogFactor_summable
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes =>
      -Complex.log (1 - chi p * (p : ℂ) ^ (-s))) :=
  chi.summable_neg_log_one_sub_mul_prime_cpow hs

private theorem inner_primePower_hasSum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    HasSum (fun n : ℕ => appendixBLPrimePowerTerm chi s (p, n))
      (-Complex.log (1 - chi p * (p : ℂ) ^ (-s))) := by
  let z : ℂ := chi p * (p : ℂ) ^ (-s)
  have hsne : (-s).re ≠ 0 := by simp; linarith
  have hpNorm : ‖(p : ℂ) ^ (-s)‖ = Real.rpow (p : ℝ) (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_re_ne_zero p hsne]
    simp
  have hpReal : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by linarith
  have hpPow : Real.rpow (p : ℝ) (-s.re) < 1 := by
    calc
      Real.rpow (p : ℝ) (-s.re) = (Real.rpow (p : ℝ) s.re)⁻¹ :=
        Real.rpow_neg hp0 s.re
      _ < 1 := by
        have hgt := Real.one_lt_rpow hpReal (by linarith : 0 < s.re)
        exact (inv_lt_one₀ (zero_lt_one.trans hgt)).2 hgt
  have hzNorm : ‖z‖ < 1 := by
    dsimp [z]
    rw [norm_mul, hpNorm]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hp0 _) (chi.norm_le_one p)).trans_lt hpPow
  have ht := Complex.hasSum_taylorSeries_neg_log hzNorm
  have hrs := ht.summable
  have hshift := hrs.tsum_eq_zero_add
  have htail : (∑' n : ℕ, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) =
      -Complex.log (1 - z) := by
    rw [ht.tsum_eq] at hshift
    simpa using hshift.symm
  have hsTail : Summable
      (fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 hrs
  have hterm (n : ℕ) :
      appendixBLPrimePowerTerm chi s (p, n) =
        z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) := by
    unfold appendixBLPrimePowerTerm ppExponent
    simp only [Prod.fst, Prod.snd, z]
  have hsPP : Summable (fun n : ℕ => appendixBLPrimePowerTerm chi s (p, n)) :=
    hsTail.congr (fun n => (hterm n).symm)
  have hsum : (∑' n : ℕ, appendixBLPrimePowerTerm chi s (p, n)) =
      -Complex.log (1 - chi p * (p : ℂ) ^ (-s)) := by
    calc
      _ = ∑' n : ℕ, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) := tsum_congr hterm
      _ = -Complex.log (1-z) := htail
      _ = _ := by rfl
  rw [← hsum]
  exact hsPP.hasSum

/-- Exact absolutely convergent prime-power expansion of `log |L(s,chi)|`
for `Re(s)>1`. -/
theorem log_norm_LFunction_eq_tsum_primePowers
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    Real.log ‖DirichletCharacter.LFunction chi s‖ =
      (∑' k : PrimePowerIndex, appendixBLPrimePowerTerm chi s k).re := by
  have hPrime := primeLogFactor_summable chi hs
  have hFlat := appendixBLPrimePowerTerm_summable chi hs
  have hseries :
      (∑' k : PrimePowerIndex, appendixBLPrimePowerTerm chi s k) =
        ∑' p : Nat.Primes,
          -Complex.log (1 - chi p * (p : ℂ) ^ (-s)) := by
    calc
      _ = ∑' p : Nat.Primes, ∑' n : ℕ,
          appendixBLPrimePowerTerm chi s (p,n) := hFlat.tsum_prod
      _ = _ := by
        apply tsum_congr
        intro p
        exact (inner_primePower_hasSum chi hs p).tsum_eq
  have hEuler := DirichletCharacter.LSeries_eulerProduct_exp_log chi hs
  rw [← chi.LFunction_eq_LSeries hs] at hEuler
  have hExp : Complex.exp (∑' k : PrimePowerIndex,
      appendixBLPrimePowerTerm chi s k) =
      DirichletCharacter.LFunction chi s := by
    rw [hseries]
    exact hEuler
  have hnorm := congrArg norm hExp
  simp only [Complex.norm_exp] at hnorm
  rw [← hnorm, Real.log_exp]

end
end MAPKhaleAppendixBLFunctionEulerCertified

#print axioms MAPKhaleAppendixBLFunctionEulerCertified.appendixBLPrimePowerTerm_summable
#print axioms MAPKhaleAppendixBLFunctionEulerCertified.log_norm_LFunction_eq_tsum_primePowers
