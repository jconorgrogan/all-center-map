import KhaleAppendixBLemma51ExpansionReduction
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Prime-power Euler identity for `log zeta(1+eta)`

This certifies the zeta-side identity left visible by the Euler/Fourier
reduction of Khale Lemma 5.1.  It uses Mathlib's absolutely convergent Euler
product and the Taylor series for `-log(1-z)`.
-/

namespace MAPKhaleAppendixBZetaPrimePowerCertified

open MAPKhaleAppendixB1ZetaReduction
open MAPKhaleAppendixBLemma51ExpansionReduction

noncomputable section

private def primeLogFactor (eta : ℝ) (p : Nat.Primes) : ℂ :=
  -Complex.log (1 - (p : ℂ) ^ (-(((1 + eta : ℝ) : ℂ))))

private theorem primeLogFactor_summable {eta : ℝ} (heta : 0 < eta) :
    Summable (primeLogFactor eta) := by
  have hs : 1 < ((((1 + eta : ℝ) : ℂ))).re := by simp; linarith
  have h := DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow
    (1 : DirichletCharacter ℂ 1) hs
  apply h.congr
  intro p
  unfold primeLogFactor
  rw [MulChar.one_apply (isUnit_of_subsingleton _), one_mul]

private theorem primePowerTerm_as_complex_re
    (p : Nat.Primes) (x : ℝ) (n : ℕ) :
    (((p : ℂ) ^ (-((x : ℝ) : ℂ))) ^ (n + 1) /
        ((n + 1 : ℕ) : ℂ)).re =
      Real.rpow (p : ℝ) (-((n + 1 : ℝ) * x)) / (n + 1 : ℝ) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hz : (p : ℂ) ^ (-((x : ℝ) : ℂ)) =
      ((Real.rpow (p : ℝ) (-x) : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow hp0 (-x)).symm
  rw [hz, ← Complex.ofReal_pow, ← Complex.ofReal_natCast,
    ← Complex.ofReal_div]
  simp only [Complex.ofReal_re]
  have hpow := Real.rpow_mul_natCast hp0 (-x) (n + 1)
  congr 1
  · calc
      (Real.rpow (p : ℝ) (-x)) ^ (n + 1) =
          Real.rpow (p : ℝ) (-x * (n + 1 : ℝ)) := by
            simpa only [Nat.cast_add, Nat.cast_one] using! hpow.symm
      _ = Real.rpow (p : ℝ) (-((n + 1 : ℝ) * x)) := by
        congr 1 <;> ring
  · norm_num

private theorem primePower_inner_hasSum
    {eta : ℝ} (heta : 0 < eta) (p : Nat.Primes) :
    HasSum (fun n : ℕ => appendixBZetaPrimePowerTerm eta (p, n))
      (primeLogFactor eta p).re := by
  let x : ℝ := 1 + eta
  let z : ℂ := (p : ℂ) ^ (-((x : ℝ) : ℂ))
  have hx : 1 < x := by dsimp [x]; linarith
  have hpReal : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by linarith
  have hpPow : Real.rpow (p : ℝ) (-x) < 1 := by
    calc
      Real.rpow (p : ℝ) (-x) = (Real.rpow (p : ℝ) x)⁻¹ :=
        Real.rpow_neg hp0 x
      _ < 1 := by
        have hgt := Real.one_lt_rpow hpReal (by linarith : 0 < x)
        exact (inv_lt_one₀ (zero_lt_one.trans hgt)).2 hgt
  have hzEq : z = ((Real.rpow (p : ℝ) (-x) : ℝ) : ℂ) := by
    dsimp [z]
    simpa using (Complex.ofReal_cpow hp0 (-x)).symm
  have hzNorm : ‖z‖ < 1 := by
    rw [hzEq, Complex.norm_real]
    simpa [abs_of_nonneg (Real.rpow_nonneg hp0 _)]
  have ht := Complex.hasSum_taylorSeries_neg_log hzNorm
  have hr := Complex.hasSum_re ht
  have hrs := hr.summable
  have hshift := hrs.tsum_eq_zero_add
  have htail :
      (∑' n : ℕ, (z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)).re) =
        (-Complex.log (1 - z)).re := by
    rw [hr.tsum_eq] at hshift
    simpa using hshift.symm
  have hsTail : Summable
      (fun n : ℕ => (z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)).re) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 hrs
  have hterm (n : ℕ) :
      appendixBZetaPrimePowerTerm eta (p, n) =
        (z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)).re := by
    have hzTerm := primePowerTerm_as_complex_re p x n
    simpa only [appendixBZetaPrimePowerTerm, ppExponent, Prod.snd, x,
      Nat.cast_add, Nat.cast_one, z] using hzTerm.symm
  have hsPrimePower : Summable
      (fun n : ℕ => appendixBZetaPrimePowerTerm eta (p, n)) :=
    hsTail.congr (fun n => (hterm n).symm)
  have hsum :
      (∑' n : ℕ, appendixBZetaPrimePowerTerm eta (p, n)) =
        (primeLogFactor eta p).re := by
    calc
      _ = ∑' n : ℕ, (z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)).re := by
        exact tsum_congr hterm
      _ = (-Complex.log (1 - z)).re := htail
      _ = (primeLogFactor eta p).re := by
        unfold primeLogFactor
        simp only [z, x]
  rw [← hsum]
  exact hsPrimePower.hasSum

private theorem zetaPrimePower_summable {eta : ℝ} (heta : 0 < eta) :
    Summable (appendixBZetaPrimePowerTerm eta) := by
  apply (summable_prod_of_nonneg (fun k => by
    exact zeta_prime_power_term_nonneg eta k)).2
  constructor
  · intro p
    exact (primePower_inner_hasSum heta p).summable
  · have hPrimeRe : Summable (fun p : Nat.Primes => (primeLogFactor eta p).re) :=
      (Complex.hasSum_re (primeLogFactor_summable heta).hasSum).summable
    exact hPrimeRe.congr (fun p => (primePower_inner_hasSum heta p).tsum_eq.symm)

private theorem zetaPrimePower_tsum_eq_log {eta : ℝ} (heta : 0 < eta) :
    (∑' k : PrimePowerIndex, appendixBZetaPrimePowerTerm eta k) = zetaLog eta := by
  let s : ℂ := ((1 + eta : ℝ) : ℂ)
  let S : ℂ := ∑' p : Nat.Primes, primeLogFactor eta p
  have hs : 1 < s.re := by dsimp [s]; simp; linarith
  have hPrime := primeLogFactor_summable heta
  have hFlat := zetaPrimePower_summable heta
  calc
    (∑' k : PrimePowerIndex, appendixBZetaPrimePowerTerm eta k) =
        ∑' p : Nat.Primes, ∑' n : ℕ,
          appendixBZetaPrimePowerTerm eta (p, n) := hFlat.tsum_prod
    _ = ∑' p : Nat.Primes, (primeLogFactor eta p).re := by
      apply tsum_congr
      intro p
      exact (primePower_inner_hasSum heta p).tsum_eq
    _ = S.re := by
      exact (Complex.re_tsum hPrime).symm
    _ = zetaLog eta := by
      have hEuler : Complex.exp S = riemannZeta s := by
        have h := riemannZeta_eulerProduct_exp_log (s := s) hs
        simpa only [S, s, primeLogFactor] using h
      have hnorm : Real.exp S.re = ‖riemannZeta s‖ := by
        simpa only [Complex.norm_exp] using congrArg norm hEuler
      have hzre : 0 < (riemannZeta s).re := by
        simpa only [s] using riemannZeta_re_pos_of_one_lt
          (show (1 : ℝ) < 1 + eta by linarith)
      have hzim : (riemannZeta s).im = 0 := by
        simpa only [s] using riemannZeta_im_eq_zero_of_one_lt
          (show (1 : ℝ) < 1 + eta by linarith)
      have hzEq : riemannZeta s = (((riemannZeta s).re : ℝ) : ℂ) := by
        apply Complex.ext
        · change (riemannZeta s).re = (riemannZeta s).re
          rfl
        · simpa using hzim
      have hnormReal : ‖riemannZeta s‖ = (riemannZeta s).re := by
        calc
          ‖riemannZeta s‖ = ‖(((riemannZeta s).re : ℝ) : ℂ)‖ :=
            congrArg norm hzEq
          _ = |(riemannZeta s).re| := by
            rw [Complex.norm_real, Real.norm_eq_abs]
          _ = (riemannZeta s).re := abs_of_pos hzre
      unfold zetaLog
      change S.re = Real.log (riemannZeta s).re
      have hExp : Real.exp S.re = (riemannZeta s).re := hnorm.trans hnormReal
      rw [← hExp, Real.log_exp]

/-- Premise-free certification of the prime-power identity consumed by the
Euler/Fourier reduction of Khale Lemma 5.1. -/
theorem appendixBZetaPrimePowerIdentity : AppendixBZetaPrimePowerIdentity := by
  intro eta heta
  exact ⟨zetaPrimePower_summable heta, zetaPrimePower_tsum_eq_log heta⟩

end
end MAPKhaleAppendixBZetaPrimePowerCertified

#print axioms MAPKhaleAppendixBZetaPrimePowerCertified.appendixBZetaPrimePowerIdentity
