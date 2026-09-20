import SiegelArithmeticPositivity
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Coefficient positivity in Goldfeld's four-L product

The proof of Koukoulopoulos Theorem 12.9 starts from the nonnegative
coefficients of `ζ L(χ) L(ψ) L(χψ)`.  This file proves that arithmetic fact by
matching each prime-power coefficient with a product of four geometric power
series and doing the nine quadratic-value cases.
-/

namespace MAPGoldfeldSiegel

open ComplexOrder ArithmeticFunction PowerSeries
open scoped ArithmeticFunction

noncomputable section

/-- The arithmetic coefficients of Goldfeld's four-factor Dirichlet series. -/
def goldfeldFourfoldCoeff {N : ℕ}
    (chi psi : DirichletCharacter ℂ N) :
    ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta * toArithmeticFunction (chi ·) *
    toArithmeticFunction (psi ·) *
    toArithmeticFunction ((chi * psi) ·)

/-- Dirichlet convolution on a prime power is the usual exponent
antidiagonal sum. -/
theorem ArithmeticFunction.mul_apply_prime_pow
    (f g : ArithmeticFunction ℂ) {p k : ℕ} (hp : p.Prime) :
    (f * g) (p ^ k) =
      ∑ i ∈ Finset.range (k + 1), f (p ^ i) * g (p ^ (k - i)) := by
  rw [ArithmeticFunction.mul_apply]
  change (∑ x ∈ (p ^ k).divisorsAntidiagonal, f x.1 * g x.2) = _
  rw [Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)]
  rw [Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hdiv : p ^ k / p ^ i = p ^ (k - i) := by
    apply Nat.div_eq_of_eq_mul_left (pow_pos hp.pos i)
    rw [Nat.pow_sub_mul_pow p hik]
  rw [hdiv]

/-- The geometric formal power series with ratio `a`. -/
def geometricPS (a : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => a ^ n

@[simp] theorem coeff_geometricPS (a : ℂ) (n : ℕ) :
    PowerSeries.coeff n (geometricPS a) = a ^ n := by
  simp [geometricPS]

/-- Matching prime-power arithmetic coefficients is preserved by Dirichlet
convolution/formal-series multiplication. -/
theorem matchesPrimePowers_mul
    {p : ℕ} (hp : p.Prime)
    {f g : ArithmeticFunction ℂ} {F G : ℂ⟦X⟧}
    (hf : ∀ k, f (p ^ k) = PowerSeries.coeff k F)
    (hg : ∀ k, g (p ^ k) = PowerSeries.coeff k G) :
    ∀ k, (f * g) (p ^ k) = PowerSeries.coeff k (F * G) := by
  intro k
  rw [ArithmeticFunction.mul_apply_prime_pow f g hp]
  simp_rw [hf, hg]
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- The Goldfeld coefficient at `p^k` is the coefficient of the product of
four local geometric series. -/
theorem goldfeldFourfoldCoeff_prime_pow_eq_coeff
    {N : ℕ} (chi psi : DirichletCharacter ℂ N)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    goldfeldFourfoldCoeff chi psi (p ^ k) =
      PowerSeries.coeff k
        (geometricPS 1 * geometricPS (chi p) * geometricPS (psi p) *
          geometricPS (chi p * psi p)) := by
  have hzeta : ∀ j, (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p ^ j) =
      PowerSeries.coeff j (geometricPS 1) := by simp [hp.ne_zero]
  have hchi : ∀ j, toArithmeticFunction (chi ·) (p ^ j) =
      PowerSeries.coeff j (geometricPS (chi p)) := by
    intro j
    simp [toArithmeticFunction, map_pow, hp.ne_zero, mul_pow]
  have hpsi : ∀ j, toArithmeticFunction (psi ·) (p ^ j) =
      PowerSeries.coeff j (geometricPS (psi p)) := by
    intro j
    simp [toArithmeticFunction, map_pow, hp.ne_zero]
  have hmul : ∀ j, toArithmeticFunction ((chi * psi) ·) (p ^ j) =
      PowerSeries.coeff j (geometricPS (chi p * psi p)) := by
    intro j
    simp [toArithmeticFunction, map_pow, hp.ne_zero]
    rw [mul_pow]
  unfold goldfeldFourfoldCoeff
  exact matchesPrimePowers_mul hp
    (matchesPrimePowers_mul hp (matchesPrimePowers_mul hp hzeta hchi) hpsi) hmul k

/-- Coefficientwise nonnegativity for complex power series in the real-axis
order. -/
def PowerSeriesCoeffNonneg (F : ℂ⟦X⟧) : Prop :=
  ∀ n, 0 ≤ PowerSeries.coeff n F

theorem PowerSeriesCoeffNonneg.mul {F G : ℂ⟦X⟧}
    (hF : PowerSeriesCoeffNonneg F) (hG : PowerSeriesCoeffNonneg G) :
    PowerSeriesCoeffNonneg (F * G) := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact Finset.sum_nonneg fun ij _ => mul_nonneg (hF ij.1) (hG ij.2)

@[simp] theorem geometricPS_zero : geometricPS 0 = 1 := by
  ext n
  cases n <;> simp [geometricPS]

theorem coeffNonneg_geometricPS_one : PowerSeriesCoeffNonneg (geometricPS 1) := by
  intro n
  simp

/-- The coefficients of `(1+X+...)(1-X+...)` are zero or one. -/
theorem coeffNonneg_geometricPS_one_mul_neg_one :
    PowerSeriesCoeffNonneg (geometricPS 1 * geometricPS (-1)) := by
  intro n
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_geometricPS, one_pow, one_mul]
  have hreverse :
      (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ (n - i)) =
        ∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i := by
    simpa using Finset.sum_range_reflect (fun i => (-1 : ℂ) ^ i) (n + 1)
  rw [hreverse, neg_one_geom_sum]
  split_ifs <;> simp

/-- The nine local quadratic-value cases. -/
theorem coeffNonneg_goldfeldLocal
    {a b : ℂ} (ha : a = 0 ∨ a = 1 ∨ a = -1)
    (hb : b = 0 ∨ b = 1 ∨ b = -1) :
    PowerSeriesCoeffNonneg (geometricPS 1 * geometricPS a * geometricPS b *
      geometricPS (a * b)) := by
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl
  all_goals simp only [zero_mul, mul_zero, one_mul, neg_mul, mul_neg,
    neg_neg, neg_zero, geometricPS_zero, mul_one]
  · exact coeffNonneg_geometricPS_one
  · exact coeffNonneg_geometricPS_one.mul coeffNonneg_geometricPS_one
  · exact coeffNonneg_geometricPS_one_mul_neg_one
  · exact coeffNonneg_geometricPS_one.mul coeffNonneg_geometricPS_one
  · exact ((coeffNonneg_geometricPS_one.mul coeffNonneg_geometricPS_one).mul
      coeffNonneg_geometricPS_one).mul coeffNonneg_geometricPS_one
  · have hpair := coeffNonneg_geometricPS_one_mul_neg_one
    convert hpair.mul hpair using 1 <;> ring
  · exact coeffNonneg_geometricPS_one_mul_neg_one
  · have hpair := coeffNonneg_geometricPS_one_mul_neg_one
    convert hpair.mul hpair using 1 <;> ring
  · have hpair := coeffNonneg_geometricPS_one_mul_neg_one
    convert hpair.mul hpair using 1 <;> ring

/-- Every prime-power coefficient in Goldfeld's four-L product is
nonnegative. -/
theorem goldfeldFourfoldCoeff_prime_pow_nonneg
    {N : ℕ} {chi psi : DirichletCharacter ℂ N}
    (hchi : chi ^ 2 = 1) (hpsi : psi ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ goldfeldFourfoldCoeff chi psi (p ^ k) := by
  rw [goldfeldFourfoldCoeff_prime_pow_eq_coeff chi psi hp k]
  exact coeffNonneg_goldfeldLocal
    (MulChar.isQuadratic_iff_sq_eq_one.mpr hchi p)
    (MulChar.isQuadratic_iff_sq_eq_one.mpr hpsi p) k

/-- The Goldfeld fourfold coefficient is multiplicative. -/
theorem isMultiplicative_goldfeldFourfoldCoeff
    {N : ℕ} (chi psi : DirichletCharacter ℂ N) :
    (goldfeldFourfoldCoeff chi psi).IsMultiplicative := by
  unfold goldfeldFourfoldCoeff
  exact (((ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    (DirichletCharacter.isMultiplicative_toArithmeticFunction chi)).mul
      (DirichletCharacter.isMultiplicative_toArithmeticFunction psi)).mul
        (DirichletCharacter.isMultiplicative_toArithmeticFunction (chi * psi)))

/-- Goldfeld's source assertion: every coefficient of
`ζ L(χ)L(ψ)L(χψ)` is nonnegative. -/
theorem goldfeldFourfoldCoeff_nonneg
    {N : ℕ} {chi psi : DirichletCharacter ℂ N}
    (hchi : chi ^ 2 = 1) (hpsi : psi ^ 2 = 1) (n : ℕ) :
    0 ≤ goldfeldFourfoldCoeff chi psi n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [goldfeldFourfoldCoeff]
  · rw [(isMultiplicative_goldfeldFourfoldCoeff chi psi).multiplicative_factorization
      _ hn]
    exact Finset.prod_nonneg fun p hp =>
      goldfeldFourfoldCoeff_prime_pow_nonneg hchi hpsi
        (Nat.prime_of_mem_primeFactors hp) _

/-- On the absolutely convergent half-plane, the L-series of the fourfold
coefficient is exactly the product `ζ L(χ)L(ψ)L(χψ)`. -/
theorem LSeries_goldfeldFourfoldCoeff_eq
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => goldfeldFourfoldCoeff chi psi n) s =
      riemannZeta s * DirichletCharacter.LFunction chi s *
        DirichletCharacter.LFunction psi s *
          DirichletCharacter.LFunction (chi * psi) s := by
  let z : ArithmeticFunction ℂ := ArithmeticFunction.zeta
  let a : ArithmeticFunction ℂ := toArithmeticFunction (chi ·)
  let b : ArithmeticFunction ℂ := toArithmeticFunction (psi ·)
  let d : ArithmeticFunction ℂ := toArithmeticFunction ((chi * psi) ·)
  have hz : LSeriesSummable (fun n => z n) s := by
    simpa [z] using (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
  have ha : LSeriesSummable (fun n => a n) s := by
    exact (LSeriesSummable_congr s fun hn =>
      chi.apply_eq_toArithmeticFunction_apply hn).mp
        (DirichletCharacter.LSeriesSummable_of_one_lt_re chi hs)
  have hb : LSeriesSummable (fun n => b n) s := by
    exact (LSeriesSummable_congr s fun hn =>
      psi.apply_eq_toArithmeticFunction_apply hn).mp
        (DirichletCharacter.LSeriesSummable_of_one_lt_re psi hs)
  have hd : LSeriesSummable (fun n => d n) s := by
    exact (LSeriesSummable_congr s fun hn =>
      (chi * psi).apply_eq_toArithmeticFunction_apply hn).mp
        (DirichletCharacter.LSeriesSummable_of_one_lt_re (chi * psi) hs)
  have hza := ArithmeticFunction.LSeriesSummable_mul hz ha
  have hzab := ArithmeticFunction.LSeriesSummable_mul hza hb
  change LSeries (fun n => (((z * a) * b) * d) n) s = _
  rw [show LSeries (fun n => (((z * a) * b) * d) n) s =
      LSeries (fun n => ((z * a) * b) n) s * LSeries (fun n => d n) s by
        simpa only [← ArithmeticFunction.coe_mul] using LSeries_convolution' hzab hd]
  rw [show LSeries (fun n => ((z * a) * b) n) s =
      LSeries (fun n => (z * a) n) s * LSeries (fun n => b n) s by
        simpa only [← ArithmeticFunction.coe_mul] using LSeries_convolution' hza hb]
  rw [show LSeries (fun n => (z * a) n) s =
      LSeries (fun n => z n) s * LSeries (fun n => a n) s by
        simpa only [← ArithmeticFunction.coe_mul] using LSeries_convolution' hz ha]
  rw [show LSeries (fun n => z n) s = riemannZeta s by
      simpa [z] using ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  rw [show LSeries (fun n => a n) s = DirichletCharacter.LFunction chi s by
      rw [DirichletCharacter.LFunction_eq_LSeries chi hs]
      exact LSeries_congr (fun hn =>
        (chi.apply_eq_toArithmeticFunction_apply hn).symm) s]
  rw [show LSeries (fun n => b n) s = DirichletCharacter.LFunction psi s by
      rw [DirichletCharacter.LFunction_eq_LSeries psi hs]
      exact LSeries_congr (fun hn =>
        (psi.apply_eq_toArithmeticFunction_apply hn).symm) s]
  rw [show LSeries (fun n => d n) s =
      DirichletCharacter.LFunction (chi * psi) s by
      rw [DirichletCharacter.LFunction_eq_LSeries (chi * psi) hs]
      exact LSeries_congr (fun hn =>
        ((chi * psi).apply_eq_toArithmeticFunction_apply hn).symm) s]

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.goldfeldFourfoldCoeff_nonneg
#print axioms MAPGoldfeldSiegel.LSeries_goldfeldFourfoldCoeff_eq
