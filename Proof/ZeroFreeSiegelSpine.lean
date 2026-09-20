import DirichletLQuantitativeFoundation
import PrimitiveExplicitFormulaSpine
import PrimitiveTruncatedExplicitFormulaBridge
import PrimitiveLFixedStripGrowth
import SiegelWalfiszCharacterReduction
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Constructive spine for the classical zero-free/Siegel argument

This file exposes reusable pieces of the classical proof rather than declaring
the zero-free region, exceptional-zero theorem, or Siegel lower bound as an
opaque proposition.  The first section publicizes the `3-4-1` positivity at the
coefficient level.  Later sections isolate exact deterministic consequences of
zero repulsion and of a lower bound for `L(1, chi)`.
-/

namespace MAPZeroFreeSiegelSpine

open Complex Set DirichletZeros
open scoped BigOperators ArithmeticFunction LSeries.notation

noncomputable section

/-! ## The algebra behind the three-character positivity device -/

/-- The `3-4-1` polynomial is nonnegative throughout the closed complex unit
disk.  On the unit circle this is the classical identity
`3 + 4 cos theta + cos (2 theta) = 2 (1 + cos theta)^2`; the disk form also
covers the zero values of a Dirichlet character at bad primes. -/
theorem threeFourOne_nonneg_of_norm_le_one (z : ℂ) (hz : ‖z‖ ≤ 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have hnormSq : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have hsq : ‖z‖ ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg z) zero_le_one).2 hz
    rw [Complex.sq_norm, Complex.normSq_apply] at hsq
    simpa [pow_two] using hsq
  simp only [pow_two, Complex.mul_re]
  nlinarith [sq_nonneg (z.re + 1)]

/-- The oscillatory character value occurring in the logarithmic derivative
at `sigma + i t`. -/
def characterPhase {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) : ℂ :=
  χ n * Complex.exp (((-(Real.log n * t) : ℝ) : ℂ) * Complex.I)

/-- Every oscillatory character value lies in the closed unit disk. -/
theorem norm_characterPhase_le_one {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) :
    ‖characterPhase χ t n‖ ≤ 1 := by
  rw [characterPhase, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact χ.norm_le_one n

/-- Pointwise `3-4-1` positivity for a Dirichlet character, including the
nonunit residue classes where the character vanishes. -/
theorem threeFourOne_characterPhase_nonneg {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) :
    0 ≤ 3 + 4 * (characterPhase χ t n).re +
      ((characterPhase χ t n) ^ 2).re :=
  threeFourOne_nonneg_of_norm_le_one _ (norm_characterPhase_le_one χ t n)

/-- The literal nonnegative Mangoldt summand in the three-character
logarithmic-derivative inequality. -/
def threeCharacterMangoldtTerm {q : ℕ}
    (χ : DirichletCharacter ℂ q) (σ t : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)) *
    (3 + 4 * (characterPhase χ t n).re +
      ((characterPhase χ t n) ^ 2).re)

/-- Each literal three-character Mangoldt summand is nonnegative. -/
theorem threeCharacterMangoldtTerm_nonneg {q : ℕ}
    (χ : DirichletCharacter ℂ q) (σ t : ℝ) (n : ℕ) :
    0 ≤ threeCharacterMangoldtTerm χ σ t n := by
  apply mul_nonneg
  · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) (-σ))
  · exact threeFourOne_characterPhase_nonneg χ t n

/-- Every finite truncation of the three-character Mangoldt series is
nonnegative, with no analytic continuation or limiting argument. -/
theorem sum_threeCharacterMangoldtTerm_nonneg {q : ℕ}
    (χ : DirichletCharacter ℂ q) (σ t : ℝ) (S : Finset ℕ) :
    0 ≤ ∑ n ∈ S, threeCharacterMangoldtTerm χ σ t n := by
  exact Finset.sum_nonneg fun n _ => threeCharacterMangoldtTerm_nonneg χ σ t n

private theorem natCast_cpow_neg_I_mul {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ (-(Complex.I * (t : ℂ))) =
      Complex.exp (((-(Real.log n * t) : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
  rw [← Complex.natCast_log]
  congr 1
  push_cast
  ring

/-- One twisted Mangoldt `L`-series term has exactly the expected radial
weight times oscillatory character phase. -/
theorem re_twistedMangoldtTerm_eq {q : ℕ}
    (χ : DirichletCharacter ℂ q) (σ t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (LSeries.term (PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff χ)
      (σ + Complex.I * t) n).re =
      (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)) *
        (characterPhase χ t n).re := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
  have hrpow : (n : ℂ) ^ ((-σ : ℝ) : ℂ) =
      (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow (Nat.cast_nonneg n) (-σ)).symm
  rw [show -(↑σ + Complex.I * ↑t) =
      ((-σ : ℝ) : ℂ) + -(Complex.I * (t : ℂ)) by push_cast; ring,
    Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn),
    hrpow,
    natCast_cpow_neg_I_mul hn t]
  simp only [PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff,
    characterPhase, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

/-- The untwisted Mangoldt term on the real axis is its usual positive
radial weight. -/
theorem re_vonMangoldtTerm_eq (σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (LSeries.term (fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℂ)) σ n).re =
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
  have hrpow : (n : ℂ) ^ ((-σ : ℝ) : ℂ) =
      (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow (Nat.cast_nonneg n) (-σ)).symm
  rw [show -(σ : ℂ) = ((-σ : ℝ) : ℂ) by push_cast; ring]
  rw [hrpow]
  simp

/-- Squaring a character and doubling the frequency squares the oscillatory
phase exactly. -/
theorem characterPhase_sq {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) :
    characterPhase (χ ^ 2) (2 * t) n = (characterPhase χ t n) ^ 2 := by
  have hexp :
      Complex.exp (((-(Real.log n * (2 * t)) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((-(Real.log n * t) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((-(Real.log n * t) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [characterPhase, χ.pow_apply' two_ne_zero]
  rw [hexp]
  ring

/-! ## The logarithmic-derivative inequality on `Re s > 1` -/

/-- The convergent Mangoldt Dirichlet series satisfy the classical
three-character real-part inequality.  This is the differentiable form of the
Euler-product positivity used in de la Vallee Poussin's zero-free argument. -/
theorem threeCharacter_LSeries_re_nonneg {q : ℕ}
    (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤
      3 * (LSeries (fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℂ)) σ).re +
      4 * (LSeries (PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff χ)
        (σ + Complex.I * t)).re +
      (LSeries (PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff (χ ^ 2))
        (σ + Complex.I * (2 * t))).re := by
  have h0 : LSeriesSummable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have h1 : LSeriesSummable
      (PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff χ)
      (σ + Complex.I * t) := by
    simpa only [PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff] using
      (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ
        (by simpa using hσ))
  have h2 : LSeriesSummable
      (PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff (χ ^ 2))
      (σ + Complex.I * (2 * t)) := by
    simpa only [PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff] using
      (DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ ^ 2)
        (by simpa using hσ))
  have h0r := (hasSum_re h0.hasSum).summable.mul_left 3
  have h1r := (hasSum_re h1.hasSum).summable.mul_left 4
  have h2r := (hasSum_re h2.hasSum).summable
  have h0eq :
      (LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) σ).re =
        ∑' n, (LSeries.term (fun n : ℕ =>
          (ArithmeticFunction.vonMangoldt n : ℂ)) σ n).re := by
    exact re_tsum h0
  have h1eq :
      (LSeries (PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff χ)
        (σ + Complex.I * t)).re =
        ∑' n, (LSeries.term
          (PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff χ)
          (σ + Complex.I * t) n).re := by
    exact re_tsum h1
  have h2eq :
      (LSeries (PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff (χ ^ 2))
        (σ + Complex.I * (2 * t))).re =
        ∑' n, (LSeries.term
          (PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff (χ ^ 2))
          (σ + Complex.I * (2 * t)) n).re := by
    exact re_tsum h2
  rw [h0eq, h1eq, h2eq,
    ← tsum_mul_left, ← tsum_mul_left,
    ← h0r.tsum_add h1r, ← (h0r.add h1r).tsum_add h2r]
  refine (tsum_nonneg fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [re_vonMangoldtTerm_eq σ hn,
      re_twistedMangoldtTerm_eq χ σ t hn]
    have harg :
        (σ : ℂ) + Complex.I * (2 * (t : ℂ)) =
          (σ : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, re_twistedMangoldtTerm_eq (χ ^ 2) σ (2 * t) hn,
      characterPhase_sq]
    convert threeCharacterMangoldtTerm_nonneg χ σ t n using 1
    simp only [threeCharacterMangoldtTerm]
    ring

/-- The same inequality stated directly for logarithmic derivatives of the
actual continued `L`-functions (and zeta).  No zero estimate is used: this is
an exact consequence of absolute convergence on `sigma > 1`. -/
theorem threeCharacter_neg_logDeriv_re_nonneg {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤
      3 * (-logDeriv riemannZeta σ).re +
      4 * (-logDeriv (DirichletCharacter.LFunction χ)
        (σ + Complex.I * t)).re +
      (-logDeriv (DirichletCharacter.LFunction (χ ^ 2))
        (σ + Complex.I * (2 * t))).re := by
  have hzeta := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (show 1 < (σ : ℂ).re by simpa using hσ)
  have hχ :=
    PrimitiveExplicitFormulaSpine.LSeries_twistedMangoldtCoeff_eq_neg_logDeriv_LFunction
      χ (show 1 < (σ + Complex.I * t : ℂ).re by simpa using hσ)
  have hχ2 :=
    PrimitiveExplicitFormulaSpine.LSeries_twistedMangoldtCoeff_eq_neg_logDeriv_LFunction
      (χ ^ 2) (show 1 < (σ + Complex.I * (2 * t) : ℂ).re by simpa using hσ)
  have hbase := threeCharacter_LSeries_re_nonneg χ hσ t
  rw [hzeta, hχ, hχ2] at hbase
  simpa only [logDeriv_apply, neg_div] using hbase

/-! ## The exact divisor-backed logarithmic-derivative decomposition -/

open MAPLocalZeroWindow MAPMellinDetectorLeaf

/-- The finite product over the centered unit zero window used in the
classical local logarithmic-derivative formula.  Both its support and its
exponents come from the actual `DirichletZeros` divisor. -/
def centeredZeroFactorProduct {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) (s : ℂ) : ℂ :=
  ∏ ρ ∈ centeredUnitWindowSupport χ (1 / 2) t,
    (s - ρ) ^ zeroMultiplicity χ (1 / 2) (windowHeight (t - 1 / 2)) ρ

/-- The literal multiplicity-weighted pole sum in the centered unit window. -/
def centeredZeroPoleSum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) (s : ℂ) : ℂ :=
  ∑ ρ ∈ centeredUnitWindowSupport χ (1 / 2) t,
    (zeroMultiplicity χ (1 / 2) (windowHeight (t - 1 / 2)) ρ : ℂ) /
      (s - ρ)

/-- Every point of the centered support is a point of the underlying compact
`DirichletZeros.zeroSupport`. -/
theorem mem_zeroSupport_of_mem_centeredUnitWindowSupport
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ centeredUnitWindowSupport χ (1 / 2) t) :
    ρ ∈ zeroSupport χ (1 / 2) (windowHeight (t - 1 / 2)) := by
  exact (Finset.mem_filter.mp hρ).1

/-- The Euler-product zero-free half-plane is disjoint from the centered
divisor support. -/
theorem not_mem_centeredUnitWindowSupport_of_one_le_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
    {s : ℂ} (hs : 1 ≤ s.re) :
    s ∉ centeredUnitWindowSupport χ (1 / 2) t := by
  intro hmem
  have hre := re_lt_one_of_mem_zeroSupport χ
    (mem_zeroSupport_of_mem_centeredUnitWindowSupport χ hmem)
  linarith

/-- The centered zero product does not vanish away from its literal finite
support. -/
theorem centeredZeroFactorProduct_ne_zero_of_not_mem
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
    {s : ℂ} (hs : s ∉ centeredUnitWindowSupport χ (1 / 2) t) :
    centeredZeroFactorProduct χ t s ≠ 0 := by
  simp only [centeredZeroFactorProduct, Finset.prod_ne_zero_iff]
  intro ρ hρ
  exact pow_ne_zero _ (sub_ne_zero.mpr fun h => hs (h ▸ hρ))

/-- The logarithmic derivative of the centered zero product is exactly the
divisor-backed pole sum, with analytic multiplicity. -/
theorem logDeriv_centeredZeroFactorProduct
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
    {s : ℂ} (hs : s ∉ centeredUnitWindowSupport χ (1 / 2) t) :
    logDeriv (centeredZeroFactorProduct χ t) s =
      centeredZeroPoleSum χ t s := by
  unfold centeredZeroPoleSum
  rw [show centeredZeroFactorProduct χ t =
      fun z => ∏ ρ ∈ centeredUnitWindowSupport χ (1 / 2) t,
        (z - ρ) ^ zeroMultiplicity χ (1 / 2)
          (windowHeight (t - 1 / 2)) ρ by rfl]
  rw [logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    rw [logDeriv_fun_pow (by fun_prop)]
    simp only [logDeriv_apply, deriv_sub_const]
    have hderiv : deriv (fun y : ℂ => y) s = 1 := by
      simpa only [id_eq] using deriv_id s
    rw [hderiv]
    ring
  · intro ρ hρ
    exact pow_ne_zero _ (sub_ne_zero.mpr fun h => hs (h ▸ hρ))
  · intro ρ hρ
    fun_prop

/-- The regularized primitive L-function divided by precisely the zeros in
the centered unit window.  This is a function, rather than an opaque
zero-free-region proposition. -/
def centeredZeroDeflatedRegularizedLFunction
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) (s : ℂ) : ℂ :=
  regularizedLFunction χ s / centeredZeroFactorProduct χ t s

/-- Exact finite zero-sum decomposition on `Re s ≥ 1`.  It uses only Euler
product nonvanishing and the actual divisor; no zero-free region or remainder
estimate is assumed. -/
theorem neg_logDeriv_regularizedLFunction_eq_centeredZeroSum_add_deflated
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) {s : ℂ} (hs : 1 ≤ s.re) :
    -logDeriv (regularizedLFunction χ) s =
      -centeredZeroPoleSum χ t s -
        logDeriv (centeredZeroDeflatedRegularizedLFunction χ t) s := by
  have hsupp : s ∉ centeredUnitWindowSupport χ (1 / 2) t :=
    not_mem_centeredUnitWindowSupport_of_one_le_re χ t hs
  have hf : regularizedLFunction χ s ≠ 0 :=
    regularizedLFunction_ne_zero_of_one_le_re χ hs
  have hp : centeredZeroFactorProduct χ t s ≠ 0 :=
    centeredZeroFactorProduct_ne_zero_of_not_mem χ t hsupp
  have hpDiff : DifferentiableAt ℂ (centeredZeroFactorProduct χ t) s := by
    change DifferentiableAt ℂ
      (fun z => ∏ ρ ∈ centeredUnitWindowSupport χ (1 / 2) t,
        (z - ρ) ^ zeroMultiplicity χ (1 / 2)
          (windowHeight (t - 1 / 2)) ρ) s
    fun_prop
  have hdiv := logDeriv_div s hf hp
    (differentiable_regularizedLFunction χ).differentiableAt hpDiff
  rw [logDeriv_centeredZeroFactorProduct χ t hsupp] at hdiv
  change logDeriv (centeredZeroDeflatedRegularizedLFunction χ t) s = _ at hdiv
  rw [hdiv]
  ring

/-- Nonprincipal specialization of the exact decomposition for the actual
Dirichlet L-function. -/
theorem neg_logDeriv_LFunction_eq_centeredZeroSum_add_deflated
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (t : ℝ) {s : ℂ} (hs : 1 ≤ s.re) :
    -logDeriv (DirichletCharacter.LFunction χ) s =
      -centeredZeroPoleSum χ t s -
        logDeriv (centeredZeroDeflatedRegularizedLFunction χ t) s := by
  simpa [regularizedLFunction, hχ] using
    neg_logDeriv_regularizedLFunction_eq_centeredZeroSum_add_deflated χ t hs

/-- The literal remainder in the centered explicit logarithmic-derivative
formula, evaluated at `u + i t`. -/
def primitiveLogDerivativeRemainder {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (u t : ℝ) : ℂ :=
  -logDeriv (centeredZeroDeflatedRegularizedLFunction χ t)
    (u + Complex.I * t)

/-- Exact formula at `u + i t`, with the remainder exposed as a concrete
logarithmic derivative of the zero-deflated function. -/
theorem neg_logDeriv_LFunction_eq_centeredZeroSum_add_remainder
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {u : ℝ} (hu : 1 ≤ u) (t : ℝ) :
    -logDeriv (DirichletCharacter.LFunction χ)
        (u + Complex.I * t) =
      -centeredZeroPoleSum χ t (u + Complex.I * t) +
        primitiveLogDerivativeRemainder χ u t := by
  simpa [primitiveLogDerivativeRemainder] using
    neg_logDeriv_LFunction_eq_centeredZeroSum_add_deflated χ hχ t
      (s := u + Complex.I * t) (by simpa using hu)

/-- Every pole term in the centered divisor sum has nonnegative real part
when evaluated to the right of `Re s = 1`. -/
theorem re_centeredZeroPoleTerm_nonneg
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {u t : ℝ} (hu : 1 ≤ u) {ρ : ℂ}
    (hρ : ρ ∈ centeredUnitWindowSupport χ (1 / 2) t) :
    0 ≤ ((zeroMultiplicity χ (1 / 2)
        (windowHeight (t - 1 / 2)) ρ : ℂ) /
      ((u : ℂ) + Complex.I * t - ρ)).re := by
  have hre := re_lt_one_of_mem_zeroSupport χ
    (mem_zeroSupport_of_mem_centeredUnitWindowSupport χ hρ)
  rw [show (((zeroMultiplicity χ (1 / 2)
      (windowHeight (t - 1 / 2)) ρ : ℂ) /
      ((u : ℂ) + Complex.I * t - ρ)).re) =
      (zeroMultiplicity χ (1 / 2)
        (windowHeight (t - 1 / 2)) ρ : ℝ) *
        (u - ρ.re) /
          Complex.normSq ((u : ℂ) + Complex.I * t - ρ) by
    rw [Complex.div_re]
    simp]
  exact div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hre.le.trans hu)))
    (Complex.normSq_nonneg _)

/-- Any selected divisor pole term is bounded by the real part of the full
centered pole sum. -/
theorem re_centeredZeroPoleTerm_le_re_centeredZeroPoleSum
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {u t : ℝ} (hu : 1 ≤ u) {ρ : ℂ}
    (hρ : ρ ∈ centeredUnitWindowSupport χ (1 / 2) t) :
    ((zeroMultiplicity χ (1 / 2)
        (windowHeight (t - 1 / 2)) ρ : ℂ) /
      ((u : ℂ) + Complex.I * t - ρ)).re ≤
        (centeredZeroPoleSum χ t (u + Complex.I * t)).re := by
  unfold centeredZeroPoleSum
  rw [Complex.re_sum]
  exact Finset.single_le_sum
    (fun τ hτ => re_centeredZeroPoleTerm_nonneg χ hu hτ) hρ

/-- A pole whose ordinate equals the evaluation height contributes exactly
`multiplicity / (u - Re rho)` to the real pole sum. -/
theorem re_centeredZeroPoleTerm_eq_reciprocal_of_im_eq
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {u t : ℝ} {ρ : ℂ} (huρ : ρ.re < u) (him : ρ.im = t) :
    ((zeroMultiplicity χ (1 / 2)
        (windowHeight (t - 1 / 2)) ρ : ℂ) /
      ((u : ℂ) + Complex.I * t - ρ)).re =
        (zeroMultiplicity χ (1 / 2)
          (windowHeight (t - 1 / 2)) ρ : ℝ) / (u - ρ.re) := by
  rw [show (((zeroMultiplicity χ (1 / 2)
      (windowHeight (t - 1 / 2)) ρ : ℂ) /
      ((u : ℂ) + Complex.I * t - ρ)).re) =
      (zeroMultiplicity χ (1 / 2)
        (windowHeight (t - 1 / 2)) ρ : ℝ) *
        (u - ρ.re) /
          Complex.normSq ((u : ℂ) + Complex.I * t - ρ) by
    rw [Complex.div_re]
    simp]
  have hgap : u - ρ.re ≠ 0 := sub_ne_zero.mpr (ne_of_gt huρ)
  have hnorm : Complex.normSq ((u : ℂ) + Complex.I * t - ρ) =
      (u - ρ.re) ^ 2 := by
    rw [Complex.normSq_apply]
    simp [him]
    ring
  rw [hnorm]
  field_simp

/-- Exact single-zero isolation from a concrete remainder bound.  This is the
source-shaped upper bound consumed by `zero_gap_lower_of_logDeriv_bounds`. -/
theorem neg_logDeriv_re_le_logScale_sub_zeroPole
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {u t C : ℝ} (hu : 1 < u) {ρ : ℂ}
    (hρ : ρ ∈ centeredUnitWindowSupport χ (1 / 2) t)
    (him : ρ.im = t)
    (hrem : ‖primitiveLogDerivativeRemainder χ u t‖ ≤
      C * Real.log (arithmeticScale q t)) :
    (-logDeriv (DirichletCharacter.LFunction χ)
        (u + Complex.I * t)).re ≤
      C * Real.log (arithmeticScale q t) -
        (zeroMultiplicity χ (1 / 2)
          (windowHeight (t - 1 / 2)) ρ : ℝ) / (u - ρ.re) := by
  have hre := re_lt_one_of_mem_zeroSupport χ
    (mem_zeroSupport_of_mem_centeredUnitWindowSupport χ hρ)
  have huρ : ρ.re < u := hre.trans hu
  have hterm := re_centeredZeroPoleTerm_le_re_centeredZeroPoleSum χ hu.le hρ
  rw [re_centeredZeroPoleTerm_eq_reciprocal_of_im_eq χ huρ him] at hterm
  have hremRe : (primitiveLogDerivativeRemainder χ u t).re ≤
      C * Real.log (arithmeticScale q t) :=
    (Complex.re_le_norm _).trans hrem
  rw [neg_logDeriv_LFunction_eq_centeredZeroSum_add_remainder χ hχ hu.le t,
    Complex.add_re, Complex.neg_re]
  linarith

/-- The first missing analytic theorem after the exact divisor algebra: a
uniform Borel--Caratheodory/Hadamard bound for the zero-deflated logarithmic
derivative.  This proposition is deliberately not inhabited here. -/
def UniformPrimitiveLogDerivativeRemainderBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 →
      ∀ u t : ℝ, 1 < u → u ≤ 2 →
        ‖primitiveLogDerivativeRemainder χ u t‖ ≤
          C * Real.log (arithmeticScale q t)

/-- A supplied uniform remainder theorem produces the source-facing
`O(log(q(|t|+2)))` explicit logarithmic-derivative formula with the actual
divisor pole sum. -/
theorem UniformPrimitiveLogDerivativeRemainderBound.exists_explicitFormula
    (h : UniformPrimitiveLogDerivativeRemainderBound) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 →
        ∀ u t : ℝ, 1 < u → u ≤ 2 →
          -logDeriv (DirichletCharacter.LFunction χ)
              (u + Complex.I * t) =
            -centeredZeroPoleSum χ t (u + Complex.I * t) +
              primitiveLogDerivativeRemainder χ u t ∧
          ‖primitiveLogDerivativeRemainder χ u t‖ ≤
            C * Real.log (arithmeticScale q t) := by
  rcases h with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro q _ χ hprim hχ u t hu hu2
  exact ⟨neg_logDeriv_LFunction_eq_centeredZeroSum_add_remainder
      χ hχ hu.le t,
    hbound q χ hprim hχ u t hu hu2⟩

/-- The real-part upper bound consumed by the three-character positivity
argument.  All pole contributions remain in the literal divisor sum. -/
theorem UniformPrimitiveLogDerivativeRemainderBound.exists_realPartUpperBound
    (h : UniformPrimitiveLogDerivativeRemainderBound) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 →
        ∀ u t : ℝ, 1 < u → u ≤ 2 →
          (-logDeriv (DirichletCharacter.LFunction χ)
              (u + Complex.I * t)).re ≤
            (-centeredZeroPoleSum χ t (u + Complex.I * t)).re +
              C * Real.log (arithmeticScale q t) := by
  rcases h.exists_explicitFormula with ⟨C, hC, hformula⟩
  refine ⟨C, hC, ?_⟩
  intro q _ χ hprim hχ u t hu hu2
  rcases hformula q χ hprim hχ u t hu hu2 with ⟨heq, hrem⟩
  rw [heq, Complex.add_re]
  calc
    (-centeredZeroPoleSum χ t (u + Complex.I * t)).re +
          (primitiveLogDerivativeRemainder χ u t).re ≤
        (-centeredZeroPoleSum χ t (u + Complex.I * t)).re +
          ‖primitiveLogDerivativeRemainder χ u t‖ := by
      gcongr
      exact Complex.re_le_norm _
    _ ≤ (-centeredZeroPoleSum χ t (u + Complex.I * t)).re +
          C * Real.log (arithmeticScale q t) := by
      gcongr

/-- Uniform single-zero specialization of the explicit formula.  The pole
has its actual analytic multiplicity and no zero-free conclusion is assumed. -/
theorem UniformPrimitiveLogDerivativeRemainderBound.exists_singleZeroUpperBound
    (h : UniformPrimitiveLogDerivativeRemainderBound) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 →
        ∀ u t : ℝ, 1 < u → u ≤ 2 →
          ∀ ρ ∈ centeredUnitWindowSupport χ (1 / 2) t,
            ρ.im = t →
            (-logDeriv (DirichletCharacter.LFunction χ)
                (u + Complex.I * t)).re ≤
              C * Real.log (arithmeticScale q t) -
                (zeroMultiplicity χ (1 / 2)
                  (windowHeight (t - 1 / 2)) ρ : ℝ) / (u - ρ.re) := by
  rcases h with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro q _ χ hprim hχ u t hu hu2 ρ hρ him
  exact neg_logDeriv_re_le_logScale_sub_zeroPole χ hχ hu hρ him
    (hbound q χ hprim hχ u t hu hu2)

/-- The quantitative gap extraction used after an explicit logarithmic-
derivative formula has isolated a zero's pole term.  The hypotheses are
literal upper bounds for the three functions in the `3-4-1` inequality. -/
theorem zero_gap_lower_of_logDeriv_bounds
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ β m K Z D : ℝ} (hσ : 1 < σ) (t : ℝ)
    (hgap : 0 < σ - β)
    (hzeta : (-logDeriv riemannZeta σ).re ≤ Z)
    (hχ : (-logDeriv (DirichletCharacter.LFunction χ)
      (σ + Complex.I * t)).re ≤ K - m / (σ - β))
    (hsquare : (-logDeriv (DirichletCharacter.LFunction (χ ^ 2))
      (σ + Complex.I * (2 * t))).re ≤ D)
    (hden : 0 < 3 * Z + 4 * K + D) :
    4 * m / (3 * Z + 4 * K + D) ≤ σ - β := by
  have hpos := threeCharacter_neg_logDeriv_re_nonneg χ hσ t
  have hpole : 4 * m / (σ - β) ≤ 3 * Z + 4 * K + D := by
    have hsumle :
        3 * (-logDeriv riemannZeta σ).re +
            4 * (-logDeriv (DirichletCharacter.LFunction χ)
              (σ + Complex.I * t)).re +
            (-logDeriv (DirichletCharacter.LFunction (χ ^ 2))
              (σ + Complex.I * (2 * t))).re ≤
          3 * Z + 4 * (K - m / (σ - β)) + D := by
      gcongr
    have hnonneg : 0 ≤ 3 * Z + 4 * (K - m / (σ - β)) + D :=
      hpos.trans hsumle
    rw [show 3 * Z + 4 * (K - m / (σ - β)) + D =
        (3 * Z + 4 * K + D) - 4 * (m / (σ - β)) by ring] at hnonneg
    calc
      4 * m / (σ - β) = 4 * (m / (σ - β)) := by ring
      _ ≤ 3 * Z + 4 * K + D := by linarith
  have hmul : 4 * m ≤ (3 * Z + 4 * K + D) * (σ - β) :=
    (div_le_iff₀ hgap).mp hpole
  apply (div_le_iff₀ hden).2
  nlinarith

/-! ## Exact isolation consequences of a numerical repulsion estimate -/

/-- A generic Landau--Page isolation lemma.  Once an analytic argument gives
the displayed pair-repulsion inequality, at most one candidate can have gap
at most `eta`.  The result is deliberately stated for an arbitrary finite
family so it can later index primitive characters of varying conductors. -/
theorem card_nearOneCandidates_le_one
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (β : ι → ℝ)
    {η d : ℝ}
    (hrepel : ∀ ⦃i j⦄, i ∈ S → j ∈ S → i ≠ j →
      d ≤ (1 - β i) + (1 - β j))
    (hηd : 2 * η < d) :
    (S.filter fun i => 1 - β i ≤ η).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro i j hi hj
  have hiS := (Finset.mem_filter.mp hi).1
  have hjS := (Finset.mem_filter.mp hj).1
  have hiη := (Finset.mem_filter.mp hi).2
  have hjη := (Finset.mem_filter.mp hj).2
  by_contra hij
  have hrep := hrepel hiS hjS hij
  linarith

/-- If a finite candidate set is stable under complex conjugation and has at
most one element, that element must be real.  This is the exact final algebra
after conjugation symmetry of a real-character `L`-function is supplied. -/
theorem im_eq_zero_of_card_le_one_of_conj_mem
    (S : Finset ℂ) (hcard : S.card ≤ 1)
    (hconj : ∀ ⦃ρ : ℂ⦄, ρ ∈ S → (starRingEnd ℂ) ρ ∈ S)
    {ρ : ℂ} (hρ : ρ ∈ S) : ρ.im = 0 := by
  have heq : ρ = (starRingEnd ℂ) ρ :=
    (Finset.card_le_one_iff.mp hcard) hρ (hconj hρ)
  have him := congrArg Complex.im heq
  have him' : ρ.im = -ρ.im := by simpa using him
  linarith

/-- The literal compact support of real zeros in the strip
`1 - eta <= Re rho <= 1`.  Height zero forces every point to be real. -/
def exceptionalRealZeroSupport {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (η : ℝ) : Finset ℂ :=
  zeroSupport χ (1 - η) 0

theorem mem_exceptionalRealZeroSupport_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {η : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ exceptionalRealZeroSupport χ η) :
    1 - η ≤ ρ.re ∧ ρ.re ≤ 1 := by
  have hrect := PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
    χ (1 - η) 0 hρ
  exact (Complex.mem_reProdIm.mp hrect).1

theorem mem_exceptionalRealZeroSupport_im_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {η : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ exceptionalRealZeroSupport χ η) : ρ.im = 0 := by
  have hrect := PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
    χ (1 - η) 0 hρ
  have him := (Complex.mem_reProdIm.mp hrect).2
  simp only [mem_Icc] at him
  linarith

/-- A numerical pair-repulsion inequality on actual divisor-backed zeros
isolates at most one real zero in the narrower strip. -/
theorem card_exceptionalRealZeroSupport_le_one_of_pair_repulsion
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {η d : ℝ}
    (hrepel : ∀ ⦃ρ₁ ρ₂ : ℂ⦄,
      ρ₁ ∈ exceptionalRealZeroSupport χ η →
      ρ₂ ∈ exceptionalRealZeroSupport χ η → ρ₁ ≠ ρ₂ →
        d ≤ (1 - ρ₁.re) + (1 - ρ₂.re))
    (hηd : 2 * η < d) :
    (exceptionalRealZeroSupport χ η).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro ρ₁ ρ₂ hρ₁ hρ₂
  by_contra hne
  have hrep := hrepel hρ₁ hρ₂ hne
  have h₁ := (mem_exceptionalRealZeroSupport_re χ hρ₁).1
  have h₂ := (mem_exceptionalRealZeroSupport_re χ hρ₂).1
  linarith

/-- Every point in the divisor support has positive analytic multiplicity. -/
theorem zeroMultiplicity_pos_of_mem {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport χ σ T) :
    0 < zeroMultiplicity χ σ T ρ := by
  have hne : zeroDivisor χ σ T ρ ≠ 0 :=
    (zeroSupport_mem_iff χ σ T ρ).mp hρ
  have hrect : ρ ∈ zeroRectangle σ T :=
    (zeroDivisor χ σ T).supportWithinDomain hne
  have hnonneg : 0 ≤ zeroDivisor χ σ T ρ :=
    zeroDivisor_nonneg_of_mem χ σ T hrect
  have hpos : 0 < zeroDivisor χ σ T ρ :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  rw [← Int.ofNat_lt]
  simpa [zeroMultiplicity, Int.toNat_of_nonneg hnonneg] using hpos

/-- An upper bound strictly below two for the analytic multiplicity forces a
supported zero to be simple. -/
theorem zeroMultiplicity_eq_one_of_lt_two {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport χ σ T)
    (hlt : (zeroMultiplicity χ σ T ρ : ℝ) < 2) :
    zeroMultiplicity χ σ T ρ = 1 := by
  have hpos := zeroMultiplicity_pos_of_mem χ σ T hρ
  have hltNat : zeroMultiplicity χ σ T ρ < 2 := by exact_mod_cast hlt
  omega

/-- The form used after bounding a zero's reciprocal contribution to a
logarithmic derivative: if the normalized multiplicity lies below the
two-fold pole contribution, the zero is simple. -/
theorem zeroMultiplicity_eq_one_of_reciprocal_bound
    {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) {ρ : ℂ} {a U : ℝ}
    (hρ : ρ ∈ zeroSupport χ σ T) (ha : 0 < a)
    (hupper : (zeroMultiplicity χ σ T ρ : ℝ) / a ≤ U)
    (hU : U < 2 / a) :
    zeroMultiplicity χ σ T ρ = 1 := by
  apply zeroMultiplicity_eq_one_of_lt_two χ σ T hρ
  exact (div_lt_div_iff_of_pos_right ha).mp (hupper.trans_lt hU)

/-! ## The exact calculus bridge from `L(1, chi)` to a zero gap -/

/-- The classical ineffective Siegel lower bound, isolated as a separately
named published input.  It is not proved or inhabited in this file.  The
condition `χ ^ 2 = 1` selects real nontrivial characters. -/
def PublishedSiegelLValueLowerBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 →
          c * (q : ℝ) ^ (-ε) ≤
            ‖DirichletCharacter.LFunction χ 1‖

/-- Direct specialization of the separately named published Siegel input. -/
theorem PublishedSiegelLValueLowerBound.specialize
    (h : PublishedSiegelLValueLowerBound) {ε : ℝ} (hε : 0 < ε)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (hreal : χ ^ 2 = 1) :
    ∃ c : ℝ, 0 < c ∧
      c * (q : ℝ) ^ (-ε) ≤
        ‖DirichletCharacter.LFunction χ 1‖ := by
  rcases h ε hε with ⟨c, hc, hbound⟩
  exact ⟨c, hc, hbound q χ hprim hχ hreal⟩

/-- If `L(beta, chi)=0`, a derivative bound on `[beta,1]` converts the value
at one into an explicit upper bound by the zero gap. -/
theorem norm_LFunction_one_le_gap_mul_of_deriv_bound
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {β M : ℝ} (hβ : β ≤ 1)
    (hzero : DirichletCharacter.LFunction χ β = 0)
    (hderiv : ∀ x ∈ Set.Ico β 1,
      ‖deriv (DirichletCharacter.LFunction χ) x‖ ≤ M) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤ M * (1 - β) := by
  let f : ℝ → ℂ := fun x => DirichletCharacter.LFunction χ x
  let f' : ℝ → ℂ := fun x => deriv (DirichletCharacter.LFunction χ) x
  have hf : ∀ x ∈ Set.Icc β 1,
      HasDerivWithinAt f (f' x) (Set.Icc β 1) x := by
    intro x hx
    exact ((DirichletCharacter.differentiableAt_LFunction χ (x : ℂ)
      (.inr hχ)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico β 1, ‖f' x‖ ≤ M := by
    intro x hx
    exact hderiv x hx
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hf hbound
    1 (Set.right_mem_Icc.mpr hβ)
  simpa only [f, f', hzero, sub_zero] using hmv

/-- A Siegel-type lower bound for `L(1, chi)`, together with a derivative
majorant, gives a literal lower bound for the exceptional zero gap. -/
theorem zero_gap_lower_of_LFunction_one_lower_bound
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {β M lower : ℝ} (hβ : β ≤ 1) (hM : 0 < M)
    (hzero : DirichletCharacter.LFunction χ β = 0)
    (hderiv : ∀ x ∈ Set.Ico β 1,
      ‖deriv (DirichletCharacter.LFunction χ) x‖ ≤ M)
    (hLone : lower ≤ ‖DirichletCharacter.LFunction χ 1‖) :
    lower / M ≤ 1 - β := by
  apply (div_le_iff₀ hM).2
  simpa only [mul_comm] using hLone.trans
    (norm_LFunction_one_le_gap_mul_of_deriv_bound χ hχ hβ hzero hderiv)

/-- The power-shaped specialization expected from Siegel's theorem.  The
ineffective lower bound itself remains an analytic input; once supplied, this
theorem performs the full deterministic conversion to a zero gap. -/
theorem zero_gap_lower_of_siegel_power_bound
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {β M c ε : ℝ} (hβ : β ≤ 1) (hM : 0 < M)
    (hzero : DirichletCharacter.LFunction χ β = 0)
    (hderiv : ∀ x ∈ Set.Ico β 1,
      ‖deriv (DirichletCharacter.LFunction χ) x‖ ≤ M)
    (hSiegel : c * (q : ℝ) ^ (-ε) ≤
      ‖DirichletCharacter.LFunction χ 1‖) :
    (c * (q : ℝ) ^ (-ε)) / M ≤ 1 - β :=
  zero_gap_lower_of_LFunction_one_lower_bound
    χ hχ hβ hM hzero hderiv hSiegel

/-- Once the published Siegel input is supplied, the remaining conversion to
an exceptional-zero gap is completely deterministic. -/
theorem PublishedSiegelLValueLowerBound.exists_zero_gap_lower_bound
    (hSiegel : PublishedSiegelLValueLowerBound)
    {ε : ℝ} (hε : 0 < ε)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (hreal : χ ^ 2 = 1)
    {β M : ℝ} (hβ : β ≤ 1) (hM : 0 < M)
    (hzero : DirichletCharacter.LFunction χ β = 0)
    (hderiv : ∀ x ∈ Set.Ico β 1,
      ‖deriv (DirichletCharacter.LFunction χ) x‖ ≤ M) :
    ∃ c : ℝ, 0 < c ∧ (c * (q : ℝ) ^ (-ε)) / M ≤ 1 - β := by
  rcases hSiegel.specialize hε χ hprim hχ hreal with ⟨c, hc, hLone⟩
  exact ⟨c, hc, zero_gap_lower_of_siegel_power_bound
    χ hχ hβ hM hzero hderiv hLone⟩

end
end MAPZeroFreeSiegelSpine
