import RamachandraEulerExpEnvelope
import ZeroDeterminantSectorClosure
import RamanujanWindowAbsorption
import FixedCharacterPoweredBridge
import BHPAllCharacterDyadicBudget

/-!
# Exact divisor-square energy for Ramachandra's shifted blocks

Ramachandra's proofs of Lemmas 4--6 use
`sum_{n <= X} d(n)^2/n << log(X)^4`.  This file proves the finite inequality
needed by the Lean dyadic mean-square engine.  It does not assume any moment
bound or contour estimate.
-/

namespace RamachandraShiftedCoefficientEnergy

open scoped BigOperators
open scoped ArithmeticFunction.zeta
open ArithmeticFunction
open CGLProofDAG MixedMellinCert
open MAPMixedMeanZeroClose MAPRamanujanWindowAbsorption
open FixedCharacterPoweredBridge
open MontgomeryVaughanFiniteReduction

noncomputable section

/-- Exact harmonic majorant for the rational divisor weight already proved in
the zero-determinant sector, transported to real scalars. -/
theorem sum_tauAF_div_cast_le_harmonic_pow (r X : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X, (tauAF r n : ℝ) / (n : ℝ)) ≤
      (harmonic X : ℝ) ^ r := by
  have hq := weightedTauSum_le_harmonic_pow r X
  have hq' :
      (∑ n ∈ Finset.Ioc 0 X, (tauAF r n : ℚ) / (n : ℚ)) ≤
        (harmonic X : ℚ) ^ r := by
    rw [show (∑ n ∈ Finset.Ioc 0 X,
        (tauAF r n : ℚ) / (n : ℚ)) = weightedTauSum r X by
      unfold weightedTauSum
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : n ≠ 0 := by
        simp only [Finset.mem_Ioc] at hn
        omega
      simp [reciprocalTwist, tauRat, hn0]]
    exact hq
  calc
    (∑ n ∈ Finset.Ioc 0 X,
        (tauAF r n : ℝ) / (n : ℝ)) =
        (((∑ n ∈ Finset.Ioc 0 X,
          (tauAF r n : ℚ) / (n : ℚ)) : ℚ) : ℝ) := by
      push_cast
      rfl
    _ ≤ (((harmonic X : ℚ) ^ r : ℚ) : ℝ) := by exact_mod_cast hq'
    _ = (harmonic X : ℝ) ^ r := by norm_cast

/-- The exact finite form of Ramachandra's printed
`sum d(n)^2/n << log(X)^4`, with harmonic number in place of the asymptotic
logarithm. -/
theorem sum_orderedDivisorCount_two_sq_div_le (X : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X,
      (orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) ≤
      (harmonic X : ℝ) ^ 4 := by
  calc
    (∑ n ∈ Finset.Ioc 0 X,
      (orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) ≤
        ∑ n ∈ Finset.Ioc 0 X, (tauAF 4 n : ℝ) / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Ioc.mp hn).1
      apply div_le_div_of_nonneg_right _
        (by positivity : (0 : ℝ) ≤ (n : ℝ))
      exact_mod_cast ShiuAnalyticLayer.tauAF_square_le_tauAF_mul 2 n
    _ ≤ (harmonic X : ℝ) ^ 4 :=
      sum_tauAF_div_cast_le_harmonic_pow 4 X

/-- At order two the convolution coefficient is the ordinary divisor count. -/
theorem orderedDivisorCount_two_eq_card_divisors
    {n : ℕ} (hn : n ≠ 0) :
    orderedDivisorCount 2 n = n.divisors.card := by
  rw [FixedCharacterPoweredBridge.orderedDivisorCount_eq_tauAF]
  rw [show 2 = 1 + 1 by omega, MixedMellinCert.tauAF_succ_apply]
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hd0 : d ≠ 0 := fun h => hn (by simpa [h] using hdvd)
  simp [MixedMellinCert.tauAF, ArithmeticFunction.zeta_apply, hd0]

/-- Elementary polynomial envelope used for the exponentially small direct
tail. -/
theorem orderedDivisorCount_two_le_self {n : ℕ} (hn : 0 < n) :
    orderedDivisorCount 2 n ≤ n := by
  rw [orderedDivisorCount_two_eq_card_divisors (Nat.ne_of_gt hn)]
  exact Nat.card_divisors_le_self n

/-- A dyadic interval `(N,2N]` is contained in the initial interval
`(0,2N]`. -/
theorem dyadicSupport_subset_Ioc_zero_two_mul (N : ℕ) :
    dyadicSupport N ⊆ Finset.Ioc 0 (2 * N) := by
  intro n hn
  have h := Finset.mem_Ioc.mp hn
  exact Finset.mem_Ioc.mpr ⟨Nat.zero_lt_of_lt h.1, h.2⟩

/-- Divisor-square energy on one dyadic block. -/
theorem sum_dyadic_orderedDivisorCount_two_sq_div_le (N : ℕ) :
    (∑ n ∈ dyadicSupport N,
      (orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) ≤
      (harmonic (2 * N) : ℝ) ^ 4 := by
  calc
    (∑ n ∈ dyadicSupport N,
      (orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) ≤
        ∑ n ∈ Finset.Ioc 0 (2 * N),
          (orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (dyadicSupport_subset_Ioc_zero_two_mul N)
      intro n hn hnot
      positivity
    _ ≤ (harmonic (2 * N) : ℝ) ^ 4 :=
      sum_orderedDivisorCount_two_sq_div_le (2 * N)

/-- Any coefficient array dominated pointwise by `K d(n)^2/n` has the
corresponding exact dyadic energy bound.  This is the reusable endpoint for
all three shifted contour pieces after their literal coefficient envelopes
are established. -/
theorem coefficientEnergy_le_mul_harmonic_four
    (b : ℕ → ℂ) (N : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ n ∈ dyadicSupport N,
      ‖b n‖ ^ 2 ≤ K *
        ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ))) :
    coefficientEnergy b N ≤ K * (harmonic (2 * N) : ℝ) ^ 4 := by
  unfold coefficientEnergy
  calc
    (∑ n ∈ dyadicSupport N, ‖b n‖ ^ 2) ≤
        ∑ n ∈ dyadicSupport N,
          K * ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
      exact Finset.sum_le_sum fun n hn => hb n hn
    _ = K * ∑ n ∈ dyadicSupport N,
          ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ K * (harmonic (2 * N) : ℝ) ^ 4 := by
      exact mul_le_mul_of_nonneg_left
        (sum_dyadic_orderedDivisorCount_two_sq_div_le N) hK

/-! ## The actual shifted direct-series coefficients -/

/-- Removing the oscillatory character and `n^(-it)` from Ramachandra's
direct series leaves this real nonnegative coefficient. -/
def shiftedDivisorBlockCoeff (sigma : ℝ) (n : ℕ) : ℂ :=
  (orderedDivisorCount 2 n : ℂ) *
    (((n : ℝ) ^ (-sigma) : ℝ) : ℂ)

/-- The literal exponentially smoothed coefficient in `S(s)`. -/
def shiftedSmoothedDivisorBlockCoeff (sigma X : ℝ) (n : ℕ) : ℂ :=
  shiftedDivisorBlockCoeff sigma n *
    (Real.exp (-((n : ℝ) / X)) : ℂ)

theorem norm_shiftedSmoothedDivisorBlockCoeff_one_le
    {sigma X : ℝ} (hX : 0 < X) :
    ‖shiftedSmoothedDivisorBlockCoeff sigma X 1‖ ≤ 1 := by
  unfold shiftedSmoothedDivisorBlockCoeff shiftedDivisorBlockCoeff
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-(1 / X)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (div_nonneg (by norm_num) hX.le)
  convert hexp using 1 <;>
    simp [orderedDivisorCount, pow_two, ArithmeticFunction.mul_apply]

/-- A shift of size `delta` from `1/2` costs at most
`exp(2 delta log Y)` on coefficients supported in `[1,Y]`. -/
theorem rpow_neg_two_sigma_le_exp_mul_div_of_lower
    {n Y sigma delta : ℝ}
    (hn : 1 ≤ n) (hnY : n ≤ Y) (hdelta : 0 ≤ delta)
    (hsigmaLow : 1 / 2 - delta ≤ sigma) :
    n ^ (-2 * sigma) ≤ Real.exp (2 * delta * Real.log Y) / n := by
  have hnpos : 0 < n := zero_lt_one.trans_le hn
  have hYpos : 0 < Y := hnpos.trans_le hnY
  have hexp : -2 * sigma ≤ -1 + 2 * delta := by linarith
  have h1 := Real.rpow_le_rpow_of_exponent_le hn hexp
  have hsplit : n ^ (-1 + 2 * delta) =
      n⁻¹ * n ^ (2 * delta) := by
    rw [Real.rpow_add hnpos, Real.rpow_neg_one]
  have hbase : n ^ (2 * delta) ≤ Y ^ (2 * delta) :=
    Real.rpow_le_rpow hnpos.le hnY (by positivity)
  have hYexp : Y ^ (2 * delta) =
      Real.exp (2 * delta * Real.log Y) := by
    rw [Real.rpow_def_of_pos hYpos]
    congr 1
    ring
  calc
    n ^ (-2 * sigma) ≤ n ^ (-1 + 2 * delta) := h1
    _ = n⁻¹ * n ^ (2 * delta) := hsplit
    _ ≤ n⁻¹ * Y ^ (2 * delta) := by
      exact mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hnpos.le)
    _ = Real.exp (2 * delta * Real.log Y) / n := by
      rw [hYexp]
      field_simp

theorem rpow_neg_two_sigma_le_exp_mul_div
    {n Y sigma delta : ℝ}
    (hn : 1 ≤ n) (hnY : n ≤ Y) (hdelta : 0 ≤ delta)
    (hsigma : |sigma - 1 / 2| ≤ delta) :
    n ^ (-2 * sigma) ≤ Real.exp (2 * delta * Real.log Y) / n :=
  rpow_neg_two_sigma_le_exp_mul_div_of_lower hn hnY hdelta
    (by
      have h := (abs_le.mp hsigma).1
      linarith)

theorem norm_shiftedDivisorBlockCoeff_sq
    {sigma : ℝ} {n : ℕ} (hn : 0 < n) :
    ‖shiftedDivisorBlockCoeff sigma n‖ ^ 2 =
      (orderedDivisorCount 2 n : ℝ) ^ 2 *
        (n : ℝ) ^ (-2 * sigma) := by
  have hnR : 0 ≤ (n : ℝ) := by positivity
  have hrpow : 0 ≤ (n : ℝ) ^ (-sigma) :=
    Real.rpow_nonneg hnR _
  unfold shiftedDivisorBlockCoeff
  rw [norm_mul]
  simp only [Complex.norm_natCast, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_nonneg hrpow, mul_pow]
  have hpow : ((n : ℝ) ^ (-sigma)) ^ (2 : ℕ) =
      (n : ℝ) ^ (-2 * sigma) := by
    calc
      ((n : ℝ) ^ (-sigma)) ^ (2 : ℕ) =
          (n : ℝ) ^ ((-sigma) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast hnR (-sigma) 2).symm
      _ = (n : ℝ) ^ (-2 * sigma) := by ring_nf
  rw [hpow]

theorem norm_shiftedDivisorBlockCoeff_sq_le
    {n : ℕ} {Y sigma delta : ℝ}
    (hn : 1 ≤ n) (hnY : (n : ℝ) ≤ Y) (hdelta : 0 ≤ delta)
    (hsigma : |sigma - 1 / 2| ≤ delta) :
    ‖shiftedDivisorBlockCoeff sigma n‖ ^ 2 ≤
      Real.exp (2 * delta * Real.log Y) *
        ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
  rw [norm_shiftedDivisorBlockCoeff_sq (by omega)]
  have hp := rpow_neg_two_sigma_le_exp_mul_div
    (show (1 : ℝ) ≤ n by exact_mod_cast hn) hnY hdelta hsigma
  have hdnonneg : 0 ≤ (orderedDivisorCount 2 n : ℝ) ^ 2 :=
    sq_nonneg _
  calc
    (orderedDivisorCount 2 n : ℝ) ^ 2 *
        (n : ℝ) ^ (-2 * sigma) ≤
        (orderedDivisorCount 2 n : ℝ) ^ 2 *
          (Real.exp (2 * delta * Real.log Y) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hp hdnonneg
    _ = Real.exp (2 * delta * Real.log Y) *
        ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by ring

theorem norm_shiftedDivisorBlockCoeff_sq_le_of_lower
    {n : ℕ} {Y sigma delta : ℝ}
    (hn : 1 ≤ n) (hnY : (n : ℝ) ≤ Y) (hdelta : 0 ≤ delta)
    (hsigmaLow : 1 / 2 - delta ≤ sigma) :
    ‖shiftedDivisorBlockCoeff sigma n‖ ^ 2 ≤
      Real.exp (2 * delta * Real.log Y) *
        ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
  rw [norm_shiftedDivisorBlockCoeff_sq (by omega)]
  have hp := rpow_neg_two_sigma_le_exp_mul_div_of_lower
    (show (1 : ℝ) ≤ n by exact_mod_cast hn) hnY hdelta hsigmaLow
  have hdnonneg : 0 ≤ (orderedDivisorCount 2 n : ℝ) ^ 2 :=
    sq_nonneg _
  calc
    (orderedDivisorCount 2 n : ℝ) ^ 2 *
        (n : ℝ) ^ (-2 * sigma) ≤
        (orderedDivisorCount 2 n : ℝ) ^ 2 *
          (Real.exp (2 * delta * Real.log Y) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hp hdnonneg
    _ = Real.exp (2 * delta * Real.log Y) *
        ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by ring

/-- Exponential smoothing can only reduce the coefficient norm. -/
theorem norm_shiftedSmoothedDivisorBlockCoeff_sq_le
    {sigma X : ℝ} {n : ℕ} (hX : 0 < X) :
    ‖shiftedSmoothedDivisorBlockCoeff sigma X n‖ ^ 2 ≤
      ‖shiftedDivisorBlockCoeff sigma n‖ ^ 2 := by
  have hexppos : 0 < Real.exp (-((n : ℝ) / X)) := Real.exp_pos _
  have hexple : Real.exp (-((n : ℝ) / X)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (div_nonneg (by positivity) hX.le)
  have hsquare : Real.exp (-((n : ℝ) / X)) ^ 2 ≤ 1 := by
    nlinarith
  unfold shiftedSmoothedDivisorBlockCoeff
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hexppos, mul_pow]
  nlinarith [sq_nonneg ‖shiftedDivisorBlockCoeff sigma n‖]

theorem norm_shiftedSmoothedDivisorBlockCoeff_sq_le_envelope
    {n : ℕ} {X Y sigma delta : ℝ}
    (hX : 0 < X) (hn : 1 ≤ n) (hnY : (n : ℝ) ≤ Y)
    (hdelta : 0 ≤ delta)
    (hsigma : |sigma - 1 / 2| ≤ delta) :
    ‖shiftedSmoothedDivisorBlockCoeff sigma X n‖ ^ 2 ≤
      Real.exp (2 * delta * Real.log Y) *
        ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) :=
  (norm_shiftedSmoothedDivisorBlockCoeff_sq_le hX).trans
    (norm_shiftedDivisorBlockCoeff_sq_le hn hnY hdelta hsigma)

/-- Energy for an unsmoothed shifted divisor block under only the lower
strip bound.  This is the form needed on both reflected contour lines. -/
theorem coefficientEnergy_shiftedDivisorBlockCoeff_le_of_lower
    (N : ℕ) {Y sigma delta : ℝ}
    (hNY : (2 * N : ℕ) ≤ Y) (hdelta : 0 ≤ delta)
    (hsigmaLow : 1 / 2 - delta ≤ sigma) :
    coefficientEnergy (shiftedDivisorBlockCoeff sigma) N ≤
      Real.exp (2 * delta * Real.log Y) *
        (harmonic (2 * N) : ℝ) ^ 4 := by
  apply coefficientEnergy_le_mul_harmonic_four _ _
    (Real.exp_nonneg _)
  intro n hn
  have hnpos : 0 < n :=
    Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
  apply norm_shiftedDivisorBlockCoeff_sq_le_of_lower
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hnpos)) _ hdelta hsigmaLow
  have hnle : (n : ℝ) ≤ (2 * N : ℕ) := by
    exact_mod_cast (Finset.mem_Ioc.mp hn).2
  exact hnle.trans hNY

/-- Exact energy of a literal shifted `S(s)` dyadic block. -/
theorem coefficientEnergy_shiftedSmoothedDivisorBlockCoeff_le
    (N : ℕ) {X Y sigma delta : ℝ}
    (hX : 0 < X) (hNY : (2 * N : ℕ) ≤ Y)
    (hdelta : 0 ≤ delta)
    (hsigma : |sigma - 1 / 2| ≤ delta) :
    coefficientEnergy (shiftedSmoothedDivisorBlockCoeff sigma X) N ≤
      Real.exp (2 * delta * Real.log Y) *
        (harmonic (2 * N) : ℝ) ^ 4 := by
  apply coefficientEnergy_le_mul_harmonic_four _ _
    (Real.exp_nonneg _)
  intro n hn
  have hnIoc := Finset.mem_Ioc.mp hn
  apply norm_shiftedSmoothedDivisorBlockCoeff_sq_le_envelope hX
    (by omega) _ hdelta hsigma
  have hnle : (n : ℝ) ≤ (2 * N : ℕ) := by
    exact_mod_cast hnIoc.2
  exact hnle.trans hNY

end
end RamachandraShiftedCoefficientEnergy

#print axioms RamachandraShiftedCoefficientEnergy.sum_orderedDivisorCount_two_sq_div_le
#print axioms RamachandraShiftedCoefficientEnergy.coefficientEnergy_le_mul_harmonic_four
#print axioms RamachandraShiftedCoefficientEnergy.coefficientEnergy_shiftedSmoothedDivisorBlockCoeff_le
