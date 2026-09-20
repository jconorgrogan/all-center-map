import MontgomeryDetectorCharacterFactorization
import PostA5TypeIFourierAssembly
import RamachandraShiftedCoefficientEnergy

/-!
# Exact energy of one Montgomery detector shell

The fail-fast hybrid dichotomy needs the literal `ℓ²` energy of the common
detector coefficient.  The source coefficient is bounded by

`n^(-sigma) d₂(n)`.

On `(D,2D]` and `sigma >= 1/2`, its square is at most

`D^(1-2 sigma) d₂(n)^2/n`.

Thus the already certified divisor-square harmonic estimate gives the exact
finite energy bound below.  No pointwise `n^epsilon` estimate is used.
-/

namespace MAPMontgomeryDetectorEnergy

open scoped BigOperators
open CGLProofDAG MontgomeryVaughanFiniteReduction
open MAPMollifierCoefficientIdentity MAPAppendixA4PostA5SetAdapter
open MAPMontgomeryDetectorCharacterFactorization
open RamachandraShiftedCoefficientEnergy

noncomputable section

/-- Character-free version of the source-faithful detector coefficient
majorant. -/
theorem norm_untwistedDetectorCommonCoefficient_le
    (U N : ℕ) {Y : ℝ} (hY : 0 < Y) (sigma : ℝ)
    {n : ℕ} (hn : 0 < n) :
    ‖untwistedDetectorCommonCoefficient U N Y sigma n‖ ≤
      Real.rpow n (-sigma) * orderedDivisorCount 2 n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hmoll := norm_mollifierCoeff_le_orderedDivisorCount_two U hn0
  have hexp : Real.exp (-((n : ℝ) / Y)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (n : ℝ) / Y := by positivity
    linarith
  have hrpow0 : 0 ≤ Real.rpow (n : ℝ) (-sigma) :=
    Real.rpow_nonneg (by positivity) _
  unfold untwistedDetectorCommonCoefficient
  split_ifs with hsupp
  · rw [norm_mul, norm_mul]
    simp only [Real.norm_eq_abs, Complex.norm_real,
      abs_of_nonneg (Real.exp_pos _).le]
    rw [abs_of_nonneg hrpow0]
    calc
      Real.rpow n (-sigma) *
          (Real.exp (-((n : ℝ) / Y)) * ‖mollifierCoeff U n‖) ≤
        Real.rpow n (-sigma) *
          (1 * orderedDivisorCount 2 n) := by
            gcongr
      _ = Real.rpow n (-sigma) * orderedDivisorCount 2 n := by ring
  · rw [mul_zero, norm_zero]
    exact mul_nonneg hrpow0 (Nat.cast_nonneg _)

/-- Exact pointwise square envelope on a dyadic shell. -/
theorem norm_untwistedDetectorCommonCoefficient_sq_le
    (U N D : ℕ) {Y sigma : ℝ} (hY : 0 < Y)
    (hD : 1 ≤ D) (hsigma : 1 / 2 ≤ sigma)
    {n : ℕ} (hn : n ∈ dyadicSupport D) :
    ‖untwistedDetectorCommonCoefficient U N Y sigma n‖ ^ 2 ≤
      Real.rpow D (1 - 2 * sigma) *
        ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
  have hnBounds := Finset.mem_Ioc.mp hn
  have hnPos : 0 < n := Nat.zero_lt_of_lt hnBounds.1
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hDn : (D : ℝ) ≤ n := by exact_mod_cast hnBounds.1.le
  have hexp : 1 - 2 * sigma ≤ 0 := by linarith
  have hpow : Real.rpow n (1 - 2 * sigma) ≤
      Real.rpow D (1 - 2 * sigma) :=
    Real.rpow_le_rpow_of_nonpos hDpos hDn hexp
  have hpoint := norm_untwistedDetectorCommonCoefficient_le
    U N hY sigma hnPos
  have hsq :
      ‖untwistedDetectorCommonCoefficient U N Y sigma n‖ ^ 2 ≤
        (Real.rpow n (-sigma) * orderedDivisorCount 2 n) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hpoint 2
  have hrpowIdentity :
      (Real.rpow n (-sigma)) ^ 2 =
        Real.rpow n (1 - 2 * sigma) / (n : ℝ) := by
    calc
      (Real.rpow n (-sigma)) ^ 2 =
          Real.rpow n ((-sigma) * 2) := by
        rw [← Real.rpow_natCast (Real.rpow n (-sigma)) 2]
        exact (Real.rpow_mul hnpos.le (-sigma) 2).symm
      _ = Real.rpow n ((1 - 2 * sigma) + (-1)) := by ring_nf
      _ = Real.rpow n (1 - 2 * sigma) * Real.rpow n (-1) :=
        Real.rpow_add hnpos _ _
      _ = Real.rpow n (1 - 2 * sigma) / (n : ℝ) := by
        have hneg : Real.rpow (n : ℝ) (-1 : ℝ) = (n : ℝ)⁻¹ :=
          Real.rpow_neg_one _
        rw [hneg, div_eq_mul_inv]
  calc
    ‖untwistedDetectorCommonCoefficient U N Y sigma n‖ ^ 2 ≤
        (Real.rpow n (-sigma) * orderedDivisorCount 2 n) ^ 2 := hsq
    _ = Real.rpow n (1 - 2 * sigma) *
        ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
      rw [mul_pow, hrpowIdentity]
      ring
    _ ≤ Real.rpow D (1 - 2 * sigma) *
        ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hpow (by positivity)

/-- Literal detector-shell energy at the exact harmonic fourth-power cost. -/
theorem detectorCommonCoefficientEnergy_le
    (U N D : ℕ) {Y sigma : ℝ} (hY : 0 < Y)
    (hD : 1 ≤ D) (hsigma : 1 / 2 ≤ sigma) :
    coefficientEnergy
        (untwistedDetectorCommonCoefficient U N Y sigma) D ≤
      Real.rpow D (1 - 2 * sigma) *
        (harmonic (2 * D) : ℝ) ^ 4 := by
  apply coefficientEnergy_le_mul_harmonic_four
  · exact Real.rpow_nonneg (by positivity) _
  · intro n hn
    exact norm_untwistedDetectorCommonCoefficient_sq_le
      U N D hY hD hsigma hn

end

end MAPMontgomeryDetectorEnergy

#print axioms MAPMontgomeryDetectorEnergy.norm_untwistedDetectorCommonCoefficient_le
#print axioms MAPMontgomeryDetectorEnergy.norm_untwistedDetectorCommonCoefficient_sq_le
#print axioms MAPMontgomeryDetectorEnergy.detectorCommonCoefficientEnergy_le
