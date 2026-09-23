import RamachandraShiftedDirectSeries

/-!
# Literal shifted reflected-series blocks

This module identifies every term in the reflected series occurring in
Ramachandra's `I₁` and `I₂` contours with the dual dyadic block used by the
certified all-character mean square.  The inverse character is converted to
complex conjugation by the exact `MulChar.star_eq_inv` identity.
-/

namespace RamachandraShiftedReflectedSeries

open scoped BigOperators LSeries.notation ComplexConjugate
open Complex
open CGLProofDAG
open BHPRamachandraMeanValueFromDyadicAFE
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedCoefficientEnergy
open MAPMRTLemma210OrthogonalityReduction
open MontgomeryVaughanFiniteReduction
open BHPAllCharacterDyadicBudget

noncomputable section

/-- Coefficient left after extracting the inverse character and the
`exp(+it log n)` phase.  The Mellin ordinate `v` remains in the coefficient,
as required by the continuous-Mellin reduction. -/
def shiftedReflectedBlockCoeff (sigma u v : ℝ) (n : ℕ) : ℂ :=
  shiftedDivisorBlockCoeff (1 - sigma - u) n *
    twistedPhase n (-v)

/-- Exact reflected term identity at `z=sigma+it+u+iv`. -/
theorem reflectedTerm_eq_blockTerm
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {n : ℕ} (hn : 0 < n) (sigma u t v : ℝ) :
    ramachandraReflectedTerm psi
        (ramachandraShiftedPoint sigma t + ((u : ℂ) + v * I)) n =
      (shiftedReflectedBlockCoeff sigma u v n * star psi n) *
        twistedPhase n (-t) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold ramachandraReflectedTerm ramachandraDivisorCoeff
    ramachandraShiftedPoint shiftedReflectedBlockCoeff
    shiftedDivisorBlockCoeff twistedPhase
  rw [LSeries.term_of_ne_zero hn0]
  rw [Complex.cpow_def_of_ne_zero hnC]
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) :=
    (Complex.ofReal_log hnR.le).symm
  rw [hlog, Real.rpow_def_of_pos hnR]
  rw [div_eq_mul_inv, ← Complex.exp_neg]
  have hrpowExp :
      ((Real.exp (Real.log (n : ℝ) * -(1 - sigma - u)) : ℝ) : ℂ) =
        Complex.exp
          ((Real.log (n : ℝ) * -(1 - sigma - u) : ℝ) : ℂ) :=
    Complex.ofReal_exp _
  rw [hrpowExp]
  have hsplit :
      Complex.exp
          (-((Real.log (n : ℝ) : ℂ) *
            (1 - ((sigma : ℂ) + (t : ℂ) * I +
              ((u : ℂ) + (v : ℂ) * I))))) =
        Complex.exp
            ((Real.log (n : ℝ) * -(1 - sigma - u) : ℝ) : ℂ) *
          Complex.exp (((v * Real.log (n : ℝ)) : ℝ) * I) *
          Complex.exp (((t * Real.log (n : ℝ)) : ℝ) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hsplit, ← MulChar.star_eq_inv psi]
  ring

/-- The Mellin phase has unit norm, so reflected coefficient energy is exactly
the unphased shifted divisor energy. -/
theorem norm_shiftedReflectedBlockCoeff_sq
    (sigma u v : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖shiftedReflectedBlockCoeff sigma u v n‖ ^ 2 =
      ‖shiftedDivisorBlockCoeff (1 - sigma - u) n‖ ^ 2 := by
  unfold shiftedReflectedBlockCoeff
  rw [norm_mul, norm_twistedPhase, mul_one]

/-- Exact dyadic energy envelope for a reflected block. -/
theorem coefficientEnergy_shiftedReflectedBlockCoeff_le
    (N : ℕ) {Y sigma u delta : ℝ}
    (hNY : (2 * N : ℕ) ≤ Y) (hdelta : 0 ≤ delta)
    (hline : |(1 - sigma - u) - 1 / 2| ≤ delta)
    (v : ℝ) :
    coefficientEnergy (shiftedReflectedBlockCoeff sigma u v) N ≤
      Real.exp (2 * delta * Real.log Y) *
        (harmonic (2 * N) : ℝ) ^ 4 := by
  apply coefficientEnergy_le_mul_harmonic_four _ _
    (Real.exp_nonneg _)
  intro n hn
  have hnpos : 0 < n :=
    Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
  rw [norm_shiftedReflectedBlockCoeff_sq sigma u v hnpos]
  apply norm_shiftedDivisorBlockCoeff_sq_le
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hnpos)) _ hdelta hline
  have hnle : (n : ℝ) ≤ (2 * N : ℕ) := by
    exact_mod_cast (Finset.mem_Ioc.mp hn).2
  exact hnle.trans hNY

/-- Reflected energy under the single lower bound actually used by the
coefficient calculation. -/
theorem coefficientEnergy_shiftedReflectedBlockCoeff_le_of_lower
    (N : ℕ) {Y sigma u delta : ℝ}
    (hNY : (2 * N : ℕ) ≤ Y) (hdelta : 0 ≤ delta)
    (hlineLow : 1 / 2 - delta ≤ 1 - sigma - u)
    (v : ℝ) :
    coefficientEnergy (shiftedReflectedBlockCoeff sigma u v) N ≤
      Real.exp (2 * delta * Real.log Y) *
        (harmonic (2 * N) : ℝ) ^ 4 := by
  apply coefficientEnergy_le_mul_harmonic_four _ _
    (Real.exp_nonneg _)
  intro n hn
  have hnpos : 0 < n :=
    Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
  rw [norm_shiftedReflectedBlockCoeff_sq sigma u v hnpos]
  apply norm_shiftedDivisorBlockCoeff_sq_le_of_lower
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hnpos)) _ hdelta hlineLow
  have hnle : (n : ℝ) ≤ (2 * N : ℕ) := by
    exact_mod_cast (Finset.mem_Ioc.mp hn).2
  exact hnle.trans hNY

/-- On the long line `u=-(sigma+1/4)`, the reflected Dirichlet series has
real exponent exactly `5/4`, hence no shifted-strip energy loss at all. -/
theorem coefficientEnergy_longReflectedBlockCoeff_le
    (N : ℕ) {Y sigma : ℝ} (hNY : (2 * N : ℕ) ≤ Y) (v : ℝ) :
    coefficientEnergy
        (shiftedReflectedBlockCoeff sigma (-(sigma + 1 / 4)) v) N ≤
      (harmonic (2 * N) : ℝ) ^ 4 := by
  have h := coefficientEnergy_shiftedReflectedBlockCoeff_le_of_lower
    N hNY (show (0 : ℝ) ≤ 0 by norm_num)
      (show (1 / 2 : ℝ) - 0 ≤
          1 - sigma - (-(sigma + 1 / 4)) by linarith) v
  simpa using h

/-- Sharp energy retained on the literal long line `Re(s+w)=-1/4`.
The reflected exponent is `5/4`, so the square contributes `n⁻⁵ᐟ²`; on a
dyadic block this is `N⁻³ᐟ²` times the divisor-energy weight `1/n`. -/
theorem coefficientEnergy_quarterLineReflectedBlockCoeff_le
    (N : ℕ) (hN : 1 ≤ N) (sigma v : ℝ) :
    coefficientEnergy
        (shiftedReflectedBlockCoeff sigma (-(sigma + 1 / 4)) v) N ≤
      Real.rpow (N : ℝ) (-(3 / 2 : ℝ)) *
        (harmonic (2 * N) : ℝ) ^ 4 := by
  apply coefficientEnergy_le_mul_harmonic_four _ _
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  intro n hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
  have hnN : N < n := (Finset.mem_Ioc.mp hn).1
  rw [norm_shiftedReflectedBlockCoeff_sq sigma (-(sigma + 1 / 4)) v hnpos]
  rw [norm_shiftedDivisorBlockCoeff_sq hnpos]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hnN.le
  have hbase : Real.rpow (n : ℝ) (-(3 / 2 : ℝ)) ≤
      Real.rpow (N : ℝ) (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hNR hNn (by norm_num)
  have hpow : (n : ℝ) ^
        (-2 * (1 - sigma - (-(sigma + 1 / 4)))) ≤
      Real.rpow (N : ℝ) (-(3 / 2 : ℝ)) / (n : ℝ) := by
    have hexp : -2 * (1 - sigma - (-(sigma + 1 / 4))) =
        (-(3 / 2 : ℝ)) + (-1 : ℝ) := by ring
    calc
      (n : ℝ) ^ (-2 * (1 - sigma - (-(sigma + 1 / 4)))) =
          Real.rpow (n : ℝ) (-(3 / 2 : ℝ)) *
            Real.rpow (n : ℝ) (-1 : ℝ) := by
              rw [hexp]
              exact Real.rpow_add hnR _ _
      _ = Real.rpow (n : ℝ) (-(3 / 2 : ℝ)) / (n : ℝ) := by
            have hnegone : Real.rpow (n : ℝ) (-1 : ℝ) = (n : ℝ)⁻¹ := by
              exact Real.rpow_neg_one (n : ℝ)
            rw [hnegone]
            ring
      _ ≤ Real.rpow (N : ℝ) (-(3 / 2 : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hbase hnR.le
  have hdiv0 : 0 ≤ (orderedDivisorCount 2 n : ℝ) ^ 2 := sq_nonneg _
  calc
    (orderedDivisorCount 2 n : ℝ) ^ 2 *
        (n : ℝ) ^ (-2 * (1 - sigma - (-(sigma + 1 / 4)))) ≤
      (orderedDivisorCount 2 n : ℝ) ^ 2 *
        (Real.rpow (N : ℝ) (-(3 / 2 : ℝ)) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow hdiv0
    _ = Real.rpow (N : ℝ) (-(3 / 2 : ℝ)) *
        ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by ring

/-- Sharp energy on the rational workaround line `Re z=-1/2`.  Here the
reflected Dirichlet exponent is exactly `3/2`; retaining its two extra powers
gives the `N⁻²` saving that cancels the conductor-height factor in the long
contour moment. -/
theorem coefficientEnergy_negHalfReflectedBlockCoeff_le
    (N : ℕ) (hN : 1 ≤ N) (sigma v : ℝ) :
    coefficientEnergy
        (shiftedReflectedBlockCoeff sigma (-(sigma + 1 / 2)) v) N ≤
      ((N : ℝ)⁻¹ ^ 2) * (harmonic (2 * N) : ℝ) ^ 4 := by
  apply coefficientEnergy_le_mul_harmonic_four _ _ (by positivity)
  intro n hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
  have hnN : N < n := (Finset.mem_Ioc.mp hn).1
  rw [norm_shiftedReflectedBlockCoeff_sq sigma (-(sigma + 1 / 2)) v hnpos]
  rw [norm_shiftedDivisorBlockCoeff_sq hnpos]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hnN.le
  have hsquare : (N : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by gcongr
  have hpow : (n : ℝ) ^ (-2 * (1 - sigma - (-(sigma + 1 / 2)))) ≤
      ((N : ℝ)⁻¹ ^ 2) / (n : ℝ) := by
    have hexp : -2 * (1 - sigma - (-(sigma + 1 / 2))) = (-3 : ℝ) := by ring
    have hinvSq : (((n : ℝ) ^ 2)⁻¹) ≤ (((N : ℝ) ^ 2)⁻¹) :=
      (inv_le_inv₀ (sq_pos_of_pos hnR) (sq_pos_of_pos hNR)).2 hsquare
    have hleft : (((n : ℝ) ^ 3)⁻¹) =
        (((n : ℝ) ^ 2)⁻¹) / (n : ℝ) := by
      field_simp
    have hright : (((N : ℝ)⁻¹) ^ 2) / (n : ℝ) =
        (((N : ℝ) ^ 2)⁻¹) / (n : ℝ) := by
      rw [inv_pow]
    calc
      (n : ℝ) ^ (-2 * (1 - sigma - (-(sigma + 1 / 2)))) =
          (((n : ℝ) ^ 3)⁻¹) := by
            rw [hexp, show (-3 : ℝ) = -(3 : ℝ) by norm_num,
              Real.rpow_neg (le_of_lt hnR)]
            congr 1
            exact Real.rpow_natCast (n : ℝ) 3
      _ = (((n : ℝ) ^ 2)⁻¹) / (n : ℝ) := hleft
      _ ≤ (((N : ℝ) ^ 2)⁻¹) / (n : ℝ) :=
        div_le_div_of_nonneg_right hinvSq hnR.le
      _ = (((N : ℝ)⁻¹) ^ 2) / (n : ℝ) := hright.symm
  have hdiv0 : 0 ≤ (orderedDivisorCount 2 n : ℝ) ^ 2 := sq_nonneg _
  calc
    (orderedDivisorCount 2 n : ℝ) ^ 2 *
        (n : ℝ) ^ (-2 * (1 - sigma - (-(sigma + 1 / 2)))) ≤
      (orderedDivisorCount 2 n : ℝ) ^ 2 *
        (((N : ℝ)⁻¹ ^ 2) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow hdiv0
    _ = ((N : ℝ)⁻¹ ^ 2) *
        ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by ring

/-- Sharp energy on the short-contour workaround line `Re(s+w)=0`.  The
reflected Dirichlet exponent is exactly `1`; one retained inverse power gives
the `N⁻¹` dyadic saving required by the source head decomposition. -/
theorem coefficientEnergy_zeroLineReflectedBlockCoeff_le
    (N : ℕ) (hN : 1 ≤ N) (sigma v : ℝ) :
    coefficientEnergy
        (shiftedReflectedBlockCoeff sigma (-sigma) v) N ≤
      (N : ℝ)⁻¹ * (harmonic (2 * N) : ℝ) ^ 4 := by
  apply coefficientEnergy_le_mul_harmonic_four _ _ (by positivity)
  intro n hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
  have hnN : N < n := (Finset.mem_Ioc.mp hn).1
  rw [norm_shiftedReflectedBlockCoeff_sq sigma (-sigma) v hnpos]
  rw [norm_shiftedDivisorBlockCoeff_sq hnpos]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hnN.le
  have hinv : (n : ℝ)⁻¹ ≤ (N : ℝ)⁻¹ :=
    (inv_le_inv₀ hnR hNR).2 hNn
  have hpow : (n : ℝ) ^ (-2 * (1 - sigma - (-sigma))) ≤
      (N : ℝ)⁻¹ / (n : ℝ) := by
    have hexp : -2 * (1 - sigma - (-sigma)) = (-2 : ℝ) := by ring
    calc
      (n : ℝ) ^ (-2 * (1 - sigma - (-sigma))) =
          (((n : ℝ) ^ 2)⁻¹) := by
            rw [hexp, show (-2 : ℝ) = -(2 : ℝ) by norm_num,
              Real.rpow_neg (le_of_lt hnR)]
            congr 1
            exact Real.rpow_natCast (n : ℝ) 2
      _ = (n : ℝ)⁻¹ / (n : ℝ) := by field_simp
      _ ≤ (N : ℝ)⁻¹ / (n : ℝ) :=
        div_le_div_of_nonneg_right hinv hnR.le
  have hdiv0 : 0 ≤ (orderedDivisorCount 2 n : ℝ) ^ 2 := sq_nonneg _
  calc
    (orderedDivisorCount 2 n : ℝ) ^ 2 *
        (n : ℝ) ^ (-2 * (1 - sigma - (-sigma))) ≤
      (orderedDivisorCount 2 n : ℝ) ^ 2 *
        ((N : ℝ)⁻¹ / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow hdiv0
    _ = (N : ℝ)⁻¹ *
        ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by ring

/-- On the near line `u=-1/log X`, its extra positive exponent only improves
the lower-strip energy bound. -/
theorem coefficientEnergy_shortReflectedBlockCoeff_le
    (N : ℕ) {X Y sigma delta : ℝ}
    (hX : 1 < X) (hNY : (2 * N : ℕ) ≤ Y) (hdelta : 0 ≤ delta)
    (hsigmaUpper : sigma ≤ 1 / 2 + delta) (v : ℝ) :
    coefficientEnergy
        (shiftedReflectedBlockCoeff sigma (-(Real.log X)⁻¹) v) N ≤
      Real.exp (2 * delta * Real.log Y) *
        (harmonic (2 * N) : ℝ) ^ 4 := by
  have hlog : 0 < Real.log X := Real.log_pos hX
  apply coefficientEnergy_shiftedReflectedBlockCoeff_le_of_lower
    N hNY hdelta _ v
  have hinv : 0 ≤ (Real.log X)⁻¹ := (inv_pos.mpr hlog).le
  linarith

/-- One literal dyadic portion of a reflected series. -/
def shiftedReflectedDyadicBlock {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (N : ℕ)
    (sigma u v t : ℝ) : ℂ :=
  ∑ n ∈ dyadicSupport N,
    ramachandraReflectedTerm psi
      (ramachandraShiftedPoint sigma t + ((u : ℂ) + v * I)) n

/-- Exact identification with the dual all-character block. -/
theorem shiftedReflectedDyadicBlock_eq_ramachandraDyadicBlock
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (N : ℕ) (sigma u v t : ℝ) :
    shiftedReflectedDyadicBlock psi N sigma u v t =
      ramachandraDyadicBlock d N
        (shiftedReflectedBlockCoeff sigma u v) true psi t := by
  unfold shiftedReflectedDyadicBlock ramachandraDyadicBlock
    twistedFinitePolynomial
  simp only [if_true]
  apply Finset.sum_congr rfl
  intro n hn
  exact reflectedTerm_eq_blockTerm psi
    (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1) sigma u t v

/-- The exact reflected coefficient depends continuously on the Mellin
ordinate. -/
theorem continuous_shiftedReflectedBlockCoeff
    (sigma u : ℝ) (n : ℕ) :
    Continuous (fun v => shiftedReflectedBlockCoeff sigma u v n) := by
  unfold shiftedReflectedBlockCoeff twistedPhase
  fun_prop

end
end RamachandraShiftedReflectedSeries

#print axioms RamachandraShiftedReflectedSeries.reflectedTerm_eq_blockTerm
#print axioms RamachandraShiftedReflectedSeries.coefficientEnergy_shiftedReflectedBlockCoeff_le
#print axioms RamachandraShiftedReflectedSeries.shiftedReflectedDyadicBlock_eq_ramachandraDyadicBlock
#print axioms RamachandraShiftedReflectedSeries.coefficientEnergy_longReflectedBlockCoeff_le
#print axioms RamachandraShiftedReflectedSeries.coefficientEnergy_quarterLineReflectedBlockCoeff_le
#print axioms RamachandraShiftedReflectedSeries.coefficientEnergy_shortReflectedBlockCoeff_le
#print axioms RamachandraShiftedReflectedSeries.coefficientEnergy_negHalfReflectedBlockCoeff_le
#print axioms RamachandraShiftedReflectedSeries.coefficientEnergy_zeroLineReflectedBlockCoeff_le
