import RamachandraShortFunctionalFactorMomentEnvelope
import RamachandraShiftedReflectedHeadAssembly
import RamachandraFullLineReflectedBlockBudget
import RamachandraShiftedDirectAssembly

/-!
# All-character full-line budget for the literal reflected head

This is the finite arithmetic input for Ramachandra's short contour.  The
literal endpoint `n ≤ X` is kept.  It is split into the unit coefficient and
the exact source dyadic shells, with the Mellin ordinate remaining continuous.
-/

namespace RamachandraShortHeadFamilyBudget

open scoped BigOperators Interval LSeries.notation
open Complex MeasureTheory
open BHPRamachandraMeanValueFromDyadicAFE
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedReflectedSeries
open RamachandraShiftedReflectedHeadAssembly
open RamachandraFullLineReflectedBlockBudget
open RamachandraGammaWeightIntegrability
open RamachandraPrimitiveShiftedMellinReduction
open RamachandraShiftedDirectAssembly
open RamachandraShiftedCoefficientEnergy
open RamachandraShiftedContourSharpEnvelopes
open MRTLemma215DyadicPartition
open CGLProofDAG
open MAPMRTLemma210OrthogonalityReduction
open MontgomeryVaughanFiniteReduction
open BHPAllCharacterDyadicBudget

noncomputable section

set_option maxHeartbeats 1000000

variable {d : ℕ} [NeZero d]

/-- The exact finite reflected head written at the short functional point. -/
def shortReflectedHead
    (psi : DirichletCharacter ℂ d) (X sigma t v : ℝ) : ℂ :=
  ramachandraReflectedHead psi X (shortFunctionalPoint X sigma t v)

theorem shortFunctionalPoint_eq_shifted
    (X sigma t v : ℝ) :
    shortFunctionalPoint X sigma t v =
      ramachandraShiftedPoint sigma t +
        (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I) := by
  apply Complex.ext <;>
    simp [shortFunctionalPoint, ramachandraShiftedPoint] <;> ring

/-- The unit coefficient in the reflected head has norm at most one. -/
theorem norm_reflectedHeadSourceUnitPolynomial_le_one
    (psi : DirichletCharacter ℂ d)
    {M : ℕ} (hM : 1 ≤ M) (sigma u v t : ℝ) :
    ‖twistedFinitePolynomial d (Finset.Icc 1 M)
      (reflectedHeadSourceUnitCoeff M sigma u v) (star psi) (-t)‖ ≤ 1 := by
  have hcount : orderedDivisorCount 2 1 = 1 := by
    rw [orderedDivisorCount_two_eq_card_divisors (by norm_num)]
    norm_num
  unfold twistedFinitePolynomial
  rw [Finset.sum_eq_single 1]
  · simp [reflectedHeadSourceUnitCoeff, sourceUnitCoeff, hM,
      shiftedReflectedBlockCoeff, shiftedDivisorBlockCoeff,
      twistedPhase, hcount]
  · intro n hn hn1
    unfold reflectedHeadSourceUnitCoeff sourceUnitCoeff
    simp [hn1]
  · intro hnot
    exact (hnot (Finset.mem_Icc.mpr ⟨le_rfl, hM⟩)).elim

/-- Masking the exact reflected coefficient by a source shell can only lower
its dyadic energy.  On the near line the reflected exponent is at least
`1/2`, so there is no shift loss. -/
theorem coefficientEnergy_reflectedHeadSourceShellCoeff_le
    (M : ℕ) (j : Fin (sourceDyadicCount M))
    {X sigma : ℝ} (hX : 1 < X)
    (hline : 1 / 2 ≤ 1 - sigma + (Real.log X)⁻¹) (v : ℝ) :
    coefficientEnergy
        (reflectedHeadSourceShellCoeff M sigma (-(Real.log X)⁻¹) v j)
        (2 ^ (j : ℕ)) ≤
      (harmonic (2 * 2 ^ (j : ℕ)) : ℝ) ^ 4 := by
  have henergy := coefficientEnergy_le_mul_harmonic_four
    (reflectedHeadSourceShellCoeff M sigma (-(Real.log X)⁻¹) v j)
    (2 ^ (j : ℕ)) (K := 1) (by norm_num : (0 : ℝ) ≤ 1) (by
      intro n hn
      unfold reflectedHeadSourceShellCoeff sourceDyadicCoeff
      split_ifs with hkeep
      · have hterm :
            ‖shiftedReflectedBlockCoeff sigma (-(Real.log X)⁻¹) v n‖ ^ 2 ≤
              ((orderedDivisorCount 2 n : ℝ) ^ 2 / (n : ℝ)) := by
          have hnpos : 0 < n := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
          rw [norm_shiftedReflectedBlockCoeff_sq sigma (-(Real.log X)⁻¹) v hnpos]
          have h := norm_shiftedDivisorBlockCoeff_sq_le_of_lower
            (n := n) (Y := (n : ℝ))
            (sigma := 1 - sigma - (-(Real.log X)⁻¹)) (delta := 0)
            (by omega) le_rfl (by norm_num : (0 : ℝ) ≤ 0)
            (by simpa using hline)
          simpa using h
        simpa using hterm
      · have hnpos : 0 < n := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
        simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), one_mul]
        exact div_nonneg (sq_nonneg _) (by exact_mod_cast hnpos.le))
  simpa using henergy

/-- One exact source shell, integrated over the full Mellin line, has the
standard all-character length-energy cost. -/
theorem integral_shortHeadSourceShell_le
    (M : ℕ) (j : Fin (sourceDyadicCount M))
    {X T sigma : ℝ} (hT : 0 ≤ T) (hX : 1 < X)
    (hline : 1 / 2 ≤ 1 - sigma + (Real.log X)⁻¹)
    (weight : ℝ → ℝ) (hweight : Continuous weight)
    (hweightInt : Integrable weight) (hweight0 : ∀ v, 0 ≤ weight v) :
    (∫ v : ℝ, weight v *
      (∫ t in (-T)..T,
        ∑ psi : DirichletCharacter ℂ d,
          ‖ramachandraDyadicBlock d (2 ^ (j : ℕ))
            (reflectedHeadSourceShellCoeff M sigma (-(Real.log X)⁻¹) v j)
            true psi t‖ ^ 2)) ≤
      (∫ v : ℝ, weight v) *
        (((d : ℝ) * (2 * T) + 8 * Real.pi * (2 ^ (j : ℕ) : ℕ)) *
          (harmonic (2 * 2 ^ (j : ℕ)) : ℝ) ^ 4) := by
  apply integral_allCharacter_intervalIntegral_weightedBlock_le
    d (2 ^ (j : ℕ)) Nat.one_le_two_pow hT
      (by positivity : (0 : ℝ) ≤ (harmonic (2 * 2 ^ (j : ℕ)) : ℝ) ^ 4)
      (fun v => reflectedHeadSourceShellCoeff M sigma (-(Real.log X)⁻¹) v j)
      (fun n => continuous_reflectedHeadSourceShellCoeff
        M sigma (-(Real.log X)⁻¹) j n)
      (fun v => coefficientEnergy_reflectedHeadSourceShellCoeff_le
        M j hX hline v)
      weight hweight hweightInt hweight0

/-- The fixed-`v` length-energy cost of one exact head shell. -/
def shortHeadSourceShellCost
    (d M : ℕ) (T : ℝ) (j : Fin (sourceDyadicCount M)) : ℝ :=
  ((d : ℝ) * (2 * T) + 8 * Real.pi * (2 ^ (j : ℕ) : ℕ)) *
    (harmonic (2 * 2 ^ (j : ℕ)) : ℝ) ^ 4

/-- At each Mellin ordinate the literal finite head has the complete-character
mean-square bound obtained from its unit term and exact source shells. -/
theorem intervalIntegral_sum_norm_shortReflectedHead_sq_le
    (d M : ℕ) [NeZero d] (hM : 1 ≤ M)
    {X T sigma v : ℝ} (hfloor : M = ⌊X⌋₊)
    (hT : 0 ≤ T) (hX : 1 < X)
    (hline : 1 / 2 ≤ 1 - sigma + (Real.log X)⁻¹) :
    (∫ t in (-T)..T,
      ∑ psi : DirichletCharacter ℂ d,
        ‖shortReflectedHead psi X sigma t v‖ ^ 2) ≤
      4 * (d : ℝ) * T +
        2 * (sourceDyadicCount M : ℝ) *
          ∑ j : Fin (sourceDyadicCount M),
            shortHeadSourceShellCost d M T j := by
  let U : DirichletCharacter ℂ d → ℝ → ℂ := fun psi t =>
    twistedFinitePolynomial d (Finset.Icc 1 M)
      (reflectedHeadSourceUnitCoeff M sigma (-(Real.log X)⁻¹) v)
      (star psi) (-t)
  let S : Fin (sourceDyadicCount M) →
      DirichletCharacter ℂ d → ℝ → ℂ := fun j psi t =>
    ramachandraDyadicBlock d (2 ^ (j : ℕ))
      (reflectedHeadSourceShellCoeff M sigma (-(Real.log X)⁻¹) v j)
      true psi t
  have hhead (psi : DirichletCharacter ℂ d) (t : ℝ) :
      shortReflectedHead psi X sigma t v = U psi t + ∑ j, S j psi t := by
    unfold shortReflectedHead
    rw [shortFunctionalPoint_eq_shifted]
    have h := ramachandraReflectedHead_eq_unit_add_shells
      psi (by linarith : 0 ≤ X) sigma (-(Real.log X)⁻¹) v t
    rw [← hfloor] at h
    simpa [U, S] using h
  have hpoint (psi : DirichletCharacter ℂ d) (t : ℝ) :
      ‖shortReflectedHead psi X sigma t v‖ ^ 2 ≤
        2 * ‖U psi t‖ ^ 2 +
          2 * (sourceDyadicCount M : ℝ) *
            ∑ j : Fin (sourceDyadicCount M), ‖S j psi t‖ ^ 2 := by
    rw [hhead]
    have hsum := norm_fin_sum_sq_le_card_mul_sum_norm_sq
      (Finset.univ : Finset (Fin (sourceDyadicCount M)))
      (fun j => S j psi t)
    have htri := norm_add_le (U psi t) (∑ j, S j psi t)
    have hsq : ‖U psi t + ∑ j, S j psi t‖ ^ 2 ≤
        (‖U psi t‖ + ‖∑ j, S j psi t‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 htri
    have hadd : ‖U psi t + ∑ j, S j psi t‖ ^ 2 ≤
        2 * ‖U psi t‖ ^ 2 + 2 * ‖∑ j, S j psi t‖ ^ 2 := by
      have hdif : 0 ≤ (‖U psi t‖ - ‖∑ j, S j psi t‖) ^ 2 := sq_nonneg _
      nlinarith
    have hcard :
        ((Finset.univ : Finset (Fin (sourceDyadicCount M))).card : ℝ) =
          sourceDyadicCount M := by simp
    rw [hcard] at hsum
    nlinarith [mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)]
  have hUcont (psi : DirichletCharacter ℂ d) :
      Continuous (fun t : ℝ => U psi t) := by
    dsimp [U]
    unfold twistedFinitePolynomial twistedPhase
    fun_prop
  have hScont (j : Fin (sourceDyadicCount M))
      (psi : DirichletCharacter ℂ d) :
      Continuous (fun t : ℝ => S j psi t) := by
    dsimp [S]
    exact continuous_ramachandraDyadicBlock d (2 ^ (j : ℕ))
      (reflectedHeadSourceShellCoeff M sigma (-(Real.log X)⁻¹) v j)
      true psi
  have hleftCont : Continuous (fun t : ℝ =>
      ∑ psi : DirichletCharacter ℂ d,
        ‖shortReflectedHead psi X sigma t v‖ ^ 2) := by
    apply continuous_finsetSum
    intro psi hpsi
    have hsum : Continuous (fun t : ℝ => ∑ j, S j psi t) := by
      apply continuous_finsetSum
      intro j hj
      exact hScont j psi
    have heq : (fun t : ℝ => shortReflectedHead psi X sigma t v) =
        fun t => U psi t + ∑ j, S j psi t := by
      funext t
      exact hhead psi t
    have hc : Continuous (fun t : ℝ => shortReflectedHead psi X sigma t v) := by
      rw [heq]
      exact (hUcont psi).add hsum
    exact hc.norm.pow 2
  have hrightCont : Continuous (fun t : ℝ =>
      2 * ∑ psi : DirichletCharacter ℂ d, ‖U psi t‖ ^ 2 +
        2 * (sourceDyadicCount M : ℝ) *
          ∑ j : Fin (sourceDyadicCount M),
            ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2) := by
    apply Continuous.add
    · apply continuous_const.mul
      apply continuous_finsetSum
      intro psi hpsi
      exact (hUcont psi).norm.pow 2
    · apply continuous_const.mul
      apply continuous_finsetSum
      intro j hj
      apply continuous_finsetSum
      intro psi hpsi
      exact (hScont j psi).norm.pow 2
  calc
    (∫ t in (-T)..T,
      ∑ psi : DirichletCharacter ℂ d,
        ‖shortReflectedHead psi X sigma t v‖ ^ 2) ≤
      ∫ t in (-T)..T,
        (2 * ∑ psi : DirichletCharacter ℂ d, ‖U psi t‖ ^ 2 +
          2 * (sourceDyadicCount M : ℝ) *
            ∑ j : Fin (sourceDyadicCount M),
              ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2) := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · exact hleftCont.intervalIntegrable _ _
        · exact hrightCont.intervalIntegrable _ _
        · intro t ht
          calc
            (∑ psi : DirichletCharacter ℂ d,
              ‖shortReflectedHead psi X sigma t v‖ ^ 2) ≤
                ∑ psi : DirichletCharacter ℂ d,
                  (2 * ‖U psi t‖ ^ 2 +
                    2 * (sourceDyadicCount M : ℝ) *
                      ∑ j : Fin (sourceDyadicCount M), ‖S j psi t‖ ^ 2) :=
              Finset.sum_le_sum fun psi hpsi => hpoint psi t
            _ = 2 * ∑ psi : DirichletCharacter ℂ d, ‖U psi t‖ ^ 2 +
                2 * (sourceDyadicCount M : ℝ) *
                  ∑ j : Fin (sourceDyadicCount M),
                    ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_comm]
              simp_rw [← Finset.mul_sum]
    _ = 2 * (∫ t in (-T)..T,
          ∑ psi : DirichletCharacter ℂ d, ‖U psi t‖ ^ 2) +
        2 * (sourceDyadicCount M : ℝ) *
          ∑ j : Fin (sourceDyadicCount M),
            (∫ t in (-T)..T,
              ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2) := by
      have hUfamily : Continuous (fun t : ℝ =>
          ∑ psi : DirichletCharacter ℂ d, ‖U psi t‖ ^ 2) := by
        apply continuous_finsetSum
        intro psi hpsi
        exact (hUcont psi).norm.pow 2
      have hSfamily (j : Fin (sourceDyadicCount M)) :
          Continuous (fun t : ℝ =>
            ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2) := by
        apply continuous_finsetSum
        intro psi hpsi
        exact (hScont j psi).norm.pow 2
      have hSsum : Continuous (fun t : ℝ =>
          ∑ j : Fin (sourceDyadicCount M),
            ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2) := by
        apply continuous_finsetSum
        intro j hj
        exact hSfamily j
      rw [intervalIntegral.integral_add
        (f := fun t => 2 * ∑ psi : DirichletCharacter ℂ d, ‖U psi t‖ ^ 2)
        (g := fun t => 2 * (sourceDyadicCount M : ℝ) *
          ∑ j : Fin (sourceDyadicCount M),
            ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2)
        ((continuous_const.mul hUfamily).intervalIntegrable _ _)
        ((continuous_const.mul hSsum).intervalIntegrable _ _)]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      congr 1
      rw [intervalIntegral.integral_finsetSum]
      intro j hj
      exact (hSfamily j).intervalIntegrable _ _
    _ ≤ 2 * (2 * (d : ℝ) * T) +
        2 * (sourceDyadicCount M : ℝ) *
          ∑ j : Fin (sourceDyadicCount M),
            shortHeadSourceShellCost d M T j := by
      have hunit : (∫ t in (-T)..T,
          ∑ psi : DirichletCharacter ℂ d, ‖U psi t‖ ^ 2) ≤
          2 * (d : ℝ) * T := by
        have hcont : Continuous (fun t : ℝ =>
            ∑ psi : DirichletCharacter ℂ d, ‖U psi t‖ ^ 2) := by
          apply continuous_finsetSum
          intro psi hpsi
          exact (hUcont psi).norm.pow 2
        calc
          _ ≤ ∫ _t in (-T)..T,
              (Fintype.card (DirichletCharacter ℂ d) : ℝ) := by
            apply intervalIntegral.integral_mono_on (by linarith)
            · exact hcont.intervalIntegrable _ _
            · exact continuous_const.intervalIntegrable _ _
            · intro t ht
              calc
                (∑ psi : DirichletCharacter ℂ d, ‖U psi t‖ ^ 2) ≤
                    ∑ _psi : DirichletCharacter ℂ d, (1 : ℝ) := by
                  apply Finset.sum_le_sum
                  intro psi hpsi
                  exact pow_le_one₀ (norm_nonneg _)
                    (by
                      simpa [U] using
                        (norm_reflectedHeadSourceUnitPolynomial_le_one
                          psi hM sigma (-(Real.log X)⁻¹) v t))
                _ = _ := by simp
          _ = 2 * T * (Fintype.card (DirichletCharacter ℂ d) : ℝ) := by
            rw [intervalIntegral.integral_const]
            simp only [smul_eq_mul]
            ring
          _ ≤ 2 * T * (d : ℝ) := by
            have hc : (Fintype.card (DirichletCharacter ℂ d) : ℝ) ≤ d := by
              exact_mod_cast MAPMRTCorollary53Source.card_dirichletCharacters_le_modulus d
            exact mul_le_mul_of_nonneg_left hc (by positivity)
          _ = _ := by ring
      have hshell (j : Fin (sourceDyadicCount M)) :
          (∫ t in (-T)..T,
            ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2) ≤
            shortHeadSourceShellCost d M T j := by
        have hmean := integral_sum_norm_ramachandraDyadicBlock_sq_le
          d (2 ^ (j : ℕ)) Nat.one_le_two_pow
          (reflectedHeadSourceShellCoeff M sigma (-(Real.log X)⁻¹) v j)
          true hT
        apply hmean.trans
        unfold ramachandraDyadicCost shortHeadSourceShellCost
        exact mul_le_mul_of_nonneg_left
          (coefficientEnergy_reflectedHeadSourceShellCoeff_le M j hX hline v)
          (by positivity)
      have hsum : (∑ j : Fin (sourceDyadicCount M),
          (∫ t in (-T)..T,
            ∑ psi : DirichletCharacter ℂ d, ‖S j psi t‖ ^ 2)) ≤
          ∑ j : Fin (sourceDyadicCount M), shortHeadSourceShellCost d M T j :=
        Finset.sum_le_sum fun j hj => hshell j
      have hJ : 0 ≤ 2 * (sourceDyadicCount M : ℝ) := by positivity
      exact add_le_add
        (mul_le_mul_of_nonneg_left hunit (by norm_num : (0 : ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left hsum hJ)
    _ = _ := by ring

/-- Joint continuity of the literal finite reflected head in Mellin and
external ordinates. -/
theorem continuous_uncurry_shortReflectedHead
    (psi : DirichletCharacter ℂ d) {X : ℝ} (hX : 0 ≤ X) (sigma : ℝ) :
    Continuous (Function.uncurry (fun v t =>
      shortReflectedHead psi X sigma t v)) := by
  let M : ℕ := ⌊X⌋₊
  have heq : Function.uncurry (fun v t =>
      shortReflectedHead psi X sigma t v) =
      Function.uncurry (fun v t =>
        twistedFinitePolynomial d (Finset.Icc 1 M)
          (shiftedReflectedBlockCoeff sigma (-(Real.log X)⁻¹) v)
          (star psi) (-t)) := by
    funext p
    change ramachandraReflectedHead psi X
        (shortFunctionalPoint X sigma p.2 p.1) =
      twistedFinitePolynomial d (Finset.Icc 1 M)
        (shiftedReflectedBlockCoeff sigma (-(Real.log X)⁻¹) p.1)
        (star psi) (-p.2)
    rw [shortFunctionalPoint_eq_shifted]
    simpa [M] using ramachandraReflectedHead_eq_prefixPolynomial
      psi hX sigma (-(Real.log X)⁻¹) p.1 p.2
  rw [heq]
  unfold Function.uncurry twistedFinitePolynomial twistedPhase
  apply continuous_finsetSum
  intro n hn
  exact (((continuous_shiftedReflectedBlockCoeff
    sigma (-(Real.log X)⁻¹) n).comp continuous_fst).mul continuous_const).mul
      (Complex.continuous_exp.comp (by fun_prop))

/-- The exact full-Mellin-line complete-character head moment. -/
def shortHeadAllCharacterMellinMoment
    (d : ℕ) [NeZero d] (X T sigma : ℝ) : ℝ :=
  ∫ v : ℝ, gammaPolynomialWeight (-(Real.log X)⁻¹) v *
    (∫ t in (-T)..T,
      ∑ psi : DirichletCharacter ℂ d,
        ‖shortReflectedHead psi X sigma t v‖ ^ 2)

/-- Full-line head budget, preserving the literal endpoint `n ≤ X`. -/
theorem shortHeadAllCharacterMellinMoment_le
    (d : ℕ) [NeZero d] {X T sigma : ℝ}
    (hT : 0 ≤ T) (hX : 6 ≤ X)
    (hline : 1 / 2 ≤ 1 - sigma + (Real.log X)⁻¹) :
    shortHeadAllCharacterMellinMoment d X T sigma ≤
      (∫ v : ℝ, gammaPolynomialWeight (-(Real.log X)⁻¹) v) *
        (4 * (d : ℝ) * T +
          2 * (sourceDyadicCount ⌊X⌋₊ : ℝ) *
            ∑ j : Fin (sourceDyadicCount ⌊X⌋₊),
              shortHeadSourceShellCost d ⌊X⌋₊ T j) := by
  let w : ℝ → ℝ := gammaPolynomialWeight (-(Real.log X)⁻¹)
  let G : ℝ → ℝ := fun v =>
    ∫ t in (-T)..T,
      ∑ psi : DirichletCharacter ℂ d,
        ‖shortReflectedHead psi X sigma t v‖ ^ 2
  let C : ℝ := 4 * (d : ℝ) * T +
    2 * (sourceDyadicCount ⌊X⌋₊ : ℝ) *
      ∑ j : Fin (sourceDyadicCount ⌊X⌋₊),
        shortHeadSourceShellCost d ⌊X⌋₊ T j
  have hlog : 1 < Real.log X :=
    RamachandraShiftedDirectParameters.one_lt_log_of_three_le (by linarith)
  have hcLo : -1 < -(Real.log X)⁻¹ := by
    have hi : (Real.log X)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).2 hlog
    linarith
  have hcHi : -(Real.log X)⁻¹ < 0 := by
    have hi : 0 < (Real.log X)⁻¹ := inv_pos.mpr (by linarith)
    linarith
  have hwcont : Continuous w := continuous_gammaPolynomialWeight hcLo hcHi
  have hwint : Integrable w := integrable_gammaPolynomialWeight hcLo hcHi
  have hw0 (v : ℝ) : 0 ≤ w v := gammaPolynomialWeight_nonneg _ _
  have hGcont : Continuous G := by
    unfold G
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    apply continuous_finsetSum
    intro psi hpsi
    exact (continuous_uncurry_shortReflectedHead psi (X := X)
      (by linarith) sigma).norm.pow 2
  have hG0 (v : ℝ) : 0 ≤ G v := by
    unfold G
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    positivity
  have hC0 : 0 ≤ C := by
    dsimp [C, shortHeadSourceShellCost]
    positivity
  have hGle (v : ℝ) : G v ≤ C := by
    unfold G C
    exact intervalIntegral_sum_norm_shortReflectedHead_sq_le
      d ⌊X⌋₊ (by
        rw [Nat.one_le_iff_ne_zero]
        intro h
        have hf : ⌊X⌋₊ = 0 := h
        have hxlt := Nat.lt_floor_add_one X
        rw [hf] at hxlt
        norm_num at hxlt
        linarith)
      rfl hT (by linarith) hline
  have hright : Integrable (fun v => w v * C) := hwint.mul_const C
  have hleft : Integrable (fun v => w v * G v) := by
    apply hright.mono'
    · exact (hwcont.mul hGcont).aestronglyMeasurable
    · filter_upwards with v
      rw [Real.norm_of_nonneg (mul_nonneg (hw0 v) (hG0 v))]
      exact mul_le_mul_of_nonneg_left (hGle v) (hw0 v)
  unfold shortHeadAllCharacterMellinMoment
  change (∫ v : ℝ, w v * G v) ≤ (∫ v : ℝ, w v) * C
  calc
    (∫ v : ℝ, w v * G v) ≤ ∫ v : ℝ, w v * C := by
      apply integral_mono hleft hright
      intro v
      exact mul_le_mul_of_nonneg_left (hGle v) (hw0 v)
    _ = (∫ v : ℝ, w v) * C := by rw [MeasureTheory.integral_mul_const]

end
end RamachandraShortHeadFamilyBudget

#print axioms RamachandraShortHeadFamilyBudget.norm_reflectedHeadSourceUnitPolynomial_le_one
#print axioms RamachandraShortHeadFamilyBudget.coefficientEnergy_reflectedHeadSourceShellCoeff_le
#print axioms RamachandraShortHeadFamilyBudget.integral_shortHeadSourceShell_le
