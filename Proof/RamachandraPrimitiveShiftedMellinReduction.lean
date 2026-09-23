import RamachandraPrimitiveShiftedFiniteReduction
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Continuous Mellin reduction for Ramachandra's primitive shifted estimate

Ramachandra's Lemmas 5--6 retain a continuous Mellin ordinate.  This module
proves the missing Fubini step literally: it never replaces that integral by
quadrature or by a finite-rank AFE.  For each Mellin ordinate, the already
certified character-orthogonality/Hilbert mean square is applied to the exact
coefficient array, and the result is then integrated.
-/

namespace RamachandraPrimitiveShiftedMellinReduction

open scoped BigOperators Interval
open Complex MeasureTheory
open RamachandraTheorem6ShiftedStripSource
open RamachandraTheorem6SourceProofChain
open RamachandraPrimitiveShiftedFiniteReduction
open BHPAllCharacterDyadicBudget
open MAPMRTLemma210OrthogonalityReduction

noncomputable section

/-- Fubini for two compact real intervals under the source's joint continuity
hypothesis. -/
theorem intervalIntegral_intervalIntegral_swap_of_continuous
    (f : ℝ → ℝ → ℝ) (hf : Continuous (Function.uncurry f))
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ x in a..b, ∫ y in c..d, f x y) =
      ∫ y in c..d, ∫ x in a..b, f x y := by
  have hcompact : IntegrableOn (Function.uncurry f)
      (Set.Icc a b ×ˢ Set.Icc c d) (volume.prod volume) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hIoc : IntegrableOn (Function.uncurry f)
      (Set.Ioc a b ×ˢ Set.Ioc c d) (volume.prod volume) :=
    hcompact.mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have hprod : Integrable (Function.uncurry f)
      ((volume.restrict (Set.uIoc a b)).prod
        (volume.restrict (Set.uIoc c d))) := by
    rw [Set.uIoc_of_le hab, Set.uIoc_of_le hcd]
    simpa only [← Measure.prod_restrict, IntegrableOn] using hIoc
  have hswap := MeasureTheory.intervalIntegral_integral_swap
    (μ := volume.restrict (Set.uIoc c d)) hprod
  rw [Set.uIoc_of_le hcd] at hswap
  simpa [intervalIntegral.integral_of_le hcd] using hswap

/-- Joint continuity of one literal dyadic block when its coefficient array
varies continuously with the Mellin ordinate. -/
theorem continuous_uncurry_ramachandraDyadicBlock
    (q N : ℕ) [NeZero q] (dual : Bool)
    (b : ℝ → ℕ → ℂ) (hb : ∀ n, Continuous (fun v => b v n))
    (chi : DirichletCharacter ℂ q) :
    Continuous (Function.uncurry (fun t v =>
      ramachandraDyadicBlock q N (b v) dual chi t)) := by
  cases dual with
  | false =>
      unfold Function.uncurry ramachandraDyadicBlock
        twistedFinitePolynomial twistedPhase
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply continuous_finsetSum
      intro n hn
      exact ((((hb n).comp continuous_snd).mul continuous_const).mul
        (Complex.continuous_exp.comp (by fun_prop)))
  | true =>
      unfold Function.uncurry ramachandraDyadicBlock
        twistedFinitePolynomial twistedPhase
      simp only [↓reduceIte]
      apply continuous_finsetSum
      intro n hn
      exact ((((hb n).comp continuous_snd).mul continuous_const).mul
        (Complex.continuous_exp.comp (by fun_prop)))

/-- Joint continuity of the nonnegative weighted squared block. -/
theorem continuous_uncurry_weightedBlock
    (q N : ℕ) [NeZero q] (dual : Bool)
    (b : ℝ → ℕ → ℂ) (weight : ℝ → ℝ)
    (hb : ∀ n, Continuous (fun v => b v n))
    (hweight : Continuous weight)
    (chi : DirichletCharacter ℂ q) :
    Continuous (Function.uncurry (fun t v =>
      weight v * ‖ramachandraDyadicBlock q N (b v) dual chi t‖ ^ 2)) := by
  exact (hweight.comp continuous_snd).mul
    ((continuous_uncurry_ramachandraDyadicBlock q N dual b hb chi).norm.pow 2)

/-- The continuous-Mellin version of the complete-character dyadic mean
square.  This is the exact analytic operation only sketched in the proofs of
Ramachandra Lemmas 5--6: Fubini, followed by the mean-square estimate at each
fixed Mellin ordinate. -/
theorem allCharacter_doubleIntegral_weightedBlock_le
    (q N : ℕ) [NeZero q] (hN : 1 ≤ N)
    (dual : Bool) (b : ℝ → ℕ → ℂ) (weight : ℝ → ℝ)
    (hb : ∀ n, Continuous (fun v => b v n))
    (hweight : Continuous weight)
    {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hweight0 : ∀ v ∈ Set.Icc (-V) V, 0 ≤ weight v) :
    (∑ chi : DirichletCharacter ℂ q,
      ∫ t in (-U)..U,
        ∫ v in (-V)..V,
          weight v * ‖ramachandraDyadicBlock q N (b v) dual chi t‖ ^ 2) ≤
      ∫ v in (-V)..V, weight v * ramachandraDyadicCost q N U (b v) := by
  classical
  have hswap (chi : DirichletCharacter ℂ q) :
      (∫ t in (-U)..U,
        ∫ v in (-V)..V,
          weight v * ‖ramachandraDyadicBlock q N (b v) dual chi t‖ ^ 2) =
      ∫ v in (-V)..V,
        ∫ t in (-U)..U,
          weight v * ‖ramachandraDyadicBlock q N (b v) dual chi t‖ ^ 2 :=
    intervalIntegral_intervalIntegral_swap_of_continuous _
      (continuous_uncurry_weightedBlock q N dual b weight hb hweight chi)
      (by linarith) (by linarith)
  rw [show (∑ chi : DirichletCharacter ℂ q,
      ∫ t in (-U)..U,
        ∫ v in (-V)..V,
          weight v * ‖ramachandraDyadicBlock q N (b v) dual chi t‖ ^ 2) =
      ∑ chi : DirichletCharacter ℂ q,
        ∫ v in (-V)..V,
          ∫ t in (-U)..U,
            weight v * ‖ramachandraDyadicBlock q N (b v) dual chi t‖ ^ 2 by
        apply Finset.sum_congr rfl
        intro chi hchi
        exact hswap chi]
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_mono_on (by linarith)
    · apply Continuous.intervalIntegrable
      apply continuous_finsetSum
      intro chi hchi
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      exact (continuous_uncurry_weightedBlock q N dual b weight hb hweight chi).comp
        continuous_swap
    · apply Continuous.intervalIntegrable
      exact hweight.mul (by
        unfold ramachandraDyadicCost MontgomeryVaughanFiniteReduction.coefficientEnergy
        fun_prop)
    · intro v hv
      have hw := hweight0 v hv
      simp_rw [intervalIntegral.integral_const_mul]
      rw [← Finset.mul_sum]
      have hmean := integral_sum_norm_ramachandraDyadicBlock_sq_le
        q N hN (b v) dual hU
      have heq :
          (∑ chi : DirichletCharacter ℂ q,
            ∫ t in (-U)..U,
              ‖ramachandraDyadicBlock q N (b v) dual chi t‖ ^ 2) =
            ∫ t in (-U)..U,
              ∑ chi : DirichletCharacter ℂ q,
                ‖ramachandraDyadicBlock q N (b v) dual chi t‖ ^ 2 := by
        rw [intervalIntegral.integral_finsetSum]
        intro chi hchi
        exact ((continuous_ramachandraDyadicBlock q N (b v) dual chi).norm.pow 2).intervalIntegrable _ _
      rw [heq]
      exact mul_le_mul_of_nonneg_left hmean hw
  · intro chi hchi
    have hparam : Continuous (fun v =>
        ∫ t in (-U)..U,
          weight v * ‖ramachandraDyadicBlock q N (b v) dual chi t‖ ^ 2) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      change Continuous (fun p : ℝ × ℝ =>
        weight p.1 *
          ‖ramachandraDyadicBlock q N (b p.1) dual chi p.2‖ ^ 2)
      simpa only [Function.uncurry, Function.comp_apply, Prod.swap_prod_mk] using!
        (continuous_uncurry_weightedBlock q N dual b weight hb hweight chi).comp
          continuous_swap
    exact hparam.intervalIntegrable _ _

/-! ## Finite family of continuous Mellin blocks -/

/-- The literal continuous-Mellin block family left after Cauchy in
Ramachandra Lemmas 5--6. -/
def ramachandraMellinDyadicFamily
    {J q : ℕ} [NeZero q]
    (dual : Fin J → Bool) (N : Fin J → ℕ)
    (b : Fin J → ℝ → ℕ → ℂ)
    (weight : Fin J → ℝ → ℝ) (V : ℝ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  ∑ j : Fin J,
    ∫ v in (-V)..V, weight j v *
      ‖ramachandraDyadicBlock q (N j) (b j v) (dual j) chi t‖ ^ 2

/-- Exact integrated length-energy cost of the continuous Mellin family. -/
def ramachandraMellinDyadicFamilyCost
    {J : ℕ} (q : ℕ) (U V : ℝ)
    (N : Fin J → ℕ) (b : Fin J → ℝ → ℕ → ℂ)
    (weight : Fin J → ℝ → ℝ) : ℝ :=
  ∑ j : Fin J,
    ∫ v in (-V)..V, weight j v *
      ramachandraDyadicCost q (N j) U (b j v)

theorem continuous_ramachandraMellinDyadicFamily
    {J q : ℕ} [NeZero q]
    (dual : Fin J → Bool) (N : Fin J → ℕ)
    (b : Fin J → ℝ → ℕ → ℂ)
    (weight : Fin J → ℝ → ℝ) (V : ℝ)
    (hb : ∀ j n, Continuous (fun v => b j v n))
    (hweight : ∀ j, Continuous (weight j))
    (chi : DirichletCharacter ℂ q) :
    Continuous (ramachandraMellinDyadicFamily dual N b weight V chi) := by
  unfold ramachandraMellinDyadicFamily
  apply continuous_finsetSum
  intro j hj
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact continuous_uncurry_weightedBlock q (N j) (dual j) (b j)
    (weight j) (hb j) (hweight j) chi

/-- Source-faithful primitive-family reduction with the Mellin ordinate
retained continuously.  The conclusion is obtained from exact Fubini and the
premise-free all-character dyadic mean square.  The sole pointwise premise is
the explicit contour/Cauchy majorant, not a fourth-moment estimate. -/
theorem primitiveFamilyShiftedFourthIntegral_le_mellinDyadicCost
    {J d : ℕ} [NeZero d]
    {U V sigma A : ℝ}
    (dual : Fin J → Bool) (N : Fin J → ℕ)
    (b : Fin J → ℝ → ℕ → ℂ)
    (weight : Fin J → ℝ → ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hA : 0 ≤ A)
    (hsigma : sigma ≠ 1)
    (hN : ∀ j, 1 ≤ N j)
    (hb : ∀ j n, Continuous (fun v => b j v n))
    (hweight : ∀ j, Continuous (weight j))
    (hweight0 : ∀ j v, v ∈ Set.Icc (-V) V → 0 ≤ weight j v)
    (hmajor : ∀ (chi : DirichletCharacter ℂ d), chi.IsPrimitive →
      ∀ t, |t| ≤ U →
        shiftedStripLFourth chi sigma t ≤
          A * ramachandraMellinDyadicFamily dual N b weight V chi t) :
    primitiveFamilyShiftedFourthIntegral d U sigma ≤
      A * ramachandraMellinDyadicFamilyCost d U V N b weight := by
  classical
  let F : DirichletCharacter ℂ d → ℝ → ℝ :=
    fun chi => primitiveMaskedShiftedFourth sigma chi
  have hF : ∀ chi, Continuous (F chi) := by
    intro chi
    exact continuous_primitiveMaskedShiftedFourth chi hsigma
  have hfamily : ∀ chi : DirichletCharacter ℂ d,
      Continuous (ramachandraMellinDyadicFamily dual N b weight V chi) := by
    intro chi
    exact continuous_ramachandraMellinDyadicFamily
      dual N b weight V hb hweight chi
  have hmajorMasked : ∀ (chi : DirichletCharacter ℂ d) t, |t| ≤ U →
      F chi t ≤
        A * ramachandraMellinDyadicFamily dual N b weight V chi t := by
    intro chi t ht
    by_cases hp : chi.IsPrimitive
    · simpa [F, primitiveMaskedShiftedFourth, hp] using hmajor chi hp t ht
    · have hright : 0 ≤
          A * ramachandraMellinDyadicFamily dual N b weight V chi t := by
        apply mul_nonneg hA
        unfold ramachandraMellinDyadicFamily
        apply Finset.sum_nonneg
        intro j hj
        apply intervalIntegral.integral_nonneg (by linarith)
        intro v hv
        exact mul_nonneg (hweight0 j v hv) (sq_nonneg _)
      simpa [F, primitiveMaskedShiftedFourth, hp] using hright
  have hchi (chi : DirichletCharacter ℂ d) :
      (∫ t in (-U)..U, F chi t) ≤
        ∫ t in (-U)..U,
          A * ramachandraMellinDyadicFamily dual N b weight V chi t := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (hF chi).intervalIntegrable _ _
    · exact (continuous_const.mul (hfamily chi)).intervalIntegrable _ _
    · intro t ht
      exact hmajorMasked chi t ((abs_le).2 ⟨by linarith [ht.1], ht.2⟩)
  have hblocks :
      (∑ j : Fin J,
        ∑ chi : DirichletCharacter ℂ d,
          ∫ t in (-U)..U,
            ∫ v in (-V)..V, weight j v *
              ‖ramachandraDyadicBlock d (N j) (b j v)
                (dual j) chi t‖ ^ 2) ≤
      ramachandraMellinDyadicFamilyCost d U V N b weight := by
    unfold ramachandraMellinDyadicFamilyCost
    apply Finset.sum_le_sum
    intro j hj
    exact allCharacter_doubleIntegral_weightedBlock_le
      d (N j) (hN j) (dual j) (b j) (weight j)
        (hb j) (hweight j) hU hV (hweight0 j)
  rw [primitiveFamilyShiftedFourthIntegral_eq_masked]
  calc
    (∑ chi : DirichletCharacter ℂ d,
        ∫ t in (-U)..U, F chi t) ≤
        ∑ chi : DirichletCharacter ℂ d,
          ∫ t in (-U)..U,
            A * ramachandraMellinDyadicFamily dual N b weight V chi t :=
      Finset.sum_le_sum fun chi hchiMem => hchi chi
    _ = A * ∑ j : Fin J,
        ∑ chi : DirichletCharacter ℂ d,
          ∫ t in (-U)..U,
            ∫ v in (-V)..V, weight j v *
              ‖ramachandraDyadicBlock d (N j) (b j v)
                (dual j) chi t‖ ^ 2 := by
      simp_rw [intervalIntegral.integral_const_mul]
      rw [← Finset.mul_sum]
      congr 1
      unfold ramachandraMellinDyadicFamily
      calc
        (∑ chi : DirichletCharacter ℂ d,
            ∫ t in (-U)..U,
              ∑ j : Fin J,
                ∫ v in (-V)..V, weight j v *
                  ‖ramachandraDyadicBlock d (N j) (b j v)
                    (dual j) chi t‖ ^ 2) =
            ∑ chi : DirichletCharacter ℂ d,
              ∑ j : Fin J,
                ∫ t in (-U)..U,
                  ∫ v in (-V)..V, weight j v *
                    ‖ramachandraDyadicBlock d (N j) (b j v)
                      (dual j) chi t‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro chi hchiMem
          rw [intervalIntegral.integral_finsetSum]
          intro j hj
          exact ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
            (continuous_uncurry_weightedBlock d (N j) (dual j) (b j)
              (weight j) (hb j) (hweight j) chi) (-V) V).intervalIntegrable _ _)
        _ = ∑ j : Fin J,
              ∑ chi : DirichletCharacter ℂ d,
                ∫ t in (-U)..U,
                  ∫ v in (-V)..V, weight j v *
                    ‖ramachandraDyadicBlock d (N j) (b j v)
                      (dual j) chi t‖ ^ 2 := by
          rw [Finset.sum_comm]
    _ ≤ A * ramachandraMellinDyadicFamilyCost d U V N b weight :=
      mul_le_mul_of_nonneg_left hblocks hA

/-! ## Exact source-construction boundary -/

/-- Concrete output of the omitted shifted analogue of Lemmas 3--6.

Unlike a fourth-moment premise, this data consists of the literal finite
dyadic block parameters, their continuous Mellin coefficients and weights,
the pointwise contour/Cauchy majorant, and the explicit length-energy budget.
The preceding theorem proves that these fields imply the desired moment. -/
structure PrimitiveShiftedMellinAFEData
    (d : ℕ) [NeZero d] (T sigma Cprim : ℝ) where
  blockCount : ℕ
  mellinHeight : ℝ
  cauchyMass : ℝ
  dual : Fin blockCount → Bool
  length : Fin blockCount → ℕ
  coeff : Fin blockCount → ℝ → ℕ → ℂ
  weight : Fin blockCount → ℝ → ℝ
  mellinHeight_nonneg : 0 ≤ mellinHeight
  cauchyMass_nonneg : 0 ≤ cauchyMass
  length_pos : ∀ j : Fin blockCount, 1 ≤ length j
  coeff_continuous : ∀ (j : Fin blockCount) (n : ℕ),
    Continuous (fun v : ℝ => coeff j v n)
  weight_continuous : ∀ j : Fin blockCount, Continuous (weight j)
  weight_nonneg : ∀ (j : Fin blockCount) (v : ℝ),
    v ∈ Set.Icc (-mellinHeight) mellinHeight → 0 ≤ weight j v
  pointwise : ∀ (chi : DirichletCharacter ℂ d), chi.IsPrimitive →
    ∀ t : ℝ, |t| ≤ T →
      shiftedStripLFourth chi sigma t ≤
        cauchyMass * ramachandraMellinDyadicFamily dual length coeff weight
          mellinHeight chi t
  cost : cauchyMass * ramachandraMellinDyadicFamilyCost d T mellinHeight
      length coeff weight ≤
    Cprim * ((d : ℝ) * T) * Real.log ((d : ℝ) * T) ^ 200

/-- One concrete shifted Mellin construction yields the primitive-family
estimate at that parameter point. -/
theorem primitiveFamilyShiftedFourthIntegral_le_of_mellinAFEData
    {d : ℕ} [NeZero d] {T sigma Cprim : ℝ}
    (hT : 0 ≤ T) (hsigma : sigma ≠ 1)
    (data : PrimitiveShiftedMellinAFEData d T sigma Cprim) :
    primitiveFamilyShiftedFourthIntegral d T sigma ≤
      Cprim * ((d : ℝ) * T) * Real.log ((d : ℝ) * T) ^ 200 := by
  exact (primitiveFamilyShiftedFourthIntegral_le_mellinDyadicCost
    data.dual data.length data.coeff data.weight hT data.mellinHeight_nonneg
      data.cauchyMass_nonneg hsigma data.length_pos data.coeff_continuous
      data.weight_continuous
      data.weight_nonneg data.pointwise).trans data.cost

/-- Uniform construction of the literal shifted Lemmas 3--6 data proves the
primitive source leaf used on p.88.  The remaining premise is now an explicit
AFE construction, not the desired moment under another name. -/
theorem ramachandraPrimitiveShiftedFourthK2_of_mellinAFEConstruction
    {Cprim : ℝ} (hCprim : 0 < Cprim)
    (hconstruct : ∀ (q d : ℕ) [NeZero q] [NeZero d]
      (T sigma : ℝ), d ∣ q → 3 ≤ T →
      |sigma - (1 / 2 : ℝ)| ≤
          (100 * Real.log ((q : ℝ) * T))⁻¹ →
      PrimitiveShiftedMellinAFEData d T sigma Cprim) :
    RamachandraPrimitiveShiftedFourthK2 := by
  refine ⟨Cprim, hCprim, ?_⟩
  intro q d _instq _instd T sigma hdq hT hstrip
  have hsigma := sigma_ne_one_of_ramachandraStrip hT hstrip
  exact primitiveFamilyShiftedFourthIntegral_le_of_mellinAFEData
    (by linarith : 0 ≤ T) hsigma (hconstruct q d T sigma hdq hT hstrip)

end
end RamachandraPrimitiveShiftedMellinReduction

#print axioms RamachandraPrimitiveShiftedMellinReduction.intervalIntegral_intervalIntegral_swap_of_continuous
#print axioms RamachandraPrimitiveShiftedMellinReduction.continuous_uncurry_ramachandraDyadicBlock
#print axioms RamachandraPrimitiveShiftedMellinReduction.allCharacter_doubleIntegral_weightedBlock_le
#print axioms RamachandraPrimitiveShiftedMellinReduction.primitiveFamilyShiftedFourthIntegral_le_mellinDyadicCost
#print axioms RamachandraPrimitiveShiftedMellinReduction.primitiveFamilyShiftedFourthIntegral_le_of_mellinAFEData
#print axioms RamachandraPrimitiveShiftedMellinReduction.ramachandraPrimitiveShiftedFourthK2_of_mellinAFEConstruction
