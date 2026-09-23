import RamachandraShortContourContinuity
import RamachandraShortHeadFamilyBudget
import RamachandraPrimitiveShiftedPackageAdapter

/-!
# Primitive-family moment of the literal short contour

This module performs the source-order Fubini weld for the complete reflected
head and then sums the certified pointwise weighted-Cauchy estimate over the
primitive characters.  The conclusion is an inequality for the actual
`primitiveFamilyShortContourSecondMoment`, not a surrogate block moment.
-/

namespace RamachandraShortContourFamilyMoment

open scoped BigOperators Interval
open Complex MeasureTheory
open BHPRamachandraMeanValueFromDyadicAFE
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShortContourCauchy
open RamachandraShortContourContinuity
open RamachandraShortHeadFamilyBudget
open RamachandraShiftedFunctionalFactorMomentEnvelope
open RamachandraGammaWeightIntegrability
open RamachandraPrimitiveShiftedMellinReduction
open MRTLemma215DyadicPartition
open RamachandraShortFunctionalFactorMomentEnvelope

noncomputable section

set_option maxHeartbeats 1000000

variable {d : ℕ} [NeZero d]

/-- Product integrability for the literal all-character reflected head. -/
theorem integrable_uncurry_allCharacter_shortHead
    (d : ℕ) [NeZero d] {X T sigma : ℝ}
    (hT : 0 ≤ T) (hX : 6 ≤ X)
    (hline : 1 / 2 ≤ 1 - sigma + (Real.log X)⁻¹) :
    Integrable (Function.uncurry (fun t v =>
      gammaPolynomialWeight (-(Real.log X)⁻¹) v *
        ∑ psi : DirichletCharacter ℂ d,
          ‖shortReflectedHead psi X sigma t v‖ ^ 2))
      ((volume.restrict (Set.uIoc (-T) T)).prod volume) := by
  let w : ℝ → ℝ := gammaPolynomialWeight (-(Real.log X)⁻¹)
  let G : ℝ → ℝ := fun v =>
    ∫ t in (-T)..T,
      ∑ psi : DirichletCharacter ℂ d,
        ‖shortReflectedHead psi X sigma t v‖ ^ 2
  let C : ℝ := 4 * (d : ℝ) * T +
    2 * (sourceDyadicCount ⌊X⌋₊ : ℝ) *
      ∑ j : Fin (sourceDyadicCount ⌊X⌋₊),
        shortHeadSourceShellCost d ⌊X⌋₊ T j
  let K : ℝ × ℝ → ℝ := fun z => w z.2 *
    ∑ psi : DirichletCharacter ℂ d,
      ‖shortReflectedHead psi X sigma z.1 z.2‖ ^ 2
  have horder : -T ≤ T := by linarith
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
    apply intervalIntegral.integral_nonneg horder
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
        have hxlt := Nat.lt_floor_add_one X
        rw [h] at hxlt
        norm_num at hxlt
        linarith) rfl hT (by linarith) hline
  have houter : Integrable (fun v => w v * G v) := by
    have hmajor : Integrable (fun v => w v * C) := hwint.mul_const C
    apply hmajor.mono'
    · exact (hwcont.mul hGcont).aestronglyMeasurable
    · filter_upwards with v
      rw [Real.norm_of_nonneg (mul_nonneg (hw0 v) (hG0 v))]
      exact mul_le_mul_of_nonneg_left (hGle v) (hw0 v)
  have hKcont : Continuous K := by
    unfold K
    exact (hwcont.comp continuous_snd).mul (by
      apply continuous_finsetSum
      intro psi hpsi
      exact ((continuous_uncurry_shortReflectedHead psi
        (X := X) (by linarith) sigma).comp continuous_swap).norm.pow 2)
  apply (integrable_prod_iff' hKcont.aestronglyMeasurable).2
  constructor
  · filter_upwards with v
    have hcont : Continuous (fun t => K (t, v)) :=
      hKcont.comp (continuous_id.prodMk continuous_const)
    exact (intervalIntegrable_iff.mp (hcont.intervalIntegrable (-T) T))
  · have hinner : (fun v =>
        ∫ t, ‖K (t, v)‖ ∂(volume.restrict (Set.uIoc (-T) T))) =
        (fun v => w v * G v) := by
      funext v
      rw [Set.uIoc_of_le horder]
      rw [← intervalIntegral.integral_of_le horder]
      have hpoint (t : ℝ) : ‖K (t, v)‖ = K (t, v) := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact mul_nonneg (hw0 v)
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      simp_rw [hpoint]
      dsimp [K, G]
      rw [intervalIntegral.integral_const_mul]
    rw [hinner]
    exact houter

/-- Exact complete-family source-order Fubini identity for the reflected head. -/
theorem sum_intervalIntegral_integral_shortHead_eq
    (d : ℕ) [NeZero d] {X T sigma : ℝ}
    (hT : 0 ≤ T) (hX : 6 ≤ X)
    (hline : 1 / 2 ≤ 1 - sigma + (Real.log X)⁻¹) :
    (∑ psi : DirichletCharacter ℂ d,
      ∫ t in (-T)..T,
        ∫ v : ℝ, gammaPolynomialWeight (-(Real.log X)⁻¹) v *
          ‖shortReflectedHead psi X sigma t v‖ ^ 2) =
      shortHeadAllCharacterMellinMoment d X T sigma := by
  let muT : Measure ℝ := volume.restrict (Set.uIoc (-T) T)
  let w : ℝ → ℝ := gammaPolynomialWeight (-(Real.log X)⁻¹)
  let K : ℝ × ℝ → ℝ := fun z => w z.2 *
    ∑ psi : DirichletCharacter ℂ d,
      ‖shortReflectedHead psi X sigma z.1 z.2‖ ^ 2
  let Kpsi : DirichletCharacter ℂ d → ℝ × ℝ → ℝ := fun psi z =>
    w z.2 * ‖shortReflectedHead psi X sigma z.1 z.2‖ ^ 2
  have hlog : 1 < Real.log X :=
    RamachandraShiftedDirectParameters.one_lt_log_of_three_le (by linarith)
  have hcLo : -1 < -(Real.log X)⁻¹ := by
    have hi : (Real.log X)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).2 hlog
    linarith
  have hcHi : -(Real.log X)⁻¹ < 0 := by
    have hi : 0 < (Real.log X)⁻¹ := inv_pos.mpr (by linarith)
    linarith
  have hwcont : Continuous w := continuous_gammaPolynomialWeight hcLo hcHi
  have hw0 (v : ℝ) : 0 ≤ w v := gammaPolynomialWeight_nonneg _ _
  have hprod : Integrable K (muT.prod volume) := by
    simpa only [K, w, muT, Function.uncurry] using!
      integrable_uncurry_allCharacter_shortHead d hT hX hline
  have hterm (psi : DirichletCharacter ℂ d) :
      Integrable (Kpsi psi) (muT.prod volume) := by
    apply hprod.mono
    · unfold Kpsi
      exact ((hwcont.comp continuous_snd).mul
        (((continuous_uncurry_shortReflectedHead psi
          (X := X) (by linarith) sigma).comp continuous_swap).norm.pow 2)).aestronglyMeasurable
    · filter_upwards with z
      have hsingle : ‖shortReflectedHead psi X sigma z.1 z.2‖ ^ 2 ≤
          ∑ chi : DirichletCharacter ℂ d,
            ‖shortReflectedHead chi X sigma z.1 z.2‖ ^ 2 :=
        Finset.single_le_sum
          (s := (Finset.univ : Finset (DirichletCharacter ℂ d)))
          (f := fun chi => ‖shortReflectedHead chi X sigma z.1 z.2‖ ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ psi)
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hw0 z.2) (sq_nonneg _)),
        Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hw0 z.2)
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
      exact mul_le_mul_of_nonneg_left hsingle (hw0 z.2)
  have houterTerm (psi : DirichletCharacter ℂ d) :
      IntervalIntegrable (fun t => ∫ v : ℝ, Kpsi psi (t, v))
        volume (-T) T := by
    rw [intervalIntegrable_iff]
    simpa only [muT] using! (hterm psi).integral_prod_left
  have hswap :
      (∫ t in (-T)..T, ∫ v : ℝ, K (t, v)) =
        ∫ v : ℝ, w v *
          (∫ t in (-T)..T,
            ∑ psi : DirichletCharacter ℂ d,
              ‖shortReflectedHead psi X sigma t v‖ ^ 2) := by
    change Integrable (Function.uncurry (fun t v => K (t, v)))
      (muT.prod volume) at hprod
    simpa only [K, muT, Function.uncurry,
      intervalIntegral.integral_const_mul] using
      (MeasureTheory.intervalIntegral_integral_swap hprod)
  have hsections : ∀ᵐ t ∂muT,
      ∀ psi : DirichletCharacter ℂ d,
        Integrable (fun v => Kpsi psi (t, v)) :=
    eventually_countable_forall.mpr (fun psi => (hterm psi).prod_right_ae)
  have hcollapse :
      (∫ t in (-T)..T, ∫ v : ℝ, K (t, v)) =
        ∫ t in (-T)..T,
          ∑ psi : DirichletCharacter ℂ d, ∫ v : ℝ, Kpsi psi (t, v) := by
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [hsections] with t ht
    have hsum := MeasureTheory.integral_finsetSum Finset.univ
      (fun psi hpsi => ht psi)
    simpa only [K, Kpsi, ← Finset.mul_sum] using hsum
  calc
    (∑ psi : DirichletCharacter ℂ d,
      ∫ t in (-T)..T,
        ∫ v : ℝ, gammaPolynomialWeight (-(Real.log X)⁻¹) v *
          ‖shortReflectedHead psi X sigma t v‖ ^ 2) =
        ∫ t in (-T)..T,
          ∑ psi : DirichletCharacter ℂ d,
            ∫ v : ℝ, Kpsi psi (t, v) := by
      symm
      simpa only [Kpsi, w] using
        (intervalIntegral.integral_finsetSum
          (s := (Finset.univ : Finset (DirichletCharacter ℂ d)))
          (fun psi hpsi => houterTerm psi))
    _ = ∫ t in (-T)..T, ∫ v : ℝ, K (t, v) := hcollapse.symm
    _ = ∫ v : ℝ, w v *
          (∫ t in (-T)..T,
            ∑ psi : DirichletCharacter ℂ d,
              ‖shortReflectedHead psi X sigma t v‖ ^ 2) := hswap
    _ = shortHeadAllCharacterMellinMoment d X T sigma := by
      rfl

/-- The actual primitive-family short-contour moment is bounded by the complete
head moment.  Both integrals are the literal whole Mellin line. -/
theorem primitiveFamilyShortContourSecondMoment_le_headMoment
    (d : ℕ) [NeZero d] {T sigma : ℝ}
    (hT : 3 ≤ T) (hX : 6 ≤ primitiveShiftedScale d T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log (primitiveShiftedScale d T))⁻¹)
    (hline : 1 / 2 ≤ 1 - sigma +
      (Real.log (primitiveShiftedScale d T))⁻¹) :
    primitiveFamilyShortContourSecondMoment d T sigma ≤
      (∫ v : ℝ, gammaPolynomialWeight
        (-(Real.log (primitiveShiftedScale d T))⁻¹) v) *
      shortFunctionalMomentConstant *
        shortHeadAllCharacterMellinMoment d
          (primitiveShiftedScale d T) T sigma := by
  classical
  let X := primitiveShiftedScale d T
  let W : ℝ := ∫ v : ℝ, gammaPolynomialWeight (-(Real.log X)⁻¹) v
  let Kpsi : DirichletCharacter ℂ d → ℝ → ℝ := fun psi t =>
    ∫ v : ℝ, gammaPolynomialWeight (-(Real.log X)⁻¹) v *
      ‖shortReflectedHead psi X sigma t v‖ ^ 2
  have hW0 : 0 ≤ W := integral_nonneg (fun _ => gammaPolynomialWeight_nonneg _ _)
  have hC0 : 0 ≤ shortFunctionalMomentConstant :=
    shortFunctionalMomentConstant_nonneg
  have hpsi (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive) :
      (∫ t in (-T)..T, ‖primitiveShiftedShortContour psi T sigma t‖ ^ 2) ≤
        W * shortFunctionalMomentConstant *
          ∫ t in (-T)..T, Kpsi psi t := by
    have hcont := continuous_primitiveShiftedShortContour psi hT hX hstrip
    have hleft : IntervalIntegrable
        (fun t => ‖primitiveShiftedShortContour psi T sigma t‖ ^ 2)
        volume (-T) T := (hcont.norm.pow 2).intervalIntegrable _ _
    let muT : Measure ℝ := volume.restrict (Set.uIoc (-T) T)
    let Kprod : ℝ × ℝ → ℝ := fun z =>
      gammaPolynomialWeight (-(Real.log X)⁻¹) z.2 *
        ∑ chi : DirichletCharacter ℂ d,
          ‖shortReflectedHead chi X sigma z.1 z.2‖ ^ 2
    let KprodPsi : ℝ × ℝ → ℝ := fun z =>
      gammaPolynomialWeight (-(Real.log X)⁻¹) z.2 *
        ‖shortReflectedHead psi X sigma z.1 z.2‖ ^ 2
    have hprod : Integrable Kprod (muT.prod volume) := by
      simpa only [Kprod, muT, Function.uncurry] using!
        integrable_uncurry_allCharacter_shortHead d (by linarith)
          (by simpa [X] using hX) (by simpa [X] using hline)
    have hterm : Integrable KprodPsi (muT.prod volume) := by
      apply hprod.mono
      · unfold KprodPsi
        have hlog : 1 < Real.log X :=
          RamachandraShiftedDirectParameters.one_lt_log_of_three_le
            (by dsimp [X]; linarith)
        have hcLo : -1 < -(Real.log X)⁻¹ := by
          have hi : (Real.log X)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).2 hlog
          linarith
        have hcHi : -(Real.log X)⁻¹ < 0 := by
          have hi : 0 < (Real.log X)⁻¹ := inv_pos.mpr (by linarith)
          linarith
        exact (((continuous_gammaPolynomialWeight hcLo hcHi).comp continuous_snd).mul
          (((continuous_uncurry_shortReflectedHead psi
            (X := X) (by dsimp [X]; linarith) sigma).comp continuous_swap).norm.pow 2))
              |>.aestronglyMeasurable
      · filter_upwards with z
        have hsingle : ‖shortReflectedHead psi X sigma z.1 z.2‖ ^ 2 ≤
            ∑ chi : DirichletCharacter ℂ d,
              ‖shortReflectedHead chi X sigma z.1 z.2‖ ^ 2 :=
          Finset.single_le_sum
            (s := (Finset.univ : Finset (DirichletCharacter ℂ d)))
            (f := fun chi => ‖shortReflectedHead chi X sigma z.1 z.2‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ psi)
        have hw0 := gammaPolynomialWeight_nonneg (-(Real.log X)⁻¹) z.2
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg hw0 (sq_nonneg _)),
          Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg hw0
            (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
        exact mul_le_mul_of_nonneg_left hsingle hw0
    have hright : IntervalIntegrable
        (fun t => W * shortFunctionalMomentConstant * Kpsi psi t)
        volume (-T) T := by
      have hsec : IntervalIntegrable (Kpsi psi) volume (-T) T := by
        rw [intervalIntegrable_iff]
        have hleftSec := hterm.integral_prod_left
        simpa only [KprodPsi, Kpsi, muT] using! hleftSec
      exact hsec.const_mul _
    have hmono : (∫ t in (-T)..T,
        ‖primitiveShiftedShortContour psi T sigma t‖ ^ 2) ≤
        ∫ t in (-T)..T, W * shortFunctionalMomentConstant * Kpsi psi t := by
      apply intervalIntegral.integral_mono_on (by linarith) hleft hright
      intro t ht
      have htAbs : |t| ≤ T := (abs_le).2 ⟨by linarith [ht.1], ht.2⟩
      have hpoint := norm_primitiveShiftedShortContour_sq_le
        psi hprim hT hX hstrip htAbs
      dsimp [W, Kpsi, X]
      calc
        _ ≤ (∫ v : ℝ, gammaPolynomialWeight
            (-(Real.log (primitiveShiftedScale d T))⁻¹) v) *
          ∫ v : ℝ, shortFunctionalMomentConstant *
            gammaPolynomialWeight
              (-(Real.log (primitiveShiftedScale d T))⁻¹) v *
              ‖shortReflectedHead psi (primitiveShiftedScale d T) sigma t v‖ ^ 2 := hpoint
        _ = _ := by
          have heq : (∫ v : ℝ, shortFunctionalMomentConstant *
                gammaPolynomialWeight
                  (-(Real.log (primitiveShiftedScale d T))⁻¹) v *
                ‖shortReflectedHead psi (primitiveShiftedScale d T) sigma t v‖ ^ 2) =
              shortFunctionalMomentConstant *
                ∫ v : ℝ, gammaPolynomialWeight
                  (-(Real.log (primitiveShiftedScale d T))⁻¹) v *
                ‖shortReflectedHead psi (primitiveShiftedScale d T) sigma t v‖ ^ 2 := by
            rw [← MeasureTheory.integral_const_mul]
            apply MeasureTheory.integral_congr_ae
            filter_upwards with v
            ring
          rw [heq]
          ring
    calc
      _ ≤ ∫ t in (-T)..T, W * shortFunctionalMomentConstant * Kpsi psi t := hmono
      _ = W * shortFunctionalMomentConstant * ∫ t in (-T)..T, Kpsi psi t := by
        rw [intervalIntegral.integral_const_mul]
  unfold primitiveFamilyShortContourSecondMoment
  calc
    (∑ psi : DirichletCharacter ℂ d,
      if psi.IsPrimitive then
        ∫ t in (-T)..T, ‖primitiveShiftedShortContour psi T sigma t‖ ^ 2
      else 0) ≤
      ∑ psi : DirichletCharacter ℂ d,
        W * shortFunctionalMomentConstant *
          ∫ t in (-T)..T, Kpsi psi t := by
      apply Finset.sum_le_sum
      intro psi hmem
      split_ifs with hp
      · exact hpsi psi hp
      · exact mul_nonneg (mul_nonneg hW0 hC0)
          (intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by
            unfold Kpsi
            exact integral_nonneg (fun _ => mul_nonneg
              (gammaPolynomialWeight_nonneg _ _) (sq_nonneg _))))
    _ = W * shortFunctionalMomentConstant *
        ∑ psi : DirichletCharacter ℂ d,
          ∫ t in (-T)..T, Kpsi psi t := by
      rw [Finset.mul_sum]
    _ = W * shortFunctionalMomentConstant *
        shortHeadAllCharacterMellinMoment d X T sigma := by
      rw [sum_intervalIntegral_integral_shortHead_eq d
        (by linarith) (by simpa [X] using hX) (by simpa [X] using hline)]
    _ = _ := by rfl

end
end RamachandraShortContourFamilyMoment

#print axioms RamachandraShortContourFamilyMoment.integrable_uncurry_allCharacter_shortHead
#print axioms RamachandraShortContourFamilyMoment.sum_intervalIntegral_integral_shortHead_eq
#print axioms RamachandraShortContourFamilyMoment.primitiveFamilyShortContourSecondMoment_le_headMoment
