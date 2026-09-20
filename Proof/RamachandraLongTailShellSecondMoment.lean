import RamachandraLongTailShellCauchy
import RamachandraFullLineReflectedBlockFubini
import RamachandraLongGammaUniformMass

/-!
# Primitive-family second moment of one exact long-tail shell

This module performs the complete continuous weighted-Cauchy/Fubini weld for
one standard dyadic cell.  The result is deliberately prior to the infinite
shell summation: every analytic operation in `t` and `v` is discharged here,
leaving only a nonnegative scalar dyadic series.
-/

namespace RamachandraLongTailShellSecondMoment

open scoped BigOperators Interval
open Complex MeasureTheory
open RamachandraPrimitiveShiftedContourReduction
open RamachandraLongTailShellCauchy
open RamachandraShiftedFunctionalFactorMomentEnvelope
open RamachandraGammaWeightIntegrability
open RamachandraShiftedReflectedTailInfiniteAssembly
open RamachandraShiftedReflectedSeries
open RamachandraFullLineReflectedBlockBudget
open RamachandraFullLineReflectedBlockFubini
open RamachandraPrimitiveShiftedMellinReduction
open BHPAllCharacterDyadicBudget
open MontgomeryVaughanFiniteReduction

noncomputable section

set_option maxHeartbeats 1000000

variable {d : ℕ} [NeZero d]

/-- The exact source-order second moment of one integrated tail shell,
restricted to primitive characters. -/
def primitiveLongTailShellSecondMoment
    (d : ℕ) [NeZero d] (X T sigma : ℝ) (j : ℕ) : ℝ := by
  classical
  exact ∑ psi : DirichletCharacter ℂ d,
    if psi.IsPrimitive then
      ∫ t in (-T)..T,
        ‖∫ v : ℝ, longTailShellIntegrand psi X sigma t j v‖ ^ 2
    else 0

private theorem one_add_abs_pow_three_le
    {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) :
    (1 + |t|) ^ 3 ≤ (1 + T) ^ 3 := by
  gcongr

/-- One complete dyadic cell after weighted Cauchy, primitive restriction,
Fubini, character orthogonality, and the sharp quarter-line coefficient
energy.  No compact Mellin cutoff occurs in the statement. -/
theorem primitiveLongTailShellSecondMoment_le
    (d : ℕ) [NeZero d] {X T sigma : ℝ} (hX : 0 < X)
    (hT : 0 ≤ T)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ) :
    primitiveLongTailShellSecondMoment d X T sigma j ≤
      (∫ v : ℝ, gammaPolynomialWeight (-(sigma + 1 / 4)) v) ^ 2 *
        (longFunctionalMomentConstant * (d : ℝ) ^ 3 *
          Real.rpow X (-2 * (sigma + 1 / 4)) * (1 + T) ^ 3) *
        (((d : ℝ) * (2 * T) + 8 * Real.pi * ((2 ^ j : ℕ) : ℝ)) *
          (Real.rpow ((2 ^ j : ℕ) : ℝ) (-(3 / 2 : ℝ)) *
            (harmonic (2 * (2 ^ j)) : ℝ) ^ 4)) := by
  classical
  let N : ℕ := 2 ^ j
  let b : ℝ → ℕ → ℂ := fun v =>
    reflectedTailInfiniteShellCoeff X sigma (-(sigma + 1 / 4)) v
  let w : ℝ → ℝ := gammaPolynomialWeight (-(sigma + 1 / 4))
  let W : ℝ := ∫ v : ℝ, w v
  let E : ℝ := Real.rpow (N : ℝ) (-(3 / 2 : ℝ)) *
    (harmonic (2 * N) : ℝ) ^ 4
  let A : ℝ := longFunctionalMomentConstant * (d : ℝ) ^ 3 *
    Real.rpow X (-2 * (sigma + 1 / 4)) * (1 + T) ^ 3
  have hN : 1 ≤ N := by
    dsimp [N]
    exact one_le_pow₀ (by norm_num)
  have hE : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg longFunctionalMomentConstant_nonneg (by positivity))
        (Real.rpow_nonneg hX.le _)) (by positivity)
  have hW : 0 ≤ W := by
    dsimp [W, w]
    exact integral_nonneg (fun v => gammaPolynomialWeight_nonneg _ _)
  have hwcont : Continuous w := continuous_gammaPolynomialWeight hcLo hcHi
  have hwint : Integrable w := integrable_gammaPolynomialWeight hcLo hcHi
  have hw0 (v : ℝ) : 0 ≤ w v := gammaPolynomialWeight_nonneg _ _
  have hbcont : ∀ n, Continuous (fun v => b v n) := fun n =>
    continuous_reflectedTailInfiniteShellCoeff
      X sigma (-(sigma + 1 / 4)) n
  have henergy (v : ℝ) : coefficientEnergy (b v) N ≤ E := by
    dsimp [b, E]
    exact (coefficientEnergy_reflectedTailInfiniteShellCoeff_le
      X sigma (-(sigma + 1 / 4)) v N).trans
        (coefficientEnergy_quarterLineReflectedBlockCoeff_le N hN sigma v)
  let muT : Measure ℝ := volume.restrict (Set.uIoc (-T) T)
  let Kpsi : DirichletCharacter ℂ d → ℝ × ℝ → ℝ := fun psi z =>
    w z.2 * ‖ramachandraDyadicBlock d N (b z.2) true psi z.1‖ ^ 2
  have hprodAll : Integrable (Function.uncurry (fun t v =>
      w v * ∑ psi : DirichletCharacter ℂ d,
        ‖ramachandraDyadicBlock d N (b v) true psi t‖ ^ 2))
      (muT.prod volume) := by
    simpa only [muT] using
      (integrable_uncurry_allCharacter_weightedBlock
        d N hN hT hE b hbcont henergy w hwcont hwint hw0)
  have hterm (psi : DirichletCharacter ℂ d) :
      Integrable (Kpsi psi) (muT.prod volume) := by
    apply hprodAll.mono
    · unfold Kpsi
      exact ((hwcont.comp continuous_snd).mul
        ((continuous_uncurry_ramachandraDyadicBlock
          d N true b hbcont psi).norm.pow 2)).aestronglyMeasurable
    · filter_upwards with z
      dsimp only [Kpsi, Function.uncurry]
      have hsingle :
          ‖ramachandraDyadicBlock d N (b z.2) true psi z.1‖ ^ 2 ≤
            ∑ chi : DirichletCharacter ℂ d,
              ‖ramachandraDyadicBlock d N (b z.2) true chi z.1‖ ^ 2 :=
        Finset.single_le_sum
          (s := (Finset.univ : Finset (DirichletCharacter ℂ d)))
          (f := fun chi =>
            ‖ramachandraDyadicBlock d N (b z.2) true chi z.1‖ ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ psi)
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hw0 z.2) (sq_nonneg _)),
        Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hw0 z.2)
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
      exact mul_le_mul_of_nonneg_left hsingle (hw0 z.2)
  have hHInt (psi : DirichletCharacter ℂ d) :
      IntervalIntegrable (fun t => ∫ v : ℝ, Kpsi psi (t, v))
        volume (-T) T := by
    rw [intervalIntegrable_iff]
    simpa only [muT] using (hterm psi).integral_prod_left
  have hcontourMeas (psi : DirichletCharacter ℂ d) :
      StronglyMeasurable (fun t =>
        ∫ v : ℝ, longTailShellIntegrand psi X sigma t j v) :=
    (continuous_uncurry_longTailShellIntegrand psi hX hcLo hcHi j).stronglyMeasurable
      |>.integral_prod_right'
  have hpsi (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive) :
      (∫ t in (-T)..T,
        ‖∫ v : ℝ, longTailShellIntegrand psi X sigma t j v‖ ^ 2) ≤
        W * A * ∫ t in (-T)..T, ∫ v : ℝ, Kpsi psi (t, v) := by
    let F : ℝ → ℝ := fun t =>
      ‖∫ v : ℝ, longTailShellIntegrand psi X sigma t j v‖ ^ 2
    let G : ℝ → ℝ := fun t => W * A * ∫ v : ℝ, Kpsi psi (t, v)
    have hGI : IntervalIntegrable G volume (-T) T := by
      dsimp [G]
      exact (hHInt psi).const_mul (W * A)
    have hFmeas : AEStronglyMeasurable F := by
      exact ((hcontourMeas psi).norm.pow 2).aestronglyMeasurable
    have hFG : ∀ t ∈ Set.uIcc (-T) T, F t ≤ G t := by
      intro t ht
      have htabs : |t| ≤ T := by
        rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at ht
        exact (abs_le).2 ⟨by linarith [ht.1], ht.2⟩
      have hshell := norm_integral_longTailShell_sq_le_certified
        psi hprim (t := t) hX hcLo hcHi j
      have hAt : longFunctionalMomentConstant * (d : ℝ) ^ 3 *
          Real.rpow X (-2 * (sigma + 1 / 4)) * (1 + |t|) ^ 3 ≤ A := by
        dsimp [A]
        have hbase : (1 + |t|) ^ 3 ≤ (1 + T) ^ 3 :=
          one_add_abs_pow_three_le hT htabs
        have hfac0 : 0 ≤ longFunctionalMomentConstant * (d : ℝ) ^ 3 *
            Real.rpow X (-2 * (sigma + 1 / 4)) := by
          exact mul_nonneg
            (mul_nonneg longFunctionalMomentConstant_nonneg (by positivity))
            (Real.rpow_nonneg hX.le _)
        exact mul_le_mul_of_nonneg_left hbase hfac0
      have hinner0 : 0 ≤ ∫ v : ℝ, w v *
          ‖ramachandraReflectedTailDyadicShell psi X
            (RamachandraShiftedContourSharpEnvelopes.longFunctionalPoint
              sigma t v) j‖ ^ 2 := by
        apply integral_nonneg
        intro v
        exact mul_nonneg (hw0 v) (sq_nonneg _)
      calc
        F t ≤ W * ∫ v : ℝ,
            (longFunctionalMomentConstant * (d : ℝ) ^ 3 *
                Real.rpow X (-2 * (sigma + 1 / 4)) * (1 + |t|) ^ 3) *
              w v *
              ‖ramachandraReflectedTailDyadicShell psi X
                (RamachandraShiftedContourSharpEnvelopes.longFunctionalPoint
                  sigma t v) j‖ ^ 2 := by
          simpa [F, W, w, mul_assoc] using hshell
        _ = W *
            ((longFunctionalMomentConstant * (d : ℝ) ^ 3 *
                Real.rpow X (-2 * (sigma + 1 / 4)) * (1 + |t|) ^ 3) *
              ∫ v : ℝ, w v *
                ‖ramachandraReflectedTailDyadicShell psi X
                  (RamachandraShiftedContourSharpEnvelopes.longFunctionalPoint
                    sigma t v) j‖ ^ 2) := by
          let C₀ : ℝ := longFunctionalMomentConstant * (d : ℝ) ^ 3 *
            Real.rpow X (-2 * (sigma + 1 / 4)) * (1 + |t|) ^ 3
          let R₀ : ℝ → ℝ := fun v => w v *
            ‖ramachandraReflectedTailDyadicShell psi X
              (RamachandraShiftedContourSharpEnvelopes.longFunctionalPoint
                sigma t v) j‖ ^ 2
          have hint : (∫ v : ℝ,
              (longFunctionalMomentConstant * (d : ℝ) ^ 3 *
                Real.rpow X (-2 * (sigma + 1 / 4)) * (1 + |t|) ^ 3) *
                w v *
                ‖ramachandraReflectedTailDyadicShell psi X
                  (RamachandraShiftedContourSharpEnvelopes.longFunctionalPoint
                    sigma t v) j‖ ^ 2) = ∫ v : ℝ, C₀ * R₀ v := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with v
            dsimp [C₀, R₀]
            ring
          rw [hint, MeasureTheory.integral_const_mul]
        _ ≤ W * (A * ∫ v : ℝ, w v *
              ‖ramachandraReflectedTailDyadicShell psi X
                (RamachandraShiftedContourSharpEnvelopes.longFunctionalPoint
                  sigma t v) j‖ ^ 2) := by
          gcongr
        _ = G t := by
          have heq (v : ℝ) :
              ramachandraReflectedTailDyadicShell psi X
                  (RamachandraShiftedContourSharpEnvelopes.longFunctionalPoint
                    sigma t v) j =
                ramachandraDyadicBlock d N (b v) true psi t := by
            dsimp [N, b]
            rw [show RamachandraShiftedContourSharpEnvelopes.longFunctionalPoint
                  sigma t v =
                ramachandraShiftedPoint sigma t +
                  (((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I) by
              apply Complex.ext <;>
                simp [RamachandraShiftedContourSharpEnvelopes.longFunctionalPoint,
                  ramachandraShiftedPoint] <;> ring]
            exact ramachandraReflectedTailDyadicShell_eq_ramachandraDyadicBlock
              psi X sigma (-(sigma + 1 / 4)) v t j
          simp_rw [heq]
          dsimp [G, Kpsi]
          ring
    have hFI : IntervalIntegrable F volume (-T) T := by
      rw [intervalIntegrable_iff]
      apply (intervalIntegrable_iff.mp hGI).mono' hFmeas.restrict
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      apply hFG t
      rw [Set.uIoc_of_le (by linarith : -T ≤ T)] at ht
      rw [Set.uIcc_of_le (by linarith : -T ≤ T)]
      exact ⟨ht.1.le, ht.2⟩
    calc
      (∫ t in (-T)..T,
        ‖∫ v : ℝ, longTailShellIntegrand psi X sigma t j v‖ ^ 2) =
          ∫ t in (-T)..T, F t := rfl
      _ ≤ ∫ t in (-T)..T, G t :=
        intervalIntegral.integral_mono_on (by linarith) hFI hGI
          (fun t ht => hFG t (by
            rw [Set.uIcc_of_le (by linarith : -T ≤ T)]
            exact ⟨ht.1, ht.2⟩))
      _ = W * A * ∫ t in (-T)..T, ∫ v : ℝ, Kpsi psi (t, v) := by
        dsimp [G]
        rw [intervalIntegral.integral_const_mul]
  have hsumPrim : primitiveLongTailShellSecondMoment d X T sigma j ≤
      W * A * ∑ psi : DirichletCharacter ℂ d,
        ∫ t in (-T)..T, ∫ v : ℝ, Kpsi psi (t, v) := by
    unfold primitiveLongTailShellSecondMoment
    calc
      (∑ psi : DirichletCharacter ℂ d,
        if psi.IsPrimitive then
          ∫ t in (-T)..T,
            ‖∫ v : ℝ, longTailShellIntegrand psi X sigma t j v‖ ^ 2
        else 0) ≤
          ∑ psi : DirichletCharacter ℂ d,
            if psi.IsPrimitive then
              W * A * ∫ t in (-T)..T, ∫ v : ℝ, Kpsi psi (t, v)
            else 0 := by
        apply Finset.sum_le_sum
        intro psi hmem
        by_cases hp : psi.IsPrimitive
        · simpa [hp] using hpsi psi hp
        · simp [hp]
      _ ≤ ∑ psi : DirichletCharacter ℂ d,
          W * A * ∫ t in (-T)..T, ∫ v : ℝ, Kpsi psi (t, v) := by
        apply Finset.sum_le_sum
        intro psi hmem
        by_cases hp : psi.IsPrimitive
        · simp [hp]
        · simp only [hp, if_false]
          have hinner : 0 ≤ ∫ t in (-T)..T,
              ∫ v : ℝ, Kpsi psi (t, v) := by
            rw [intervalIntegral.integral_of_le (by linarith)]
            exact integral_nonneg (fun t => integral_nonneg (fun v => by
              dsimp [Kpsi]
              exact mul_nonneg (hw0 v) (sq_nonneg _)))
          exact mul_nonneg (mul_nonneg hW hA) hinner
      _ = W * A * ∑ psi : DirichletCharacter ℂ d,
          ∫ t in (-T)..T, ∫ v : ℝ, Kpsi psi (t, v) := by
        rw [Finset.mul_sum]
  have hswap :
      (∑ psi : DirichletCharacter ℂ d,
        ∫ t in (-T)..T, ∫ v : ℝ, Kpsi psi (t, v)) =
        ∫ v : ℝ, w v *
          (∫ t in (-T)..T,
            ∑ psi : DirichletCharacter ℂ d,
              ‖ramachandraDyadicBlock d N (b v) true psi t‖ ^ 2) := by
    simpa only [Kpsi] using
      (sum_intervalIntegral_integral_weightedBlock_eq
        d N hN hT hE b hbcont henergy w hwcont hwint hw0)
  have hblock := integral_allCharacter_intervalIntegral_weightedBlock_le
    d N hN hT hE b hbcont henergy w hwcont hwint hw0
  calc
    primitiveLongTailShellSecondMoment d X T sigma j ≤
        W * A * ∑ psi : DirichletCharacter ℂ d,
          ∫ t in (-T)..T, ∫ v : ℝ, Kpsi psi (t, v) := hsumPrim
    _ = W * A * (∫ v : ℝ, w v *
          (∫ t in (-T)..T,
            ∑ psi : DirichletCharacter ℂ d,
              ‖ramachandraDyadicBlock d N (b v) true psi t‖ ^ 2)) := by
      rw [hswap]
    _ ≤ W * A *
        (W * (((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) * E)) := by
      exact mul_le_mul_of_nonneg_left hblock (mul_nonneg hW hA)
    _ = W ^ 2 * A *
        (((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) * E) := by ring
    _ = _ := by rfl

end
end RamachandraLongTailShellSecondMoment

#print axioms RamachandraLongTailShellSecondMoment.primitiveLongTailShellSecondMoment_le
