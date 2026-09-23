import RamachandraFullLineReflectedBlockBudget

/-!
# Honest whole-line Fubini bridge for Ramachandra reflected blocks

The full-line block budget is naturally proved with the Mellin ordinate `v`
outside.  The source contour has the opposite order.  This file proves the
required interchange from product-space integrability.  In particular, the
interchange is not stored as a hypothesis and is not justified merely by a
formal rewriting of the two iterated integrals.
-/

namespace RamachandraFullLineReflectedBlockFubini

open scoped BigOperators Interval
open Complex MeasureTheory
open BHPAllCharacterDyadicBudget
open RamachandraPrimitiveShiftedMellinReduction
open MontgomeryVaughanFiniteReduction

noncomputable section

/-- The all-character weighted block is integrable on the literal product of
the finite `t` interval and the complete Mellin line.  This is the analytic
premise needed by Fubini. -/
theorem integrable_uncurry_allCharacter_weightedBlock
    (d N : ℕ) [NeZero d] (hN : 1 ≤ N)
    {T E : ℝ} (hT : 0 ≤ T) (hE : 0 ≤ E)
    (b : ℝ → ℕ → ℂ) (hb : ∀ n, Continuous (fun v => b v n))
    (henergy : ∀ v, coefficientEnergy (b v) N ≤ E)
    (weight : ℝ → ℝ) (hweight : Continuous weight)
    (hweightInt : Integrable weight) (hweight0 : ∀ v, 0 ≤ weight v) :
    Integrable (Function.uncurry (fun t v =>
      weight v * ∑ psi : DirichletCharacter ℂ d,
        ‖ramachandraDyadicBlock d N (b v) true psi t‖ ^ 2))
      ((volume.restrict (Set.uIoc (-T) T)).prod volume) := by
  let F : ℝ := (d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)
  let G : ℝ → ℝ := fun v =>
    ∫ t in (-T)..T,
      ∑ psi : DirichletCharacter ℂ d,
        ‖ramachandraDyadicBlock d N (b v) true psi t‖ ^ 2
  let K : ℝ × ℝ → ℝ := fun z =>
    weight z.2 * ∑ psi : DirichletCharacter ℂ d,
      ‖ramachandraDyadicBlock d N (b z.2) true psi z.1‖ ^ 2
  have horder : -T ≤ T := by linarith
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hGcont : Continuous G := by
    unfold G
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    apply continuous_finsetSum
    intro psi hpsi
    exact (continuous_uncurry_ramachandraDyadicBlock
      d N true b hb psi).comp continuous_swap |>.norm.pow 2
  have hG0 (v : ℝ) : 0 ≤ G v := by
    unfold G
    apply intervalIntegral.integral_nonneg horder
    intro t ht
    positivity
  have hGle (v : ℝ) : G v ≤ F * E := by
    have hmean := integral_sum_norm_ramachandraDyadicBlock_sq_le
      d N hN (b v) true hT
    calc
      G v ≤ ramachandraDyadicCost d N T (b v) := by
        simpa [G] using hmean
      _ ≤ F * E := by
        unfold ramachandraDyadicCost
        exact mul_le_mul_of_nonneg_left (henergy v) hF
  have houter : Integrable (fun v => weight v * G v) := by
    have hmajor : Integrable (fun v => weight v * (F * E)) :=
      hweightInt.mul_const (F * E)
    apply hmajor.mono'
    · exact (hweight.mul hGcont).aestronglyMeasurable
    · filter_upwards with v
      rw [Real.norm_of_nonneg (mul_nonneg (hweight0 v) (hG0 v))]
      exact mul_le_mul_of_nonneg_left (hGle v) (hweight0 v)
  have hKcont : Continuous K := by
    unfold K
    exact (hweight.comp continuous_snd).mul (by
      apply continuous_finsetSum
      intro psi hpsi
      exact (continuous_uncurry_ramachandraDyadicBlock
        d N true b hb psi).norm.pow 2)
  apply (integrable_prod_iff' hKcont.aestronglyMeasurable).2
  constructor
  · filter_upwards with v
    have hcont : Continuous (fun t => K (t, v)) :=
      hKcont.comp (continuous_id.prodMk continuous_const)
    exact (intervalIntegrable_iff.mp (hcont.intervalIntegrable (-T) T))
  · have hinner : (fun v =>
        ∫ t, ‖K (t, v)‖ ∂(volume.restrict (Set.uIoc (-T) T))) =
        (fun v => weight v * G v) := by
      funext v
      rw [Set.uIoc_of_le horder]
      rw [← intervalIntegral.integral_of_le horder]
      have hpoint (t : ℝ) : ‖K (t, v)‖ = K (t, v) :=
        by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact mul_nonneg (hweight0 v)
            (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      simp_rw [hpoint]
      dsimp [K, G]
      rw [intervalIntegral.integral_const_mul]
    rw [hinner]
    exact houter

/-- Exact source-order/mean-square-order interchange for the complete
character family.  The proof first establishes product integrability above,
then invokes Fubini. -/
theorem intervalIntegral_integral_allCharacter_weightedBlock_eq
    (d N : ℕ) [NeZero d] (hN : 1 ≤ N)
    {T E : ℝ} (hT : 0 ≤ T) (hE : 0 ≤ E)
    (b : ℝ → ℕ → ℂ) (hb : ∀ n, Continuous (fun v => b v n))
    (henergy : ∀ v, coefficientEnergy (b v) N ≤ E)
    (weight : ℝ → ℝ) (hweight : Continuous weight)
    (hweightInt : Integrable weight) (hweight0 : ∀ v, 0 ≤ weight v) :
    (∫ t in (-T)..T,
      ∫ v : ℝ, weight v * ∑ psi : DirichletCharacter ℂ d,
        ‖ramachandraDyadicBlock d N (b v) true psi t‖ ^ 2) =
      ∫ v : ℝ, weight v *
        (∫ t in (-T)..T,
          ∑ psi : DirichletCharacter ℂ d,
            ‖ramachandraDyadicBlock d N (b v) true psi t‖ ^ 2) := by
  have hprod := integrable_uncurry_allCharacter_weightedBlock
    d N hN hT hE b hb henergy weight hweight hweightInt hweight0
  simpa only [Function.uncurry, intervalIntegral.integral_const_mul] using
    (MeasureTheory.intervalIntegral_integral_swap hprod)

/-- The literal source formulation: sum over characters, then the finite
`t`-integral, then the whole Mellin line.  Every use of linearity below is
backed by the corresponding section of an integrable product function. -/
theorem sum_intervalIntegral_integral_weightedBlock_eq
    (d N : ℕ) [NeZero d] (hN : 1 ≤ N)
    {T E : ℝ} (hT : 0 ≤ T) (hE : 0 ≤ E)
    (b : ℝ → ℕ → ℂ) (hb : ∀ n, Continuous (fun v => b v n))
    (henergy : ∀ v, coefficientEnergy (b v) N ≤ E)
    (weight : ℝ → ℝ) (hweight : Continuous weight)
    (hweightInt : Integrable weight) (hweight0 : ∀ v, 0 ≤ weight v) :
    (∑ psi : DirichletCharacter ℂ d,
      ∫ t in (-T)..T,
        ∫ v : ℝ, weight v *
          ‖ramachandraDyadicBlock d N (b v) true psi t‖ ^ 2) =
      ∫ v : ℝ, weight v *
        (∫ t in (-T)..T,
          ∑ psi : DirichletCharacter ℂ d,
            ‖ramachandraDyadicBlock d N (b v) true psi t‖ ^ 2) := by
  let μT : Measure ℝ := volume.restrict (Set.uIoc (-T) T)
  let K : ℝ × ℝ → ℝ := fun z =>
    weight z.2 * ∑ psi : DirichletCharacter ℂ d,
      ‖ramachandraDyadicBlock d N (b z.2) true psi z.1‖ ^ 2
  let Kpsi : DirichletCharacter ℂ d → ℝ × ℝ → ℝ := fun psi z =>
    weight z.2 * ‖ramachandraDyadicBlock d N (b z.2) true psi z.1‖ ^ 2
  have horder : -T ≤ T := by linarith
  have hprod : Integrable K (μT.prod volume) := by
    simpa only [K, μT, Function.uncurry_def] using!
      (integrable_uncurry_allCharacter_weightedBlock
        d N hN hT hE b hb henergy weight hweight hweightInt hweight0)
  have hterm (psi : DirichletCharacter ℂ d) :
      Integrable (Kpsi psi) (μT.prod volume) := by
    apply hprod.mono
    · unfold Kpsi
      exact ((hweight.comp continuous_snd).mul
        ((continuous_uncurry_ramachandraDyadicBlock
          d N true b hb psi).norm.pow 2)).aestronglyMeasurable
    · filter_upwards with z
      have hsingle :
          ‖ramachandraDyadicBlock d N (b z.2) true psi z.1‖ ^ 2 ≤
            ∑ chi : DirichletCharacter ℂ d,
              ‖ramachandraDyadicBlock d N (b z.2) true chi z.1‖ ^ 2 :=
        Finset.single_le_sum
          (s := (Finset.univ : Finset (DirichletCharacter ℂ d)))
          (f := fun chi =>
            ‖ramachandraDyadicBlock d N (b z.2) true chi z.1‖ ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ psi)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hweight0 z.2) (sq_nonneg _)),
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hweight0 z.2)
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
      exact mul_le_mul_of_nonneg_left hsingle (hweight0 z.2)
  have houterTerm (psi : DirichletCharacter ℂ d) :
      IntervalIntegrable (fun t => ∫ v : ℝ, Kpsi psi (t, v)) volume (-T) T := by
    rw [intervalIntegrable_iff]
    exact (hterm psi).integral_prod_left
  have hsections : ∀ᵐ t ∂μT,
      ∀ psi : DirichletCharacter ℂ d,
        Integrable (fun v => Kpsi psi (t, v)) := by
    exact eventually_countable_forall.mpr (fun psi => (hterm psi).prod_right_ae)
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
        ∫ v : ℝ, weight v *
          ‖ramachandraDyadicBlock d N (b v) true psi t‖ ^ 2) =
        ∫ t in (-T)..T,
          ∑ psi : DirichletCharacter ℂ d,
            ∫ v : ℝ, Kpsi psi (t, v) := by
      symm
      simpa only [Kpsi] using
        (intervalIntegral.integral_finsetSum
          (s := (Finset.univ : Finset (DirichletCharacter ℂ d)))
          (fun psi hpsi => houterTerm psi))
    _ = ∫ t in (-T)..T, ∫ v : ℝ, K (t, v) := hcollapse.symm
    _ = ∫ v : ℝ, weight v *
        (∫ t in (-T)..T,
          ∑ psi : DirichletCharacter ℂ d,
            ‖ramachandraDyadicBlock d N (b v) true psi t‖ ^ 2) := by
      simpa only [K] using
        (intervalIntegral_integral_allCharacter_weightedBlock_eq
          d N hN hT hE b hb henergy weight hweight hweightInt hweight0)

end
end RamachandraFullLineReflectedBlockFubini

#print axioms RamachandraFullLineReflectedBlockFubini.integrable_uncurry_allCharacter_weightedBlock
#print axioms RamachandraFullLineReflectedBlockFubini.intervalIntegral_integral_allCharacter_weightedBlock_eq
#print axioms RamachandraFullLineReflectedBlockFubini.sum_intervalIntegral_integral_weightedBlock_eq
