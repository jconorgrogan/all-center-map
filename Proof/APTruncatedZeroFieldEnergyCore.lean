import APHalfIntegerAlignedTail
import APZeroFieldEnergy28Grouping

/-!
# Equation (2.8) for an arbitrary truncated zero rectangle

This is the pair-expansion/Schur kernel argument with the zero support and
multiplicity passed explicitly.  It is therefore applicable to the
half-integer-aligned Perron support `sigma ≤ Re rho ≤ 1`.
-/

namespace MAPAPTruncatedZeroFieldEnergyCore

open MeasureTheory Set
open scoped ENNReal BigOperators
open APFoundation APExplicitFormulaMajorantAdapter
open MAPEndpointRegularizedZeroPrimitive

noncomputable section

private theorem rpow_pair_factor
    {X : ℝ} (hX : 0 < X) (rho rho' : ℂ) :
    Real.rpow X (rho.re + rho'.re - 1) =
      X * Real.rpow X (rho.re - 1) * Real.rpow X (rho'.re - 1) := by
  rw [show rho.re + rho'.re - 1 =
    1 + (rho.re - 1) + (rho'.re - 1) by ring]
  have houter : Real.rpow X
      (1 + (rho.re - 1) + (rho'.re - 1)) =
      Real.rpow X (1 + (rho.re - 1)) *
        Real.rpow X (rho'.re - 1) := Real.rpow_add hX _ _
  have hinner : Real.rpow X (1 + (rho.re - 1)) =
      Real.rpow X 1 * Real.rpow X (rho.re - 1) :=
    Real.rpow_add hX _ _
  have hone : Real.rpow X 1 = X := Real.rpow_one X
  rw [houter, hinner, hone]

private theorem rpow_weight_sq
    {X : ℝ} (hX : 0 < X) (rho : ℂ) :
    (Real.rpow X (rho.re - 1)) ^ 2 =
      Real.rpow X (2 * (rho.re - 1)) := by
  rw [pow_two]
  have hadd : Real.rpow X (rho.re - 1) *
      Real.rpow X (rho.re - 1) =
      Real.rpow X ((rho.re - 1) + (rho.re - 1)) :=
    (Real.rpow_add hX _ _).symm
  rw [hadd]
  congr 1
  ring

/-- Generic finite weighted Schur collapse for a zero list. -/
theorem zeroPairQuadraticForm_le_of_row
    (S : Finset ℂ) (mult : ℂ → ℕ)
    {X H : ℝ} (hX : 0 < X)
    (hrow : ∀ rho ∈ S,
      (∑ rho' ∈ S, (mult rho' : ℝ) /
        (1 + |rho'.im - rho.im|)) ≤ H) :
    (∑ rho ∈ S, ∑ rho' ∈ S,
      (mult rho : ℝ) * (mult rho' : ℝ) *
        Real.rpow X (rho.re + rho'.re - 1) /
        (1 + |rho.im - rho'.im|)) ≤
      X * H * (∑ rho ∈ S,
        (mult rho : ℝ) * Real.rpow X (2 * (rho.re - 1))) := by
  classical
  let m : ℂ → ℝ := fun z => (mult z : ℝ)
  let w : ℂ → ℝ := fun z => Real.rpow X (z.re - 1)
  let K : ℂ → ℂ → ℝ := fun z z' => 1 / (1 + |z.im - z'.im|)
  have hrow' : ∀ z ∈ S, ∑ z' ∈ S, m z' * K z z' ≤ H := by
    intro z hz
    simpa [m, K, div_eq_mul_inv, abs_sub_comm] using hrow z hz
  have hschur := MAPPaperWindowVKBypass.finite_weighted_schur
    S m w K H
    (fun z hz => by simp [m])
    (fun z hz z' hz' => by simp [K]; positivity)
    (fun z hz z' hz' => by simp [K, abs_sub_comm])
    hrow'
  calc
    (∑ rho ∈ S, ∑ rho' ∈ S,
      (mult rho : ℝ) * (mult rho' : ℝ) *
        Real.rpow X (rho.re + rho'.re - 1) /
        (1 + |rho.im - rho'.im|)) =
      X * (∑ rho ∈ S, ∑ rho' ∈ S,
        m rho * m rho' * w rho * w rho' * K rho rho') := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho hrho
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho' hrho'
      simp only [m, w, K]
      rw [rpow_pair_factor hX rho rho']
      field_simp
    _ ≤ X * (H * ∑ rho ∈ S, m rho * (w rho) ^ 2) :=
      mul_le_mul_of_nonneg_left hschur hX.le
    _ = X * H * (∑ rho ∈ S,
        (mult rho : ℝ) * Real.rpow X (2 * (rho.re - 1))) := by
      simp only [m, w]
      rw [show (∑ rho ∈ S, (mult rho : ℝ) *
          (Real.rpow X (rho.re - 1)) ^ 2) =
        ∑ rho ∈ S, (mult rho : ℝ) *
          Real.rpow X (2 * (rho.re - 1)) by
          apply Finset.sum_congr rfl
          intro rho hrho
          rw [rpow_weight_sq hX rho]]
      ring

/-- Real interval pair expansion with the manuscript constant 192. -/
theorem intervalIntegral_norm_finiteZeroField_sq_le_of_row
    (S : Finset ℂ) (mult : ℂ → ℕ)
    {X H : ℝ} (hX : 0 < X)
    (hre : ∀ rho ∈ S, 0 ≤ rho.re ∧ rho.re ≤ 1)
    (hrow : ∀ rho ∈ S,
      (∑ rho' ∈ S, (mult rho' : ℝ) /
        (1 + |rho'.im - rho.im|)) ≤ H) :
    (∫ t : ℝ in X / 4..6 * X,
      ‖finiteZeroField S mult t‖ ^ 2) ≤
      192 * X * H * (∑ rho ∈ S,
        (mult rho : ℝ) * Real.rpow X (2 * (rho.re - 1))) := by
  have hab : X / 4 ≤ 6 * X := by linarith
  have hnonneg : 0 ≤ (∫ t : ℝ in X / 4..6 * X,
      ‖finiteZeroField S mult t‖ ^ 2) :=
    intervalIntegral.integral_nonneg hab (fun t ht => sq_nonneg _)
  have hexact :=
    MAPAPZeroFieldEnergy28Core.integral_norm_finiteZeroField_sq_eq_pairIntegrals
      S mult (a := X / 4) (b := 6 * X) (by positivity) (by positivity)
  calc
    (∫ t : ℝ in X / 4..6 * X,
      ‖finiteZeroField S mult t‖ ^ 2) =
      ‖(((∫ t : ℝ in X / 4..6 * X,
        ‖finiteZeroField S mult t‖ ^ 2) : ℝ) : ℂ)‖ := by
        simp [abs_of_nonneg hnonneg]
    _ = ‖∑ rho ∈ S, ∑ rho' ∈ S,
        ∫ t : ℝ in X / 4..6 * X,
          MAPAPZeroFieldEnergy28Core.zeroPairKernel mult rho rho' t‖ := by
      simpa using congrArg norm hexact
    _ ≤ ∑ rho ∈ S, ∑ rho' ∈ S,
        ‖∫ t : ℝ in X / 4..6 * X,
          MAPAPZeroFieldEnergy28Core.zeroPairKernel mult rho rho' t‖ := by
      exact (norm_sum_le _ _).trans (by
        apply Finset.sum_le_sum
        intro rho hrho
        exact norm_sum_le _ _)
    _ ≤ ∑ rho ∈ S, ∑ rho' ∈ S,
        192 * ((mult rho : ℝ) * (mult rho' : ℝ)) *
          Real.rpow X (rho.re + rho'.re - 1) /
          (1 + |rho.im - rho'.im|) := by
      apply Finset.sum_le_sum
      intro rho hrho
      apply Finset.sum_le_sum
      intro rho' hrho'
      exact MAPAPZeroFieldEnergy28Core.norm_integral_zeroPairKernel_le_manuscript
        mult rho rho' hX (hre rho hrho).1 (hre rho hrho).2
          (hre rho' hrho').1 (hre rho' hrho').2
    _ = 192 * (∑ rho ∈ S, ∑ rho' ∈ S,
        (mult rho : ℝ) * (mult rho' : ℝ) *
          Real.rpow X (rho.re + rho'.re - 1) /
          (1 + |rho.im - rho'.im|)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho hrho
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho' hrho'
      ring
    _ ≤ 192 * (X * H * (∑ rho ∈ S,
        (mult rho : ℝ) * Real.rpow X (2 * (rho.re - 1)))) := by
      gcongr
      exact zeroPairQuadraticForm_le_of_row S mult hX hrow
    _ = _ := by ring

private theorem continuousOn_norm_finiteZeroField_sq
    (S : Finset ℂ) (mult : ℂ → ℕ)
    {X : ℝ} (hX : 0 < X) :
    ContinuousOn (fun t : ℝ => ‖finiteZeroField S mult t‖ ^ 2)
      (Set.Icc (X / 4) (6 * X)) := by
  apply ContinuousOn.pow
  apply ContinuousOn.norm
  unfold finiteZeroField
  apply continuousOn_finsetSum
  intro rho hrho t ht
  have htpos : 0 < t := by linarith [ht.1]
  exact (continuousAt_const.mul
    (Complex.continuousAt_ofReal_cpow_const t (rho - 1)
      (Or.inr htpos.ne'))).continuousWithinAt

/-- Exact indicator-ENNReal to real interval conversion for an arbitrary
finite zero field. -/
theorem lintegral_zeroNormField_sq_eq_intervalIntegral
    (S : Finset ℂ) (mult : ℂ → ℕ)
    {X : ℝ} (hX : 0 < X) :
    (∫⁻ t : ℝ,
      ((Set.Icc (X / 4) (6 * X)).indicator
        (fun u => ENNReal.ofReal ‖finiteZeroField S mult u‖) t) ^ 2) =
      ENNReal.ofReal (∫ t : ℝ in X / 4..6 * X,
        ‖finiteZeroField S mult t‖ ^ 2) := by
  let f : ℝ → ℝ := fun t => ‖finiteZeroField S mult t‖ ^ 2
  have hcont : ContinuousOn f (Set.Icc (X / 4) (6 * X)) :=
    continuousOn_norm_finiteZeroField_sq S mult hX
  have hint : IntegrableOn f (Set.Icc (X / 4) (6 * X)) :=
    hcont.integrableOn_Icc
  have hnonneg : 0 ≤ᶠ[ae (volume.restrict (Set.Icc (X / 4) (6 * X)))] f :=
    Filter.Eventually.of_forall (fun t => sq_nonneg _)
  have hpoint (t : ℝ) :
      ((Set.Icc (X / 4) (6 * X)).indicator
        (fun u => ENNReal.ofReal ‖finiteZeroField S mult u‖) t) ^ 2 =
      (Set.Icc (X / 4) (6 * X)).indicator
        (fun u => ENNReal.ofReal (f u)) t := by
    by_cases ht : t ∈ Set.Icc (X / 4) (6 * X)
    · simp only [Set.indicator_of_mem ht]
      rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
    · simp [Set.indicator_of_notMem ht]
  calc
    (∫⁻ t : ℝ,
      ((Set.Icc (X / 4) (6 * X)).indicator
        (fun u => ENNReal.ofReal ‖finiteZeroField S mult u‖) t) ^ 2) =
      ∫⁻ t : ℝ, (Set.Icc (X / 4) (6 * X)).indicator
        (fun u => ENNReal.ofReal (f u)) t := by
      apply lintegral_congr
      exact hpoint
    _ = ∫⁻ t : ℝ in Set.Icc (X / 4) (6 * X),
        ENNReal.ofReal (f t) := lintegral_indicator measurableSet_Icc _
    _ = ENNReal.ofReal
        (∫ t : ℝ in Set.Icc (X / 4) (6 * X), f t) :=
      (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
    _ = ENNReal.ofReal
        (∫ t : ℝ in X / 4..6 * X, f t) := by
      congr 1
      rw [intervalIntegral.integral_of_le (by linarith),
        integral_Icc_eq_integral_Ioc]

/-- Generic truncated equation-(2.8) energy from a row estimate. -/
theorem lintegral_zeroNormField_sq_le_of_row
    (S : Finset ℂ) (mult : ℂ → ℕ)
    {X H : ℝ} (hX : 0 < X)
    (hre : ∀ rho ∈ S, 0 ≤ rho.re ∧ rho.re ≤ 1)
    (hrow : ∀ rho ∈ S,
      (∑ rho' ∈ S, (mult rho' : ℝ) /
        (1 + |rho'.im - rho.im|)) ≤ H) :
    (∫⁻ t : ℝ,
      ((Set.Icc (X / 4) (6 * X)).indicator
        (fun u => ENNReal.ofReal ‖finiteZeroField S mult u‖) t) ^ 2) ≤
      ENNReal.ofReal (192 * X * H * (∑ rho ∈ S,
        (mult rho : ℝ) * Real.rpow X (2 * (rho.re - 1)))) := by
  rw [lintegral_zeroNormField_sq_eq_intervalIntegral S mult hX]
  exact ENNReal.ofReal_le_ofReal
    (intervalIntegral_norm_finiteZeroField_sq_le_of_row
      S mult hX hre hrow)

end
end MAPAPTruncatedZeroFieldEnergyCore

#print axioms MAPAPTruncatedZeroFieldEnergyCore.zeroPairQuadraticForm_le_of_row
#print axioms MAPAPTruncatedZeroFieldEnergyCore.intervalIntegral_norm_finiteZeroField_sq_le_of_row
#print axioms MAPAPTruncatedZeroFieldEnergyCore.lintegral_zeroNormField_sq_le_of_row
