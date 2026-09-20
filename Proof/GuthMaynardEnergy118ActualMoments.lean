import GuthMaynardS3LiteralLemma83Energy
import GuthMaynardEnergy118ShellCount
import GuthMaynardEnergy118ShellAnalytic
import GuthMaynardEnergy114KernelEnvelope

open scoped BigOperators FourierTransform ComplexConjugate SchwartzMap
open MeasureTheory
open GuthMaynardS3LiteralLemma83Energy
open GuthMaynardEnergy118ShellCount
open GuthMaynardEnergy118Moments
open GuthMaynardEnergy114KernelEnvelope
open GuthMaynardJIteration
noncomputable section
namespace GuthMaynardEnergy118ActualMoments

/-- Pure unit-collar fourth moment bound.  The source bump Fourier expansion is
partitioned into integer phase shells; the shell count is supplied by the
literal additive-energy collision theorem and the shell weight by the
inverse-square summation lemma. -/
theorem exists_compact_fourth_energy_constant :
    ∃ C4 : ℝ, 0 < C4 ∧
      ∀ W : Finset ℝ,
        (∫ u : ℝ in Set.Icc (-1 : ℝ) 1,
            ‖logDirichletKernel W u‖ ^ 4) ≤
          C4 * (sourceApproximateAdditiveEnergy W : ℝ) := by
  obtain ⟨Cphi, hCphi_pos, hCphi⟩ :=
    sourceBump_fourier_local_quadratic_envelope
  obtain ⟨K, hKpos, hKseries⟩ := finite_inverse_square_shell_weight_bound
  let C4 : ℝ := 2 * Cphi * K
  have hC4 : 0 < C4 := by dsimp [C4]; positivity
  refine ⟨C4, hC4, ?_⟩
  intro W
  let Q := (W.product W) ×ˢ (W.product W)
  let phase : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ := additivePhase
  let κ : ((ℝ × ℝ) × (ℝ × ℝ)) → ℤ := fun p => ⌊phase p⌋
  let w : ℤ → ℝ := fun m => 1 / (1 + ((m : ℝ) / (2 * Real.pi)) ^ 2)
  have hfiber : ∀ m : ℤ, ((Q.filter (fun p => κ p = m)).card : ℝ) ≤
      2 * (sourceApproximateAdditiveEnergy W : ℝ) := by
    intro m
    have hs := additive_shell_card_le_two_energy W m
    have hcard : (Q.filter (fun p => κ p = m)).card =
        (((W.product W).product (W.product W)).filter (fun p =>
          (m : ℝ) ≤ additivePhase p ∧ additivePhase p < (m : ℝ) + 1)).card := by
      apply congrArg Finset.card
      ext p
      simp only [Q, κ, phase, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨hp, hfloor⟩
        exact ⟨Finset.mem_product.mpr hp,
          (Int.floor_eq_iff (R := ℝ) (a := additivePhase p) (z := m)).mp hfloor⟩
      · rintro ⟨hp, hbounds⟩
        exact ⟨Finset.mem_product.mp hp,
          (Int.floor_eq_iff (R := ℝ) (a := additivePhase p) (z := m)).mpr hbounds⟩
    rw [hcard]
    exact_mod_cast hs
  have hsum :
      (∑ p ∈ Q,
        ‖FourierTransform.fourier
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (-phase p / (2 * Real.pi))‖) ≤
        2 * Cphi * K * (sourceApproximateAdditiveEnergy W : ℝ) := by
    have hpt : ∀ p ∈ Q,
        ‖FourierTransform.fourier
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (-phase p / (2 * Real.pi))‖ ≤ Cphi * w (κ p) := by
      intro p hp
      have hfloor0 := Int.floor_le (phase p)
      have hfloor1 := Int.lt_floor_add_one (phase p)
      have hh := hCphi (-phase p / (2 * Real.pi))
        ((phase p - (κ p : ℝ)) / (2 * Real.pi)) (by
          have hpi : 0 < 2 * Real.pi := by positivity
          have hpi_one : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
          have hd0 : 0 ≤ phase p - (κ p : ℝ) := by linarith
          have hd1 : phase p - (κ p : ℝ) < 1 := by linarith
          rw [abs_of_nonneg (div_nonneg hd0 hpi.le)]
          apply (div_le_iff₀ hpi).2
          linarith)
      have heq := congrFun (SchwartzMap.fourier_coe
        (sourceBumpSchwartz 1 zero_lt_one)) (-phase p / (2 * Real.pi))
      have hfun : (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) =
          (sourceBumpSchwartz 1 zero_lt_one : ℝ → ℂ) := by
        funext x
        rfl
      rw [hfun]
      rw [← heq]
      convert hh using 1 <;> ring
    calc
      _ ≤ ∑ p ∈ Q, Cphi * w (κ p) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hpt p hp
      _ ≤ Cphi * (2 * (sourceApproximateAdditiveEnergy W : ℝ) * K) := by
        have hfinite := finite_shell_weight_le Q κ w
          (E := (sourceApproximateAdditiveEnergy W : ℝ)) (K := K)
          (by positivity) (by positivity) hfiber
          (fun m => by positivity) hKseries
        simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_left hfinite (le_of_lt hCphi_pos))
      _ = 2 * Cphi * K * (sourceApproximateAdditiveEnergy W : ℝ) := by ring
  have hI := integral_Icc_le_weighted_four W
    (R := 1) (a := (-1 : ℝ)) (b := 1) zero_lt_one
    (by norm_num : |(-1 : ℝ)| ≤ 1) (by norm_num : |(1 : ℝ)| ≤ 1)
  have hC := integral_bump_logDirichlet_four_eq_fourier_sum W
    (R := 1) zero_lt_one
  have hnonneg : 0 ≤ ∫ u : ℝ,
      sourceBump 1 zero_lt_one u * ‖logDirichletKernel W u‖ ^ 4 :=
    integral_nonneg (fun u => mul_nonneg (sourceBump_nonneg 1 zero_lt_one u) (by positivity))
  have hnorm : ‖((∫ u : ℝ,
      sourceBump 1 zero_lt_one u * ‖logDirichletKernel W u‖ ^ 4 : ℝ) : ℂ)‖ =
      ∫ u : ℝ, sourceBump 1 zero_lt_one u * ‖logDirichletKernel W u‖ ^ 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hweighted :
      (∫ u : ℝ, sourceBump 1 zero_lt_one u * ‖logDirichletKernel W u‖ ^ 4) ≤
        C4 * (sourceApproximateAdditiveEnergy W : ℝ) := by
    calc
      _ = ‖((∫ u : ℝ,
          sourceBump 1 zero_lt_one u * ‖logDirichletKernel W u‖ ^ 4 : ℝ) : ℂ)‖ := hnorm.symm
      _ = ‖∑ pq ∈ (W.product W) ×ˢ (W.product W),
          FourierTransform.fourier
            (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
            (-additivePhase pq / (2 * Real.pi))‖ := by rw [hC]
      _ ≤
          ∑ pq ∈ (W.product W) ×ˢ (W.product W),
            ‖FourierTransform.fourier
              (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
              (-additivePhase pq / (2 * Real.pi))‖ := norm_sum_le _ _
      _ ≤ 2 * Cphi * K * (sourceApproximateAdditiveEnergy W : ℝ) := hsum
      _ = C4 * (sourceApproximateAdditiveEnergy W : ℝ) := by ring
  exact hI.trans hweighted

end GuthMaynardEnergy118ActualMoments

#print axioms GuthMaynardEnergy118ActualMoments.exists_compact_fourth_energy_constant
