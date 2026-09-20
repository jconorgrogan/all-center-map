import GuthMaynardS3LiteralLemma83Energy
import GuthMaynardEnergy118SecondShell
import GuthMaynardEnergy118ShellAnalytic
import GuthMaynardEnergy114KernelEnvelope

open scoped BigOperators FourierTransform ComplexConjugate SchwartzMap
open MeasureTheory
open GuthMaynardS3LiteralLemma83Energy
open GuthMaynardEnergy118SecondShell
open GuthMaynardEnergy118Moments
open GuthMaynardEnergy114KernelEnvelope
open GuthMaynardJIteration
open CGLProofDAG
noncomputable section
namespace GuthMaynardEnergy118ActualSecondMoment

private theorem integral_bump_logDirichlet_sq_eq_fourier_sum (W : Finset ℝ) :
    ((∫ u : ℝ, sourceBump 1 zero_lt_one u *
        ‖logDirichletKernel W u‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ W.product W,
        FourierTransform.fourier
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (-(p.1 - p.2) / (2 * Real.pi)) := by
  have hpt : ∀ u : ℝ,
      (sourceBump 1 zero_lt_one u : ℂ) *
          (‖logDirichletKernel W u‖ ^ 2 : ℂ) =
        ∑ a ∈ W, ∑ b ∈ W,
          (sourceBump 1 zero_lt_one u : ℂ) *
            Complex.exp (Complex.I * (((a - b) * u : ℝ) : ℂ)) := by
    intro u
    rw [logDirichletKernel_norm_sq, star_logDirichletKernel]
    conv_rhs => rw [Finset.sum_comm]
    unfold logDirichletKernel
    simp [Finset.mul_sum, Finset.sum_mul, ← Complex.exp_add]
    congr 1
    funext a
    congr 1
    funext b
    ring_nf
  have hsumInt :
      Integrable (fun u : ℝ =>
        ∑ a ∈ W, ∑ b ∈ W,
          (sourceBump 1 zero_lt_one u : ℂ) *
            Complex.exp (Complex.I * (((a - b) * u : ℝ) : ℂ))) := by
    exact integrable_finsetSum _ (fun a ha => integrable_finsetSum _
      (fun b hb => integrable_bump_mul_exp zero_lt_one (a - b)))
  rw [integral_complex_ofReal.symm]
  simp_rw [Complex.ofReal_mul]
  calc
    (∫ u : ℝ, (sourceBump 1 zero_lt_one u : ℂ) *
        ((‖logDirichletKernel W u‖ ^ 2 : ℝ) : ℂ)) =
        ∫ u : ℝ, ∑ a ∈ W, ∑ b ∈ W,
          (sourceBump 1 zero_lt_one u : ℂ) *
            Complex.exp (Complex.I * (((a - b) * u : ℝ) : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with u
      simpa only [Complex.ofReal_pow] using hpt u
    _ = ∑ a ∈ W, ∑ b ∈ W, ∫ u : ℝ,
          (sourceBump 1 zero_lt_one u : ℂ) *
            Complex.exp (Complex.I * (((a - b) * u : ℝ) : ℂ)) := by
      rw [integral_finsetSum W (fun a ha => integrable_finsetSum W
        (fun b hb => integrable_bump_mul_exp zero_lt_one (a - b)))]
      apply Finset.sum_congr rfl
      intro a ha
      rw [integral_finsetSum W (fun b hb => integrable_bump_mul_exp zero_lt_one (a - b))]
    _ = ∑ p ∈ W.product W,
        FourierTransform.fourier
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (-(p.1 - p.2) / (2 * Real.pi)) := by
      rw [← Finset.sum_product']
      apply Finset.sum_congr rfl
      intro p hp
      rcases p with ⟨a, b⟩
      simp only [Finset.mem_product] at hp
      simpa using (fourier_sourceBump_phase zero_lt_one (a - b)).symm

/-- Pure compact second moment on the unit log interval. -/
theorem exists_compact_second_card_constant :
    ∃ C2 : ℝ, 0 < C2 ∧
      ∀ W : Finset ℝ, OneSeparated W →
        (∫ u : ℝ in Set.Icc (-1 : ℝ) 1,
            ‖logDirichletKernel W u‖ ^ 2) ≤ C2 * (W.card : ℝ) := by
  obtain ⟨Cphi, hCphi_pos, hCphi⟩ :=
    sourceBump_fourier_local_quadratic_envelope
  obtain ⟨K, hKpos, hKseries⟩ := finite_inverse_square_shell_weight_bound
  let C2 : ℝ := 2 * Cphi * K
  have hC2 : 0 < C2 := by dsimp [C2]; positivity
  refine ⟨C2, hC2, ?_⟩
  intro W hsep
  let Q := W.product W
  let phase : ℝ × ℝ → ℝ := fun p => p.1 - p.2
  let κ : ℝ × ℝ → ℤ := fun p => ⌊phase p⌋
  let w : ℤ → ℝ := fun m => 1 / (1 + ((m : ℝ) / (2 * Real.pi)) ^ 2)
  have hfiber : ∀ m : ℤ, ((Q.filter (fun p => κ p = m)).card : ℝ) ≤
      2 * (W.card : ℝ) := by
    intro m
    have hs := difference_shell_card_le_two_card W hsep m
    have hcard : (Q.filter (fun p => κ p = m)).card =
        (Q.filter (fun p => (m : ℝ) ≤ phase p ∧ phase p < (m : ℝ)+1)).card := by
      apply congrArg Finset.card
      ext p
      simp only [Q, κ, phase, Finset.mem_filter]
      constructor
      · rintro ⟨hp, hfloor⟩
        exact ⟨hp, (Int.floor_eq_iff (R := ℝ) (a := phase p) (z := m)).mp hfloor⟩
      · rintro ⟨hp, hb⟩
        exact ⟨hp, (Int.floor_eq_iff (R := ℝ) (a := phase p) (z := m)).mpr hb⟩
    rw [hcard]
    exact_mod_cast hs
  have hsum :
      (∑ p ∈ Q,
        ‖FourierTransform.fourier
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (-(phase p) / (2 * Real.pi))‖) ≤
        2 * Cphi * K * (W.card : ℝ) := by
    have hpt : ∀ p ∈ Q,
        ‖FourierTransform.fourier
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (-(phase p) / (2 * Real.pi))‖ ≤ Cphi * w (κ p) := by
      intro p hp
      have hfloor0 := Int.floor_le (phase p)
      have hfloor1 := Int.lt_floor_add_one (phase p)
      have hh := hCphi (-(phase p) / (2 * Real.pi))
        ((phase p - (κ p : ℝ)) / (2 * Real.pi)) (by
          have hpi : 0 < 2 * Real.pi := by positivity
          have hpi_one : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
          have hd0 : 0 ≤ phase p - (κ p : ℝ) := by linarith
          have hd1 : phase p - (κ p : ℝ) < 1 := by linarith
          rw [abs_of_nonneg (div_nonneg hd0 hpi.le)]
          apply (div_le_iff₀ hpi).2
          linarith)
      have heq := congrFun (SchwartzMap.fourier_coe
        (sourceBumpSchwartz 1 zero_lt_one)) (-(phase p) / (2 * Real.pi))
      have hfun : (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) =
          (sourceBumpSchwartz 1 zero_lt_one : ℝ → ℂ) := by
        funext x; rfl
      rw [hfun, ← heq]
      convert hh using 1 <;> ring
    calc
      _ ≤ ∑ p ∈ Q, Cphi * w (κ p) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hpt p hp
      _ ≤ Cphi * (2 * (W.card : ℝ) * K) := by
        have hfinite := finite_shell_weight_le Q κ w
          (E := (W.card : ℝ)) (K := K)
          (by positivity) (by positivity) hfiber
          (fun m => by positivity) hKseries
        simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_left hfinite (le_of_lt hCphi_pos))
      _ = 2 * Cphi * K * (W.card : ℝ) := by ring
  have hInt : Integrable (fun u : ℝ =>
      sourceBump 1 zero_lt_one u * ‖logDirichletKernel W u‖ ^ 2) :=
    ((sourceBump_contDiff 1 zero_lt_one).continuous.mul
      ((logDirichletKernel_continuous W).norm.pow 2)).integrable_of_hasCompactSupport
      (sourceBump_hasCompactSupport 1 zero_lt_one).mul_right
  have hI : (∫ u : ℝ in Set.Icc (-1 : ℝ) 1,
      ‖logDirichletKernel W u‖ ^ 2) ≤
      ∫ u : ℝ, sourceBump 1 zero_lt_one u * ‖logDirichletKernel W u‖ ^ 2 := by
    have hptI : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
        ‖logDirichletKernel W u‖ ^ 2 =
          sourceBump 1 zero_lt_one u * ‖logDirichletKernel W u‖ ^ 2 := by
      intro u hu
      have habs : |u| ≤ (1 : ℝ) := mem_Icc_abs_le hu (by norm_num) (by norm_num)
      rw [sourceBump_eq_one_of_abs_le 1 zero_lt_one habs, one_mul]
    have hf0 : 0 ≤ᵐ[volume] fun u : ℝ =>
        sourceBump 1 zero_lt_one u * ‖logDirichletKernel W u‖ ^ 2 :=
      Filter.Eventually.of_forall fun u =>
        mul_nonneg (sourceBump_nonneg 1 zero_lt_one u) (by positivity)
    rw [setIntegral_congr_fun measurableSet_Icc hptI]
    exact setIntegral_le_integral hInt hf0
  have hC := integral_bump_logDirichlet_sq_eq_fourier_sum W
  have hnonneg : 0 ≤ ∫ u : ℝ,
      sourceBump 1 zero_lt_one u * ‖logDirichletKernel W u‖ ^ 2 :=
    integral_nonneg (fun u => mul_nonneg (sourceBump_nonneg 1 zero_lt_one u) (by positivity))
  have hnorm : ‖((∫ u : ℝ,
      sourceBump 1 zero_lt_one u * ‖logDirichletKernel W u‖ ^ 2 : ℝ) : ℂ)‖ =
      ∫ u : ℝ, sourceBump 1 zero_lt_one u * ‖logDirichletKernel W u‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hweighted :
      (∫ u : ℝ, sourceBump 1 zero_lt_one u * ‖logDirichletKernel W u‖ ^ 2) ≤
        C2 * (W.card : ℝ) := by
    calc
      _ = ‖((∫ u : ℝ,
          sourceBump 1 zero_lt_one u * ‖logDirichletKernel W u‖ ^ 2 : ℝ) : ℂ)‖ := hnorm.symm
      _ = ‖∑ p ∈ Q, FourierTransform.fourier
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (-(phase p) / (2 * Real.pi))‖ := by rw [hC]
      _ ≤ _ := norm_sum_le _ _
      _ ≤ 2 * Cphi * K * (W.card : ℝ) := hsum
      _ = C2 * (W.card : ℝ) := by ring
  exact hI.trans hweighted

end GuthMaynardEnergy118ActualSecondMoment

#print axioms GuthMaynardEnergy118ActualSecondMoment.exists_compact_second_card_constant
