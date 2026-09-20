import GuthMaynardS3WideFourierTail
import GuthMaynardS3MediumActualUnequalSplit

set_option maxHeartbeats 4000000

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory Metric

noncomputable section
namespace GuthMaynardS3WideExtremesGeneric

open GuthMaynardJIteration
open GuthMaynardS3MediumActualUnequalSplit
open GuthMaynardS3WideTail

theorem profile_sigmaIIEllTailFiniteLE
    {T S eta M2 M3 C : ℝ} (hT : 1 ≤ T)
    (hSgrowth : S ≤ T ^ (4 : ℝ))
    (hM2pos : 0 < M2) (hM2M3 : M2 ≤ M3) (hM3pos : 0 < M3)
    (hM2growth : M2 ≤ T ^ (4 : ℝ))
    (ellRange m2Range : Finset ℤ)
    (hEllCard :
      ((ellRange.filter (fun ell : ℤ =>
        ¬ |(ell : ℝ)| ≤ 4 * Real.rpow T (1 + eta) / M2)).card : ℝ) ≤
        T ^ (11 : ℝ))
    (hm2lo : ∀ m2' ∈ m2Range, M2 ≤ |(m2' : ℝ)|)
    (hm2hi : ∀ m2' ∈ m2Range, |(m2' : ℝ)| ≤ 2 * M2)
    (hcard : (m2Range.card : ℝ) ≤ T ^ (4 : ℝ))
    (fhat : ℝ → ℂ) {q : ℕ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hq : (300 : ℝ) ≤ eta * q)
    (hdecay : ∀ z : ℝ, z ≠ 0 →
      ‖fhat z‖ ≤ C * T ^ eta * (T / |z|) ^ q * S)
    (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hfhat : Continuous fhat) :
    sigmaIIEllTailFiniteLE ellRange m2Range
        ((4 * Real.rpow T eta) * T / M2) (fun _ => 1) fhat
        M2 T M3 (Real.rpow T eta) ≤
      (2 * Real.rpow T eta) *
        (4 * C ^ 2 * Real.rpow T (-229 : ℝ)) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTeta0 : 0 ≤ Real.rpow T eta := Real.rpow_nonneg hTpos.le eta
  have hL : (4 * Real.rpow T eta) * T / M2 =
      4 * Real.rpow T (1 + eta) / M2 := by
    have hpowadd : Real.rpow T (1 + eta) = T * Real.rpow T eta := by
      calc
        Real.rpow T (1 + eta) = Real.rpow T 1 * Real.rpow T eta :=
          Real.rpow_add hTpos 1 eta
        _ = T * Real.rpow T eta := by norm_num
    rw [hpowadd]
    ring
  let tailRange : Finset ℤ := ellRange.filter (fun ell : ℤ =>
    ¬ |(ell : ℝ)| ≤ 4 * Real.rpow T (1 + eta) / M2)
  have htail : ∀ tau : ℝ, |tau| ≤ Real.rpow T eta →
      ∑ ell ∈ tailRange,
        ‖∑ m2 ∈ m2Range,
          (m2 : ℂ) * fhat
            (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2 ≤
        4 * C ^ 2 * Real.rpow T (-229 : ℝ) := by
    intro tau htau
    exact wide_sum_norm_sq_sigmaII_affine_tail_le
      hT hM2pos hM2M3 hM3pos hM2growth tailRange m2Range
      (fun ell hell => lt_of_not_ge (Finset.mem_filter.mp hell).2)
      (by simpa only [tailRange] using hEllCard) hm2lo hm2hi hcard hSgrowth
      fhat heta heta1 hq tau htau hdecay hC hS
  have htermInt : ∀ ell ∈ tailRange,
      IntervalIntegrable
        (fun tau : ℝ =>
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              fhat
                (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2)
        volume (-Real.rpow T eta) (Real.rpow T eta) := by
    intro ell hell
    apply Continuous.intervalIntegrable
    unfold sigmaIIAffineFrequency
    fun_prop
  have hswap :
      (∑ ell ∈ tailRange,
        ∫ tau in -Real.rpow T eta..Real.rpow T eta,
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              fhat
                (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2) =
      ∫ tau in -Real.rpow T eta..Real.rpow T eta,
        ∑ ell ∈ tailRange,
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              fhat
                (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2 := by
    symm
    exact intervalIntegral.integral_finsetSum htermInt
  have hpoint : ∀ tau ∈ Set.Icc (-Real.rpow T eta) (Real.rpow T eta),
      ∑ ell ∈ tailRange,
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              fhat
                (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2 ≤
        4 * C ^ 2 *
          Real.rpow T (-229 : ℝ) := by
    intro tau htau
    exact htail tau (abs_le.2 ⟨htau.1, htau.2⟩)
  have hsumInt :
      IntervalIntegrable
        (fun tau : ℝ =>
          ∑ ell ∈ tailRange,
            ‖∑ m2 ∈ m2Range,
              (m2 : ℂ) *
                fhat
                  (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2)
        volume (-Real.rpow T eta) (Real.rpow T eta) := by
    apply Continuous.intervalIntegrable
    unfold sigmaIIAffineFrequency
    fun_prop
  have hconstInt :
      IntervalIntegrable
        (fun _ : ℝ => 4 * C ^ 2 *
          Real.rpow T (-229 : ℝ))
        volume (-Real.rpow T eta) (Real.rpow T eta) :=
    Continuous.intervalIntegrable continuous_const _ _
  have hmono := intervalIntegral.integral_mono_on
    (by linarith [hTeta0]) hsumInt hconstInt hpoint
  unfold sigmaIIEllTailFiniteLE sigmaIIFinite
  rw [hL]
  simp only [one_mul]
  calc
    (∑ x ∈ ellRange.filter (fun ell : ℤ =>
        ¬ |(ell : ℝ)| ≤ 4 * Real.rpow T (1 + eta) / M2),
        ∫ tau in -Real.rpow T eta..Real.rpow T eta,
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              fhat
                (sigmaIIAffineFrequency M3 x m2 tau)‖ ^ 2) =
      ∫ tau in -Real.rpow T eta..Real.rpow T eta,
        ∑ ell ∈ tailRange,
          ‖∑ m2 ∈ m2Range,
            (m2 : ℂ) *
              fhat
                (sigmaIIAffineFrequency M3 ell m2 tau)‖ ^ 2 := by
      simpa only [tailRange] using hswap
    _ ≤ ∫ tau in -Real.rpow T eta..Real.rpow T eta,
        4 * C ^ 2 *
          Real.rpow T (-229 : ℝ) := hmono
    _ = (2 * Real.rpow T eta) *
        (4 * C ^ 2 *
          Real.rpow T (-229 : ℝ)) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

#print axioms GuthMaynardS3WideExtremesGeneric.profile_sigmaIIEllTailFiniteLE

end GuthMaynardS3WideExtremesGeneric
