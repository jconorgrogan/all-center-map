import GuthMaynardJIterationMediumRegionIntegration

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-! Dyadic aggregation of the exact TeX 1595--1598 affine identity. -/

/-- The exact localized-pair region integral is dominated by finite
`Sigma_II`.  Every loss preceding the analytic `Sigma_II` estimate remains
visible: `P` is the localized-pair count, `N1` bounds the signed `m1` range,
and `Kpsi` is the first cutoff Fourier supremum. -/
theorem setIntegral_norm_sourceFirstPoissonLocalizedPairSum_sq_le_sigmaII
    (m1Range ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    (hfhat : Continuous fhat) (S : Set ℝ) (hS : MeasurableSet S)
    (psi2 : ℝ → ℝ) (M2 T : ℝ)
    {M1 M3 B Kpsi P N1 : ℝ}
    (hM1 : 0 < M1) (hM3 : 0 < M3) (hB : 0 ≤ B)
    (hKpsi : 0 ≤ Kpsi) (hP : 0 ≤ P) (hN1 : 0 ≤ N1)
    (hF : ∀ z, ‖F z‖ ≤ Kpsi)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm1lo : ∀ m1 ∈ m1Range, M1 ≤ |(m1 : ℝ)|)
    (hm2pos : ∀ m2 ∈ m2Range, 0 < m2)
    (hcard1 : (m1Range.card : ℝ) ≤ N1)
    (hpairCard : ∀ xi ∈ S,
      ((sourceMediumLocalizedPairs m1Range ellRange M3 B xi).card : ℝ) ≤ P)
    (hpsi2 : ∀ ell ∈ ellRange,
      1 ≤ psi2 (M2 * (ell : ℝ) / T))
    (hleft : IntegrableOn (fun xi =>
      ‖sourceFirstPoissonLocalizedPairSum
        m1Range ellRange m2Range F fhat M3 B xi‖ ^ 2) S) :
    (∫ xi in S,
      ‖sourceFirstPoissonLocalizedPairSum
        m1Range ellRange m2Range F fhat M3 B xi‖ ^ 2) ≤
      P * (N1 * (M3 * Kpsi ^ 2 / M1)) *
        sigmaIIFinite ellRange m2Range psi2 fhat M2 T M3 B := by
  let Q : ℤ → ℝ := fun ell =>
    ∫ tau in -B..B,
      ‖∑ m2 ∈ m2Range,
        sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2
  have hQ0 : ∀ ell, 0 ≤ Q ell := by
    intro ell
    apply intervalIntegral.integral_nonneg (by linarith)
    intro tau htau
    exact sq_nonneg _
  have hcoeff : ∀ m1 ∈ m1Range,
      (M3 * Kpsi) ^ 2 * (1 / (M3 * |(m1 : ℝ)|)) ≤
        M3 * Kpsi ^ 2 / M1 := by
    intro m1 hm1mem
    have hm1abs : 0 < |(m1 : ℝ)| :=
      lt_of_lt_of_le hM1 (hm1lo m1 hm1mem)
    have hinv : 1 / |(m1 : ℝ)| ≤ 1 / M1 :=
      one_div_le_one_div_of_le hM1 (hm1lo m1 hm1mem)
    calc
      (M3 * Kpsi) ^ 2 * (1 / (M3 * |(m1 : ℝ)|)) =
          (M3 * Kpsi ^ 2) * (1 / |(m1 : ℝ)|) := by
            field_simp [hM3.ne', hm1abs.ne']
      _ ≤ (M3 * Kpsi ^ 2) * (1 / M1) := by
        exact mul_le_mul_of_nonneg_left hinv
          (mul_nonneg hM3.le (sq_nonneg _))
      _ = M3 * Kpsi ^ 2 / M1 := by ring
  have hsumQ :
      (∑ ell ∈ ellRange, Q ell) ≤
        sigmaIIFinite ellRange m2Range psi2 fhat M2 T M3 B := by
    unfold sigmaIIFinite
    apply Finset.sum_le_sum
    intro ell hell
    dsimp only [Q]
    exact le_mul_of_one_le_left (hQ0 ell) (hpsi2 ell hell)
  have hsumBound :
      (∑ p ∈ m1Range ×ˢ ellRange,
        ((M3 * Kpsi) ^ 2 * (1 / (M3 * |(p.1 : ℝ)|))) * Q p.2) ≤
      N1 * (M3 * Kpsi ^ 2 / M1) *
        sigmaIIFinite ellRange m2Range psi2 fhat M2 T M3 B := by
    rw [Finset.sum_product]
    calc
      (∑ m1 ∈ m1Range, ∑ ell ∈ ellRange,
          ((M3 * Kpsi) ^ 2 * (1 / (M3 * |(m1 : ℝ)|))) * Q ell) ≤
        ∑ _m1 ∈ m1Range, ∑ ell ∈ ellRange,
          (M3 * Kpsi ^ 2 / M1) * Q ell := by
            apply Finset.sum_le_sum
            intro m1 hm1mem
            apply Finset.sum_le_sum
            intro ell hell
            exact mul_le_mul_of_nonneg_right (hcoeff m1 hm1mem) (hQ0 ell)
      _ = (m1Range.card : ℝ) *
          ((M3 * Kpsi ^ 2 / M1) * ∑ ell ∈ ellRange, Q ell) := by
            rw [Finset.mul_sum]
            simp
      _ ≤ N1 * ((M3 * Kpsi ^ 2 / M1) * ∑ ell ∈ ellRange, Q ell) := by
            apply mul_le_mul_of_nonneg_right hcard1
            exact mul_nonneg
              (div_nonneg (mul_nonneg hM3.le (sq_nonneg _)) hM1.le)
              (Finset.sum_nonneg fun ell _ => hQ0 ell)
      _ ≤ N1 * ((M3 * Kpsi ^ 2 / M1) *
          sigmaIIFinite ellRange m2Range psi2 fhat M2 T M3 B) := by
            apply mul_le_mul_of_nonneg_left _ hN1
            exact mul_le_mul_of_nonneg_left hsumQ
              (div_nonneg (mul_nonneg hM3.le (sq_nonneg _)) hM1.le)
      _ = N1 * (M3 * Kpsi ^ 2 / M1) *
          sigmaIIFinite ellRange m2Range psi2 fhat M2 T M3 B := by ring
  refine (setIntegral_norm_sourceFirstPoissonLocalizedPairSum_sq_le_affine
    m1Range ellRange m2Range F fhat hfhat S hS hM3 hB hKpsi hP hF hm1
    hm2pos hpairCard hleft).trans ?_
  calc
    P * ∑ p ∈ m1Range ×ˢ ellRange,
        ((M3 * Kpsi) ^ 2 * (1 / (M3 * |(p.1 : ℝ)|))) *
          ∫ tau in -B..B,
            ‖∑ m2 ∈ m2Range,
              sigmaIIFourierSummand M3 fhat p.2 m2 tau‖ ^ 2 ≤
      P * (N1 * (M3 * Kpsi ^ 2 / M1) *
        sigmaIIFinite ellRange m2Range psi2 fhat M2 T M3 B) := by
          apply mul_le_mul_of_nonneg_left _ hP
          simpa only [Q] using hsumBound
    _ = P * (N1 * (M3 * Kpsi ^ 2 / M1)) *
        sigmaIIFinite ellRange m2Range psi2 fhat M2 T M3 B := by ring

/-- Source-scale simplification of the preceding exact coefficient.  If the
pair count is `Lpair*(1+M1/M3)` and the dyadic `m1` range has at most
`c1*M1` elements, the outside factor is exactly `(M1+M3)` times the exposed
losses. -/
theorem sourceMediumSigmaOutsideFactor_le
    {M1 M3 Kpsi P N1 Lpair c1 Sigma : ℝ}
    (hM1 : 0 < M1) (hM3 : 0 < M3)
    (hN1 : 0 ≤ N1) (hLpair : 0 ≤ Lpair) (hSigma : 0 ≤ Sigma)
    (hpair : P ≤ Lpair * (1 + M1 / M3))
    (hcard1 : N1 ≤ c1 * M1) :
    P * (N1 * (M3 * Kpsi ^ 2 / M1)) * Sigma ≤
      (Lpair * c1 * Kpsi ^ 2) * (M1 + M3) * Sigma := by
  have hscale : 0 ≤ M3 * Kpsi ^ 2 / M1 :=
    div_nonneg (mul_nonneg hM3.le (sq_nonneg _)) hM1.le
  calc
    P * (N1 * (M3 * Kpsi ^ 2 / M1)) * Sigma ≤
      (Lpair * (1 + M1 / M3)) *
        ((c1 * M1) * (M3 * Kpsi ^ 2 / M1)) * Sigma := by
          gcongr
    _ = (Lpair * c1 * Kpsi ^ 2) * (M1 + M3) * Sigma := by
      field_simp [hM1.ne', hM3.ne']
      ring

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.setIntegral_norm_sourceFirstPoissonLocalizedPairSum_sq_le_sigmaII
#print axioms GuthMaynardJIteration.sourceMediumSigmaOutsideFactor_le
