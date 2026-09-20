import GuthMaynardJIterationSourceHighFrequency
import GuthMaynardJIterationSigmaII

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- The corrected `M₃` affine frequency is large on the discarded `ell`
range. -/
theorem abs_sigmaIIAffineFrequency_lower
    {M3 M2lo L Ctau : ℝ} (hM3 : 0 < M3) (hM2lo : 0 ≤ M2lo)
    (hgap : 0 ≤ L - Ctau / M3)
    (ell m2 : ℤ) (tau : ℝ)
    (hell : L ≤ |(ell : ℝ)|) (hm2 : M2lo ≤ |(m2 : ℝ)|)
    (htau : |tau| ≤ Ctau) :
    M2lo * (L - Ctau / M3) ≤
      |sigmaIIAffineFrequency M3 ell m2 tau| := by
  have htauDiv : |tau / M3| ≤ Ctau / M3 := by
    rw [abs_div, abs_of_pos hM3]
    exact (div_le_div_iff_of_pos_right hM3).2 htau
  have htriangle : |(ell : ℝ)| ≤
      |(ell : ℝ) + tau / M3| + |tau / M3| := by
    calc
      |(ell : ℝ)| =
          |((ell : ℝ) + tau / M3) + (-(tau / M3))| := by ring_nf
      _ ≤ |(ell : ℝ) + tau / M3| + |-(tau / M3)| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have hbase : L - Ctau / M3 ≤ |(ell : ℝ) + tau / M3| := by
    linarith
  have hmul : M2lo * (L - Ctau / M3) ≤
      |(m2 : ℝ)| * |(ell : ℝ) + tau / M3| := by
    exact mul_le_mul hm2 hbase hgap (abs_nonneg _)
  unfold sigmaIIAffineFrequency
  rw [show (ell : ℝ) * (m2 : ℝ) + (m2 : ℝ) / M3 * tau =
      (m2 : ℝ) * ((ell : ℝ) + tau / M3) by
        field_simp [hM3.ne']]
  simpa only [abs_mul] using hmul

/-- Source Fourier decay at the corrected affine `M₃` frequency on the
discarded `ell` range. -/
theorem sourceFourierRapidDecay_at_sigmaIIAffineFrequency
    (fhat : ℝ → ℂ) {T S eta C M3 M2lo L Ctau : ℝ} (j : ℕ)
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hM3 : 0 < M3) (hM2lo : 0 ≤ M2lo)
    (hfreq : 0 < M2lo * (L - Ctau / M3))
    (hbound : ∀ z : ℝ, z ≠ 0 →
      ‖fhat z‖ ≤ C * T ^ eta * (T / |z|) ^ j * S)
    (ell m2 : ℤ) (tau : ℝ)
    (hell : L ≤ |(ell : ℝ)|) (hm2 : M2lo ≤ |(m2 : ℝ)|)
    (htau : |tau| ≤ Ctau) :
    ‖fhat (sigmaIIAffineFrequency M3 ell m2 tau)‖ ≤
      C * T ^ eta *
        (T / (M2lo * (L - Ctau / M3))) ^ j * S := by
  have hgap : 0 ≤ L - Ctau / M3 := by
    by_contra hneg
    have : M2lo * (L - Ctau / M3) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hM2lo (le_of_not_ge hneg)
    linarith
  have hlower := abs_sigmaIIAffineFrequency_lower hM3 hM2lo hgap
    ell m2 tau hell hm2 htau
  have hzabs : 0 < |sigmaIIAffineFrequency M3 ell m2 tau| :=
    lt_of_lt_of_le hfreq hlower
  have hfrac : T / |sigmaIIAffineFrequency M3 ell m2 tau| ≤
      T / (M2lo * (L - Ctau / M3)) :=
    div_le_div_of_nonneg_left hT hfreq hlower
  have hpow := pow_le_pow_left₀ (by positivity) hfrac j
  refine (hbound _ (abs_pos.mp hzabs)).trans ?_
  have hfac : 0 ≤ C * T ^ eta :=
    mul_nonneg hC (Real.rpow_nonneg hT eta)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow hfac) hS

def sigmaIIEllRetainedFinite
    (ellRange m2Range : Finset ℤ) (L : ℝ)
    (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ)
    (M2 T M3 Ctau : ℝ) : ℝ :=
  sigmaIIFinite (ellRange.filter fun ell => |(ell : ℝ)| < L)
    m2Range psi2 fhat M2 T M3 Ctau

def sigmaIIEllTailFinite
    (ellRange m2Range : Finset ℤ) (L : ℝ)
    (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ)
    (M2 T M3 Ctau : ℝ) : ℝ :=
  sigmaIIFinite (ellRange.filter fun ell => ¬ |(ell : ℝ)| < L)
    m2Range psi2 fhat M2 T M3 Ctau

/-- Exact finite retained/tail partition before inserting Fourier decay. -/
theorem sigmaIIFinite_eq_ellRetained_add_tail
    (ellRange m2Range : Finset ℤ) (L : ℝ)
    (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ)
    (M2 T M3 Ctau : ℝ) :
    sigmaIIFinite ellRange m2Range psi2 fhat M2 T M3 Ctau =
      sigmaIIEllRetainedFinite ellRange m2Range L psi2 fhat M2 T M3 Ctau +
        sigmaIIEllTailFinite ellRange m2Range L psi2 fhat M2 T M3 Ctau := by
  unfold sigmaIIEllRetainedFinite sigmaIIEllTailFinite sigmaIIFinite
  exact (Finset.sum_filter_add_sum_filter_not ellRange
    (fun ell => |(ell : ℝ)| < L) _).symm

/-- Pointwise discarded-`ell` Fourier sum bound. -/
theorem norm_sigmaIIFourierSum_le_on_ellTail
    (m2Range : Finset ℤ) (fhat : ℝ → ℂ)
    {T S eta C M3 M2lo M2hi N2 L Ctau : ℝ} (j : ℕ)
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hM3 : 0 < M3) (hM2lo : 0 ≤ M2lo) (hM2hi : 0 ≤ M2hi)
    (hN2 : (m2Range.card : ℝ) ≤ N2)
    (hfreq : 0 < M2lo * (L - Ctau / M3))
    (hm2lo : ∀ m2 ∈ m2Range, M2lo ≤ |(m2 : ℝ)|)
    (hm2hi : ∀ m2 ∈ m2Range, |(m2 : ℝ)| ≤ M2hi)
    (hbound : ∀ z : ℝ, z ≠ 0 →
      ‖fhat z‖ ≤ C * T ^ eta * (T / |z|) ^ j * S)
    (ell : ℤ) (tau : ℝ) (hell : L ≤ |(ell : ℝ)|)
    (htau : |tau| ≤ Ctau) :
    ‖∑ m2 ∈ m2Range, sigmaIIFourierSummand M3 fhat ell m2 tau‖ ≤
      N2 * M2hi *
        (C * T ^ eta *
          (T / (M2lo * (L - Ctau / M3))) ^ j * S) := by
  calc
    ‖∑ m2 ∈ m2Range, sigmaIIFourierSummand M3 fhat ell m2 tau‖ ≤
        ∑ m2 ∈ m2Range, ‖sigmaIIFourierSummand M3 fhat ell m2 tau‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m2 ∈ m2Range, M2hi *
        (C * T ^ eta *
          (T / (M2lo * (L - Ctau / M3))) ^ j * S) := by
      apply Finset.sum_le_sum
      intro m2 hm2mem
      unfold sigmaIIFourierSummand
      simpa only [norm_mul, Complex.norm_intCast, Int.cast_abs] using
        (mul_le_mul (hm2hi m2 hm2mem)
          (sourceFourierRapidDecay_at_sigmaIIAffineFrequency fhat j
            hT hS hC hM3 hM2lo hfreq hbound ell m2 tau hell
            (hm2lo m2 hm2mem) htau)
          (norm_nonneg _) hM2hi)
    _ = (m2Range.card : ℝ) * (M2hi *
        (C * T ^ eta *
          (T / (M2lo * (L - Ctau / M3))) ^ j * S)) := by simp
    _ ≤ N2 * M2hi *
        (C * T ^ eta *
          (T / (M2lo * (L - Ctau / M3))) ^ j * S) := by
      have hD : 0 ≤ M2hi * (C * T ^ eta *
          (T / (M2lo * (L - Ctau / M3))) ^ j * S) := by positivity
      calc
        (m2Range.card : ℝ) * (M2hi * (C * T ^ eta *
            (T / (M2lo * (L - Ctau / M3))) ^ j * S)) ≤
          N2 * (M2hi * (C * T ^ eta *
            (T / (M2lo * (L - Ctau / M3))) ^ j * S)) :=
          mul_le_mul_of_nonneg_right hN2 hD
        _ = _ := by ring

/-- Quantitative finite-`ell` restriction: the entire discarded contribution
to `Sigma_II` is bounded by the source Fourier seminorm with every finite
cardinality and bump factor visible. -/
theorem sigmaIIEllTailFinite_le
    (ellRange m2Range : Finset ℤ) (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ)
    {T S eta C M2 M3 M2lo M2hi N2 L Ctau P2 Nell : ℝ} (j : ℕ)
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hM3 : 0 < M3) (hM2lo : 0 ≤ M2lo) (hM2hi : 0 ≤ M2hi)
    (hN2 : (m2Range.card : ℝ) ≤ N2)
    (hCtau : 0 ≤ Ctau) (hP2 : 0 ≤ P2)
    (hNell : ((ellRange.filter fun ell : ℤ => ¬ |(ell : ℝ)| < L).card : ℝ) ≤ Nell)
    (hfreq : 0 < M2lo * (L - Ctau / M3))
    (hm2lo : ∀ m2 ∈ m2Range, M2lo ≤ |(m2 : ℝ)|)
    (hm2hi : ∀ m2 ∈ m2Range, |(m2 : ℝ)| ≤ M2hi)
    (hpsi0 : ∀ ell ∈ ellRange, 0 ≤ psi2 (M2 * (ell : ℝ) / T))
    (hpsi : ∀ ell ∈ ellRange, psi2 (M2 * (ell : ℝ) / T) ≤ P2)
    (hbound : ∀ z : ℝ, z ≠ 0 →
      ‖fhat z‖ ≤ C * T ^ eta * (T / |z|) ^ j * S) :
    sigmaIIEllTailFinite ellRange m2Range L psi2 fhat M2 T M3 Ctau ≤
      Nell * P2 * (2 * Ctau) *
        (N2 * M2hi *
          (C * T ^ eta *
            (T / (M2lo * (L - Ctau / M3))) ^ j * S)) ^ 2 := by
  let D : ℝ := C * T ^ eta *
    (T / (M2lo * (L - Ctau / M3))) ^ j * S
  let Q : ℝ := N2 * M2hi * D
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hN20 : 0 ≤ N2 := le_trans (Nat.cast_nonneg _) hN2
  have hQ : 0 ≤ Q := mul_nonneg (mul_nonneg hN20 hM2hi) hD
  unfold sigmaIIEllTailFinite sigmaIIFinite
  calc
    (∑ ell ∈ ellRange.filter fun ell : ℤ => ¬ |(ell : ℝ)| < L,
        psi2 (M2 * (ell : ℝ) / T) *
          ∫ tau in -Ctau..Ctau,
            ‖∑ m2 ∈ m2Range,
              sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2) ≤
      ∑ _ell ∈ ellRange.filter fun ell : ℤ => ¬ |(ell : ℝ)| < L,
        P2 * (2 * Ctau * Q ^ 2) := by
      apply Finset.sum_le_sum
      intro ell hellmem
      have hellRange : ell ∈ ellRange := (Finset.mem_filter.mp hellmem).1
      have hell : L ≤ |(ell : ℝ)| :=
        le_of_not_gt (Finset.mem_filter.mp hellmem).2
      have hint : (∫ tau in -Ctau..Ctau,
          ‖∑ m2 ∈ m2Range,
            sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2) ≤
          2 * Ctau * Q ^ 2 := by
        have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := -Ctau) (b := Ctau) (C := Q ^ 2)
          (f := fun tau : ℝ =>
            ‖∑ m2 ∈ m2Range,
              sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2) (by
            intro tau htau
            have htIcc : tau ∈ Set.Icc (-Ctau) Ctau := by
              have := Set.uIoc_subset_uIcc htau
              simpa [Set.uIcc_of_le (by linarith : -Ctau ≤ Ctau)] using this
            have htauAbs : |tau| ≤ Ctau := by
              rw [Set.mem_Icc] at htIcc
              exact abs_le.mpr htIcc
            have hsum := norm_sigmaIIFourierSum_le_on_ellTail
              m2Range fhat j hT hS hC hM3 hM2lo hM2hi hN2 hfreq
              hm2lo hm2hi hbound ell tau hell htauAbs
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            exact (pow_le_pow_left₀ (norm_nonneg _) hsum 2))
        calc
          (∫ tau in -Ctau..Ctau,
              ‖∑ m2 ∈ m2Range,
                sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2) ≤
            |(∫ tau in -Ctau..Ctau,
              ‖∑ m2 ∈ m2Range,
                sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2)| := le_abs_self _
          _ = ‖(∫ tau in -Ctau..Ctau,
              ‖∑ m2 ∈ m2Range,
                sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2)‖ := by
            rw [Real.norm_eq_abs]
          _ ≤ Q ^ 2 * |Ctau - (-Ctau)| := hnorm
          _ = 2 * Ctau * Q ^ 2 := by
            rw [abs_of_nonneg (by linarith)]
            ring
      have hint0 : 0 ≤ (∫ tau in -Ctau..Ctau,
          ‖∑ m2 ∈ m2Range,
            sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2) := by
        apply intervalIntegral.integral_nonneg (by linarith)
        intro tau htau
        exact sq_nonneg _
      exact mul_le_mul (hpsi ell hellRange) hint hint0 hP2
    _ = ((ellRange.filter fun ell : ℤ => ¬ |(ell : ℝ)| < L).card : ℝ) *
        (P2 * (2 * Ctau * Q ^ 2)) := by simp
    _ ≤ Nell * (P2 * (2 * Ctau * Q ^ 2)) := by
      exact mul_le_mul_of_nonneg_right hNell (by positivity)
    _ = Nell * P2 * (2 * Ctau) *
        (N2 * M2hi *
          (C * T ^ eta *
            (T / (M2lo * (L - Ctau / M3))) ^ j * S)) ^ 2 := by
      dsimp only [Q, D]
      ring

/-- Uniform `T⁻¹⁰⁰` specialization of the finite-`ell` restriction. -/
theorem sigmaIIEllTailFinite_le_time_neg100
    (ellRange m2Range : Finset ℤ) (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ)
    {T S eta C M2 M3 M2lo M2hi N2 L Ctau P2 Nell Cell : ℝ} (j : ℕ)
    (hT : 0 < T) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hM3 : 0 < M3) (hM2lo : 0 ≤ M2lo) (hM2hi : 0 ≤ M2hi)
    (hN2 : (m2Range.card : ℝ) ≤ N2)
    (hCtau : 0 ≤ Ctau) (hP2 : 0 ≤ P2)
    (hNell : ((ellRange.filter fun ell : ℤ => ¬ |(ell : ℝ)| < L).card : ℝ) ≤ Nell)
    (hfreq : 0 < M2lo * (L - Ctau / M3))
    (hm2lo : ∀ m2 ∈ m2Range, M2lo ≤ |(m2 : ℝ)|)
    (hm2hi : ∀ m2 ∈ m2Range, |(m2 : ℝ)| ≤ M2hi)
    (hpsi0 : ∀ ell ∈ ellRange, 0 ≤ psi2 (M2 * (ell : ℝ) / T))
    (hpsi : ∀ ell ∈ ellRange, psi2 (M2 * (ell : ℝ) / T) ≤ P2)
    (hbound : ∀ z : ℝ, z ≠ 0 →
      ‖fhat z‖ ≤ C * T ^ eta * (T / |z|) ^ j * S)
    (hbudget : Nell * P2 * (2 * Ctau) *
      (N2 * M2hi *
        (C * T ^ eta *
          (T / (M2lo * (L - Ctau / M3))) ^ j * S)) ^ 2 * T ^ 100 ≤ Cell) :
    sigmaIIEllTailFinite ellRange m2Range L psi2 fhat M2 T M3 Ctau ≤
      Cell / T ^ 100 := by
  refine (sigmaIIEllTailFinite_le ellRange m2Range psi2 fhat j hT.le hS hC
    hM3 hM2lo hM2hi hN2 hCtau hP2 hNell hfreq hm2lo hm2hi
    hpsi0 hpsi hbound).trans ?_
  exact (le_div_iff₀ (pow_pos hT 100)).2 hbudget

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.abs_sigmaIIAffineFrequency_lower
#print axioms GuthMaynardJIteration.sourceFourierRapidDecay_at_sigmaIIAffineFrequency
#print axioms GuthMaynardJIteration.sigmaIIFinite_eq_ellRetained_add_tail
#print axioms GuthMaynardJIteration.norm_sigmaIIFourierSum_le_on_ellTail
#print axioms GuthMaynardJIteration.sigmaIIEllTailFinite_le
#print axioms GuthMaynardJIteration.sigmaIIEllTailFinite_le_time_neg100
