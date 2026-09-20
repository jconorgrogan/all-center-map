import GuthMaynardJIterationSourceFourierDecay
import GuthMaynardJIterationFrequencyBounds

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- Direct finite-sum bound for the actual Fourier transform of the source
`g`.  Every range cardinality, bump norm, dilation ratio, and Fourier bound is
separate. -/
theorem norm_fourier_sourceGFinite_le_of_fhat_bound
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 f : ℝ → ℂ) (hf : Integrable f) (M3 xi : ℝ)
    {N1 N2 N3 P1 Rhi D : ℝ}
    (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (hN3 : 0 ≤ N3)
    (hP1 : 0 ≤ P1) (hRhi : 0 ≤ Rhi) (hD0 : 0 ≤ D)
    (hcard1 : (m1Range.card : ℝ) ≤ N1)
    (hcard2 : (m2Range.card : ℝ) ≤ N2)
    (hcard3 : (m3Range.card : ℝ) ≤ N3)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0)
    (hpsi : ∀ m3 ∈ m3Range, ‖psi1 ((m3 : ℝ) / M3)‖ ≤ P1)
    (hratio : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      |((m2 : ℝ) / (m1 : ℝ))| ≤ Rhi)
    (hfhat : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      ‖FourierTransform.fourier f
        (((m2 : ℝ) / (m1 : ℝ)) * xi)‖ ≤ D) :
    ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ≤
      N1 * N2 * N3 * P1 * Rhi * D := by
  rw [fourier_sourceGFinite m1Range m2Range m3Range psi1 f hf M3 xi hm1 hm2]
  calc
    ‖∑ m1 ∈ m1Range, ∑ m2 ∈ m2Range, ∑ m3 ∈ m3Range,
        psi1 ((m3 : ℝ) / M3) *
          sourcePhase (((m3 : ℝ) / (m1 : ℝ)) * xi) *
            (((|((m2 : ℝ) / (m1 : ℝ))| : ℝ) : ℂ) *
              FourierTransform.fourier f
                (((m2 : ℝ) / (m1 : ℝ)) * xi))‖ ≤
      ∑ m1 ∈ m1Range,
        ‖∑ m2 ∈ m2Range, ∑ m3 ∈ m3Range,
          psi1 ((m3 : ℝ) / M3) *
            sourcePhase (((m3 : ℝ) / (m1 : ℝ)) * xi) *
              (((|((m2 : ℝ) / (m1 : ℝ))| : ℝ) : ℂ) *
                FourierTransform.fourier f
                  (((m2 : ℝ) / (m1 : ℝ)) * xi))‖ := norm_sum_le _ _
    _ ≤ ∑ m1 ∈ m1Range, ∑ m2 ∈ m2Range,
        ‖∑ m3 ∈ m3Range,
          psi1 ((m3 : ℝ) / M3) *
            sourcePhase (((m3 : ℝ) / (m1 : ℝ)) * xi) *
              (((|((m2 : ℝ) / (m1 : ℝ))| : ℝ) : ℂ) *
                FourierTransform.fourier f
                  (((m2 : ℝ) / (m1 : ℝ)) * xi))‖ := by
      apply Finset.sum_le_sum
      intro m1 hm1mem
      exact norm_sum_le _ _
    _ ≤ ∑ m1 ∈ m1Range, ∑ m2 ∈ m2Range, ∑ m3 ∈ m3Range,
        ‖psi1 ((m3 : ℝ) / M3) *
          sourcePhase (((m3 : ℝ) / (m1 : ℝ)) * xi) *
            (((|((m2 : ℝ) / (m1 : ℝ))| : ℝ) : ℂ) *
              FourierTransform.fourier f
                (((m2 : ℝ) / (m1 : ℝ)) * xi))‖ := by
      apply Finset.sum_le_sum
      intro m1 hm1mem
      apply Finset.sum_le_sum
      intro m2 hm2mem
      exact norm_sum_le _ _
    _ ≤ ∑ _m1 ∈ m1Range, ∑ _m2 ∈ m2Range, ∑ _m3 ∈ m3Range,
        P1 * Rhi * D := by
      apply Finset.sum_le_sum
      intro m1 hm1mem
      apply Finset.sum_le_sum
      intro m2 hm2mem
      apply Finset.sum_le_sum
      intro m3 hm3mem
      calc
        ‖psi1 ((m3 : ℝ) / M3) *
            sourcePhase (((m3 : ℝ) / (m1 : ℝ)) * xi) *
              (((|((m2 : ℝ) / (m1 : ℝ))| : ℝ) : ℂ) *
                FourierTransform.fourier f
                  (((m2 : ℝ) / (m1 : ℝ)) * xi))‖ =
          ‖psi1 ((m3 : ℝ) / M3)‖ *
            (|((m2 : ℝ) / (m1 : ℝ))| *
              ‖FourierTransform.fourier f
                (((m2 : ℝ) / (m1 : ℝ)) * xi)‖) := by
          rw [norm_mul, norm_mul, norm_mul, norm_sourcePhase,
            Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (abs_nonneg _)]
          ring
        _ ≤ P1 * (Rhi * D) := by
          exact mul_le_mul (hpsi m3 hm3mem)
            (mul_le_mul (hratio m1 hm1mem m2 hm2mem)
              (hfhat m1 hm1mem m2 hm2mem) (norm_nonneg _) hRhi)
            (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hP1
        _ = P1 * Rhi * D := by ring
    _ = (m1Range.card : ℝ) * (m2Range.card : ℝ) *
        (m3Range.card : ℝ) * P1 * Rhi * D := by simp; ring
    _ ≤ N1 * N2 * N3 * P1 * Rhi * D := by
      gcongr

/-- Source rapid decay propagated through all three finite ranges of `g`, in
the exact reciprocal-power form before the integrable-envelope conversion. -/
theorem norm_fourier_sourceGFinite_le_sourceDecay
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 f : ℝ → ℂ) (hf : Integrable f) (M3 xi : ℝ)
    {T S eta C Rlo N1 N2 N3 P1 Rhi : ℝ} (p : ℕ)
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hRlo : 0 < Rlo)
    (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (hN3 : 0 ≤ N3)
    (hP1 : 0 ≤ P1) (hRhi : 0 ≤ Rhi)
    (hcard1 : (m1Range.card : ℝ) ≤ N1)
    (hcard2 : (m2Range.card : ℝ) ≤ N2)
    (hcard3 : (m3Range.card : ℝ) ≤ N3)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0)
    (hpsi : ∀ m3 ∈ m3Range, ‖psi1 ((m3 : ℝ) / M3)‖ ≤ P1)
    (hratioLo : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      Rlo ≤ |((m2 : ℝ) / (m1 : ℝ))|)
    (hratioHi : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      |((m2 : ℝ) / (m1 : ℝ))| ≤ Rhi)
    (hxi : xi ≠ 0)
    (hbound : ∀ {m1 m2 xi : ℝ},
      m1 ≠ 0 → m2 ≠ 0 → xi ≠ 0 →
      ‖FourierTransform.fourier f ((m2 / m1) * xi)‖ ≤
        C * T ^ eta * (T / (|m2 / m1| * |xi|)) ^ p * S) :
    ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ≤
      N1 * N2 * N3 * P1 * Rhi *
        (C * T ^ eta * (T / (Rlo * |xi|)) ^ p * S) := by
  apply norm_fourier_sourceGFinite_le_of_fhat_bound
    m1Range m2Range m3Range psi1 f hf M3 xi
    hN1 hN2 hN3 hP1 hRhi (by positivity)
    hcard1 hcard2 hcard3 hm1 hm2 hpsi hratioHi
  intro m1 hm1mem m2 hm2mem
  exact sourceFourierRapidDecay_at_ratio_lower
    (FourierTransform.fourier f) p hT hS hC hRlo hbound
    (by exact_mod_cast hm1 m1 hm1mem)
    (by exact_mod_cast hm2 m2 hm2mem) hxi (hratioLo m1 hm1mem m2 hm2mem)

/-- Conversion of the preceding source bound to the exact envelope expected
by the promoted high-frequency integral theorem. -/
theorem norm_fourier_sourceGFinite_le_decayEnvelope
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 f : ℝ → ℂ) (hf : Integrable f) (M3 xi : ℝ)
    {T S eta C Rlo N1 N2 N3 P1 Rhi : ℝ} (p : ℕ)
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hRlo : 0 < Rlo)
    (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (hN3 : 0 ≤ N3)
    (hP1 : 0 ≤ P1) (hRhi : 0 ≤ Rhi)
    (hcard1 : (m1Range.card : ℝ) ≤ N1)
    (hcard2 : (m2Range.card : ℝ) ≤ N2)
    (hcard3 : (m3Range.card : ℝ) ≤ N3)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0)
    (hpsi : ∀ m3 ∈ m3Range, ‖psi1 ((m3 : ℝ) / M3)‖ ≤ P1)
    (hratioLo : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      Rlo ≤ |((m2 : ℝ) / (m1 : ℝ))|)
    (hratioHi : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      |((m2 : ℝ) / (m1 : ℝ))| ≤ Rhi)
    (hxi : 1 ≤ |xi|)
    (hbound : ∀ {m1 m2 xi : ℝ},
      m1 ≠ 0 → m2 ≠ 0 → xi ≠ 0 →
      ‖FourierTransform.fourier f ((m2 / m1) * xi)‖ ≤
        C * T ^ eta * (T / (|m2 / m1| * |xi|)) ^ p * S) :
    ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ≤
      (N1 * N2 * N3 * P1 * Rhi *
        (C * T ^ eta * (T / Rlo) ^ p * 2 ^ p * S)) /
          (1 + |xi|) ^ p := by
  have hraw := norm_fourier_sourceGFinite_le_sourceDecay
    m1Range m2Range m3Range psi1 f hf M3 xi p hT hS hC hRlo
    hN1 hN2 hN3 hP1 hRhi hcard1 hcard2 hcard3 hm1 hm2 hpsi
    hratioLo hratioHi (abs_pos.mp (lt_of_lt_of_le (by norm_num) hxi)) hbound
  refine hraw.trans ?_
  have hxine : xi ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by norm_num) hxi)
  have hrecip := reciprocal_abs_pow_le_one_add_abs hxi p
  have hfactor : 0 ≤ N1 * N2 * N3 * P1 * Rhi * (C * T ^ eta) *
      (T / Rlo) ^ p * S := by positivity
  calc
    N1 * N2 * N3 * P1 * Rhi *
        (C * T ^ eta * (T / (Rlo * |xi|)) ^ p * S) =
      (N1 * N2 * N3 * P1 * Rhi * (C * T ^ eta) *
        (T / Rlo) ^ p * S) * (1 / |xi|) ^ p := by
        field_simp [hRlo.ne', hxine]
        ring
    _ ≤ (N1 * N2 * N3 * P1 * Rhi * (C * T ^ eta) *
        (T / Rlo) ^ p * S) * (2 ^ p / (1 + |xi|) ^ p) :=
      mul_le_mul_of_nonneg_left hrecip hfactor
    _ = (N1 * N2 * N3 * P1 * Rhi *
        (C * T ^ eta * (T / Rlo) ^ p * 2 ^ p * S)) /
          (1 + |xi|) ^ p := by ring

/-- Literal high-frequency region `III = O(T⁻¹⁰⁰)` for the finite source
`g`, obtained from the source Fourier-decay specialization rather than assumed
as a bound on `ghat`. -/
theorem sourceGFinite_highFrequencyIntegral_le_time_neg100
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 f : ℝ → ℂ) (hf : Integrable f) (M3 : ℝ) (q : ℕ)
    {T S eta Cdec Rlo N1 N2 N3 P1 Rhi CIII : ℝ}
    (hT : 1 ≤ T) (hS : 0 ≤ S) (hCdec : 0 ≤ Cdec)
    (hRlo : 0 < Rlo)
    (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (hN3 : 0 ≤ N3)
    (hP1 : 0 ≤ P1) (hRhi : 0 ≤ Rhi)
    (hcard1 : (m1Range.card : ℝ) ≤ N1)
    (hcard2 : (m2Range.card : ℝ) ≤ N2)
    (hcard3 : (m3Range.card : ℝ) ≤ N3)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0)
    (hpsi : ∀ m3 ∈ m3Range, ‖psi1 ((m3 : ℝ) / M3)‖ ≤ P1)
    (hratioLo : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      Rlo ≤ |((m2 : ℝ) / (m1 : ℝ))|)
    (hratioHi : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      |((m2 : ℝ) / (m1 : ℝ))| ≤ Rhi)
    (hbound : ∀ {m1 m2 xi : ℝ},
      m1 ≠ 0 → m2 ≠ 0 → xi ≠ 0 →
      ‖FourierTransform.fourier f ((m2 / m1) * xi)‖ ≤
        Cdec * T ^ eta *
          (T / (|m2 / m1| * |xi|)) ^ (q + 2) * S)
    (hghat : IntegrableOn
      (fun xi =>
        ‖FourierTransform.fourier
          (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ^ 2)
      (highFrequencyRegion (sourceHighFrequencyCutoff T)))
    (hbudget :
      ((N1 * N2 * N3 * P1 * Rhi *
          (Cdec * T ^ eta * (T / Rlo) ^ (q + 2) * 2 ^ (q + 2) * S)) /
        (sourceHighFrequencyCutoff T) ^ q) ^ 2 *
          quarticDecayMass * T ^ 100 ≤ CIII) :
    (∫ xi in highFrequencyRegion (sourceHighFrequencyCutoff T),
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ^ 2) ≤
      CIII / T ^ 100 := by
  let K : ℝ := N1 * N2 * N3 * P1 * Rhi *
    (Cdec * T ^ eta * (T / Rlo) ^ (q + 2) * 2 ^ (q + 2) * S)
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hdecay : ∀ xi ∈ highFrequencyRegion (sourceHighFrequencyCutoff T),
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ≤
        K / (1 + |xi|) ^ (q + 2) := by
    intro xi hxi
    have hcut1 : 1 ≤ sourceHighFrequencyCutoff T := by
      unfold sourceHighFrequencyCutoff
      exact one_le_pow₀ hT
    have hxi1 : 1 ≤ |xi| := le_trans hcut1 hxi.le
    exact norm_fourier_sourceGFinite_le_decayEnvelope
      m1Range m2Range m3Range psi1 f hf M3 xi (q + 2)
      (le_trans (by norm_num) hT) hS hCdec hRlo hN1 hN2 hN3 hP1 hRhi
      hcard1 hcard2 hcard3 hm1 hm2 hpsi hratioLo hratioHi hxi1 hbound
  apply sourceHighFrequencyIntegral_le_time_neg100
    (fun xi => FourierTransform.fourier
      (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi)
    q hK (lt_of_lt_of_le (by norm_num) hT) hdecay hghat
  simpa only [K] using hbudget

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.norm_fourier_sourceGFinite_le_of_fhat_bound
#print axioms GuthMaynardJIteration.norm_fourier_sourceGFinite_le_sourceDecay
#print axioms GuthMaynardJIteration.norm_fourier_sourceGFinite_le_decayEnvelope
#print axioms GuthMaynardJIteration.sourceGFinite_highFrequencyIntegral_le_time_neg100
