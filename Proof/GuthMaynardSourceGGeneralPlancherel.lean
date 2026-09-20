import GuthMaynardGeneralPlancherel
import GuthMaynardJIterationSourceHighFrequency
import GuthMaynardAffineSmoothingNorms

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- The literal finite source function is `L¹` whenever its profile is, with
only the source's nonzero numerator/denominator conditions. -/
theorem integrable_sourceGFinite
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 f : ℝ → ℂ) (hf : Integrable f) (M3 : ℝ)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0) :
    Integrable (sourceGFinite m1Range m2Range m3Range psi1 f M3) := by
  unfold sourceGFinite
  apply integrable_finsetSum m1Range
  intro m1 hm1mem
  apply integrable_finsetSum m2Range
  intro m2 hm2mem
  apply integrable_finsetSum m3Range
  intro m3 hm3mem
  exact integrable_sourceGSummand psi1 f hf M3 m1 m2 m3
    (hm1 m1 hm1mem) (hm2 m2 hm2mem)

/-- Continuity of the literal finite source function. -/
theorem continuous_sourceGFinite
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 f : ℝ → ℂ) (hf : Continuous f) (M3 : ℝ)
    :
    Continuous (sourceGFinite m1Range m2Range m3Range psi1 f M3) := by
  unfold sourceGFinite sourceGSummand
  fun_prop

/-- A direct pointwise-decay Plancherel weld for the finite source function.
This replaces the earlier auxiliary Schwartz representative. -/
theorem integral_norm_sq_fourier_sourceGFinite_of_decay_four
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 f : ℝ → ℂ) (hf : Integrable f) (hfc : Continuous f)
    (M3 : ℝ)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0)
    {K : ℝ}
    (hdecay : ∀ xi, 1 ≤ |xi| →
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ≤
          K / (1 + |xi|) ^ 4) :
    (∫ xi : ℝ,
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ^ 2) =
      ∫ u : ℝ,
        ‖sourceGFinite m1Range m2Range m3Range psi1 f M3 u‖ ^ 2 := by
  exact integral_norm_sq_fourier_eq_of_decay_four
    (sourceGFinite m1Range m2Range m3Range psi1 f M3)
    (integrable_sourceGFinite m1Range m2Range m3Range psi1 f hf M3 hm1 hm2)
    (continuous_sourceGFinite m1Range m2Range m3Range psi1 f hfc M3)
    hdecay

/-- The source rapid-decay quantifier itself supplies the preceding fourth-
order envelope.  Hence exact Plancherel holds for every admissible profile;
no Schwartz strengthening is present in the signature. -/
theorem integral_norm_sq_fourier_sourceGFinite_of_sourceProfile
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 : ℝ → ℂ) {fReal : ℝ → ℝ}
    {T S F M3 eta Rlo N1 N2 N3 P1 Rhi : ℝ}
    (hf : SourceAdmissibleProfile T S F fReal)
    (heta : 0 < eta) (hT : 0 ≤ T)
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
      |((m2 : ℝ) / (m1 : ℝ))| ≤ Rhi) :
    (∫ xi : ℝ,
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1
          (fun u : ℝ => (fReal u : ℂ)) M3) xi‖ ^ 2) =
      ∫ u : ℝ,
        ‖sourceGFinite m1Range m2Range m3Range psi1
          (fun u : ℝ => (fReal u : ℂ)) M3 u‖ ^ 2 := by
  obtain ⟨Cdec, hCdec, hbound⟩ :=
    sourceFourierRapidDecay_at_dyadicRatio
      (FourierTransform.fourier (fun u : ℝ => (fReal u : ℂ)))
      hf.rapidDecay heta 4
  let K : ℝ := N1 * N2 * N3 * P1 * Rhi *
    (Cdec * T ^ eta * (T / Rlo) ^ 4 * 2 ^ 4 * S)
  have hS : 0 ≤ S := hf.bound_nonneg
  apply integral_norm_sq_fourier_sourceGFinite_of_decay_four
    m1Range m2Range m3Range psi1 (fun u : ℝ => (fReal u : ℂ))
    hf.integrable.ofReal
    (Complex.continuous_ofReal.comp hf.continuous) M3 hm1 hm2
  intro xi hxi
  exact norm_fourier_sourceGFinite_le_decayEnvelope
    m1Range m2Range m3Range psi1 (fun u : ℝ => (fReal u : ℂ))
    hf.integrable.ofReal M3 xi 4 hT hS hCdec hRlo
    hN1 hN2 hN3 hP1 hRhi hcard1 hcard2 hcard3 hm1 hm2 hpsi
    hratioLo hratioHi hxi hbound

/-- The same source profile hypotheses also give ordinary integrability of
the squared Fourier norm.  This is the premise needed by the low/medium/high
region decomposition; it removes the older auxiliary Schwartz witness from
those source-facing consumers. -/
theorem integrable_norm_sq_fourier_sourceGFinite_of_sourceProfile
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 : ℝ → ℂ) {fReal : ℝ → ℝ}
    {T S F M3 eta Rlo N1 N2 N3 P1 Rhi : ℝ}
    (hf : SourceAdmissibleProfile T S F fReal)
    (heta : 0 < eta) (hT : 0 ≤ T)
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
      |((m2 : ℝ) / (m1 : ℝ))| ≤ Rhi) :
    Integrable (fun xi : ℝ =>
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1
          (fun u : ℝ => (fReal u : ℂ)) M3) xi‖ ^ 2) := by
  let g : ℝ → ℂ := sourceGFinite m1Range m2Range m3Range psi1
    (fun u : ℝ => (fReal u : ℂ)) M3
  obtain ⟨Cdec, hCdec, hbound⟩ :=
    sourceFourierRapidDecay_at_dyadicRatio
      (FourierTransform.fourier (fun u : ℝ => (fReal u : ℂ)))
      hf.rapidDecay heta 2
  let K : ℝ := N1 * N2 * N3 * P1 * Rhi *
    (Cdec * T ^ eta * (T / Rlo) ^ 2 * 2 ^ 2 * S)
  let G : ℝ → ℝ := fun xi => ‖FourierTransform.fourier g xi‖ ^ 2
  let major : ℝ → ℝ := fun xi => K ^ 2 * quarticDecayEnvelope xi
  have hgInt : Integrable g := integrable_sourceGFinite
    m1Range m2Range m3Range psi1 (fun u : ℝ => (fReal u : ℂ))
    hf.integrable.ofReal M3 hm1 hm2
  have hfourierCont : Continuous (FourierTransform.fourier g) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ hgInt
  have hGCont : Continuous G := by
    dsimp only [G]
    fun_prop
  have hmajorInt : Integrable major :=
    integrable_quarticDecayEnvelope.const_mul (K ^ 2)
  have hdecay : ∀ xi, 1 ≤ |xi| → G xi ≤ major xi := by
    intro xi hxi
    have hnorm : ‖FourierTransform.fourier g xi‖ ≤
        K / (1 + |xi|) ^ 2 := by
      dsimp only [g, K]
      exact norm_fourier_sourceGFinite_le_decayEnvelope
        m1Range m2Range m3Range psi1 (fun u : ℝ => (fReal u : ℂ))
        hf.integrable.ofReal M3 xi 2 hT hf.bound_nonneg hCdec hRlo
        hN1 hN2 hN3 hP1 hRhi hcard1 hcard2 hcard3 hm1 hm2 hpsi
        hratioLo hratioHi hxi hbound
    have hright0 : 0 ≤ K / (1 + |xi|) ^ 2 := by
      have hK : 0 ≤ K := by
        dsimp only [K]
        positivity [Real.rpow_nonneg hT eta, hf.bound_nonneg]
      positivity
    calc
      G xi = ‖FourierTransform.fourier g xi‖ ^ 2 := rfl
      _ ≤ (K / (1 + |xi|) ^ 2) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hright0).2 hnorm
      _ = major xi := by
        dsimp only [major, quarticDecayEnvelope]
        field_simp
  let I : Set ℝ := Set.Icc (-1 : ℝ) 1
  have hinside : IntegrableOn G I := hGCont.integrableOn_Icc
  have houtside : IntegrableOn G Iᶜ := by
    apply hmajorInt.integrableOn.mono' hGCont.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem (measurableSet_Icc.compl)] with xi hxi
    have habs : 1 ≤ |xi| := by
      by_contra hnot
      apply hxi
      rw [Set.mem_Icc, ← abs_le]
      exact le_of_not_ge hnot
    have hG0 : 0 ≤ G xi := by dsimp only [G]; positivity
    have hmajor0 : 0 ≤ major xi := by
      dsimp only [major, quarticDecayEnvelope]
      positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hG0, abs_of_nonneg hmajor0]
      using hdecay xi habs
  have hunion := hinside.union houtside
  rw [Set.union_compl_self I] at hunion
  simpa only [G] using integrableOn_univ.mp hunion

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.integrable_sourceGFinite
#print axioms GuthMaynardJIteration.continuous_sourceGFinite
#print axioms GuthMaynardJIteration.integral_norm_sq_fourier_sourceGFinite_of_decay_four
#print axioms GuthMaynardJIteration.integral_norm_sq_fourier_sourceGFinite_of_sourceProfile
#print axioms GuthMaynardJIteration.integrable_norm_sq_fourier_sourceGFinite_of_sourceProfile
