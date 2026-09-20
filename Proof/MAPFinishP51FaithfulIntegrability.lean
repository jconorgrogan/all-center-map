import MAPFinishP51Medium79
import MAPFaithfulCutoffDual
import MRTSourcePacketSupport

/-!
# Faithful cutoff integrability for MRT equation (79)

This module instantiates every Bochner-integrability hypothesis in the exact
one-scale equation-(79) constructor with the canonical compact smooth cutoff
and the faithful logarithmic dual function.
-/

namespace MAPFinishP51FaithfulIntegrability

open MeasureTheory Set
open MAPMRTProposition51Source MAPMRTMediumEq79Parallel
open MAPFinishP51Medium79 MAPFaithfulCutoffDual
open MAPMRTProposition51HardBranch MAPAllCenterApertureTransfer
open MAPMRTFaithfulSmoothCutoff

noncomputable section

/-- The generic Fubini kernel specializes definitionally to the literal one. -/
theorem oneScaleFubiniKernel_faithful_eq
    (T u : ℝ) (G : ℝ → ℂ) :
    oneScaleFubiniKernel T u faithfulCutoff G =
      faithfulOneScaleFubiniKernel T u G := by
  funext v y
  unfold oneScaleFubiniKernel faithfulOneScaleFubiniKernel
  ring

/-- Concrete legality of the projection-side Fubini interchange. -/
theorem faithful_oneScaleFubiniKernel_integrable
    {T u : ℝ} {G : ℝ → ℂ} (hT : 0 < T) (hG : Integrable G) :
    Integrable (Function.uncurry
      (oneScaleFubiniKernel T u faithfulCutoff G))
      (volume.prod volume) := by
  rw [oneScaleFubiniKernel_faithful_eq]
  exact MAPFaithfulCutoffDual.faithfulOneScaleFubiniKernel_integrable hT hG

/-- The transformed coefficient kernel is integrable for the faithful cutoff
at every positive scale. -/
theorem faithful_transformedOneScaleSummand_integrable
    {X T : ℝ} {f : ℕ → ℂ} {G : ℝ → ℂ} (n : ℕ)
    (hT : 0 < T) (hG : Integrable G) :
    Integrable (Function.uncurry
      (transformedOneScaleSummand X T faithfulCutoff f G n))
      (volume.prod volume) := by
  have hTne : T⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hT)
  have hcut : Integrable (fun t : ℝ ↦ (faithfulCutoff (T⁻¹ * t) : ℂ)) :=
    (integrable_comp_mul_left_iff
      (fun y : ℝ ↦ (faithfulCutoff y : ℂ)) hTne).2
      faithfulCutoff_integrable_complex
  have hbase : Integrable (Function.uncurry (fun t w : ℝ ↦
      (faithfulCutoff (T⁻¹ * t) : ℂ) * G w))
      (volume.prod volume) := hcut.mul_prod hG
  let phase : ℝ × ℝ → ℂ := fun z ↦
    Complex.exp
      (-(((z.1 * (Real.log n - Real.log X) : ℝ) : ℂ) * Complex.I)) *
      Complex.exp ((((z.1 * z.2 : ℝ) : ℂ) * Complex.I))
  have hphaseMeas : AEStronglyMeasurable phase (volume.prod volume) := by
    exact (show Continuous phase by
      unfold phase
      fun_prop).aestronglyMeasurable
  have hphaseBound : ∀ᶠ z : ℝ × ℝ in ae (volume.prod volume), ‖phase z‖ ≤ 1 :=
    Filter.Eventually.of_forall fun z ↦ by
      unfold phase
      rw [norm_mul,
        show -(((z.1 * (Real.log n - Real.log X) : ℝ) : ℂ) * Complex.I) =
          (((-(z.1 * (Real.log n - Real.log X)) : ℝ) : ℂ) *
            Complex.I) by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
        one_mul]
  have hmul := hbase.bdd_mul hphaseMeas hphaseBound
  have hcoef := hmul.const_mul (f n * (Real.sqrt n : ℂ)⁻¹)
  convert hcoef using 1
  funext z
  rcases z with ⟨t, w⟩
  unfold transformedOneScaleSummand Function.uncurry phase
  simp only [Prod.fst, Prod.snd]
  rw [show T⁻¹ * t = t / T by field_simp [ne_of_gt hT]]
  ring

/-- The complete one-scale source integrand is integrable for the literal
cutoff, obtained by summing the preceding finite coefficient kernels. -/
theorem faithful_oneScale_source_integrand_integrable
    {N : ℕ} {X T : ℝ} {f : ℕ → ℂ} {G : ℝ → ℂ}
    (hT : 0 < T) (hG : Integrable G) :
    Integrable (Function.uncurry (fun t w : ℝ ↦
      finiteCriticalPolynomial N f t * G w * xMellinPhase X t *
        Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)) *
          (faithfulCutoff (t / T) : ℂ))) (volume.prod volume) := by
  have hsum : Integrable (Function.uncurry (fun t w : ℝ ↦
      ∑ n ∈ Finset.Icc 1 N,
        transformedOneScaleSummand X T faithfulCutoff f G n t w))
      (volume.prod volume) := by
    apply integrable_finset_sum
    intro n hn
    exact faithful_transformedOneScaleSummand_integrable n hT hG
  apply hsum.congr
  filter_upwards with z
  rcases z with ⟨t, w⟩
  exact sum_transformedOneScaleSummand_eq_source_integrand

/-- All four literal integrability inputs used by equation (79), simultaneously
at the two source scales. -/
theorem faithful_equation79_integrability_package
    {N : ℕ} {X beta eta : ℝ} {f : ℕ → ℂ} {G : ℝ → ℂ}
    (hX : 0 < X) (hbeta : beta ≠ 0) (heta : 0 < eta)
    (hG : Integrable G) :
    (∀ n ∈ Finset.Icc 1 N,
      Integrable (Function.uncurry (oneScaleFubiniKernel
        (|beta| * X / eta) (Real.log n - Real.log X) faithfulCutoff G))
        (volume.prod volume)) ∧
    (∀ n ∈ Finset.Icc 1 N,
      Integrable (Function.uncurry (oneScaleFubiniKernel
        (10 * eta * |beta| * X) (Real.log n - Real.log X)
          faithfulCutoff G)) (volume.prod volume)) ∧
    (∀ n ∈ Finset.Icc 1 N,
      Integrable (Function.uncurry (transformedOneScaleSummand X
        (|beta| * X / eta) faithfulCutoff f G n)) (volume.prod volume)) ∧
    (∀ n ∈ Finset.Icc 1 N,
      Integrable (Function.uncurry (transformedOneScaleSummand X
        (10 * eta * |beta| * X) faithfulCutoff f G n))
        (volume.prod volume)) ∧
    Integrable (Function.uncurry (fun t w : ℝ ↦
      finiteCriticalPolynomial N f t * G w * xMellinPhase X t *
        Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)) *
          (faithfulCutoff (t / (|beta| * X / eta)) : ℂ)))
        (volume.prod volume) ∧
    Integrable (Function.uncurry (fun t w : ℝ ↦
      finiteCriticalPolynomial N f t * G w * xMellinPhase X t *
        Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)) *
          (faithfulCutoff (t / (10 * eta * |beta| * X)) : ℂ)))
        (volume.prod volume) := by
  have hhiT : 0 < |beta| * X / eta := by positivity
  have hloT : 0 < 10 * eta * |beta| * X := by positivity
  exact ⟨fun n hn ↦ faithful_oneScaleFubiniKernel_integrable hhiT hG,
    fun n hn ↦ faithful_oneScaleFubiniKernel_integrable hloT hG,
    fun n hn ↦ faithful_transformedOneScaleSummand_integrable n hhiT hG,
    fun n hn ↦ faithful_transformedOneScaleSummand_integrable n hloT hG,
    faithful_oneScale_source_integrand_integrable hhiT hG,
    faithful_oneScale_source_integrand_integrable hloT hG⟩

/-- Fully source-specialized equation-(79) integrability package.  The
function `G` is now the faithful compact logarithmic dual generated by an
integrable dual witness supported on `[X/2,4X]`. -/
theorem faithfulDual_equation79_integrability_package
    {N : ℕ} {epsilon X beta eta : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 4 ≤ X) (hbeta : beta ≠ 0) (heta : 0 < eta)
    (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0) :
    (∀ n ∈ Finset.Icc 1 N,
      Integrable (Function.uncurry (oneScaleFubiniKernel
        (|beta| * X / eta) (Real.log n - Real.log X) faithfulCutoff
          (faithfulLogarithmicDualFunction epsilon X beta g)))
        (volume.prod volume)) ∧
    (∀ n ∈ Finset.Icc 1 N,
      Integrable (Function.uncurry (oneScaleFubiniKernel
        (10 * eta * |beta| * X) (Real.log n - Real.log X) faithfulCutoff
          (faithfulLogarithmicDualFunction epsilon X beta g)))
        (volume.prod volume)) ∧
    (∀ n ∈ Finset.Icc 1 N,
      Integrable (Function.uncurry (transformedOneScaleSummand X
        (|beta| * X / eta) faithfulCutoff f
          (faithfulLogarithmicDualFunction epsilon X beta g) n))
        (volume.prod volume)) ∧
    (∀ n ∈ Finset.Icc 1 N,
      Integrable (Function.uncurry (transformedOneScaleSummand X
        (10 * eta * |beta| * X) faithfulCutoff f
          (faithfulLogarithmicDualFunction epsilon X beta g) n))
        (volume.prod volume)) ∧
    Integrable (Function.uncurry (fun t w : ℝ ↦
      finiteCriticalPolynomial N f t *
        faithfulLogarithmicDualFunction epsilon X beta g w *
        xMellinPhase X t *
        Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)) *
          (faithfulCutoff (t / (|beta| * X / eta)) : ℂ)))
        (volume.prod volume) ∧
    Integrable (Function.uncurry (fun t w : ℝ ↦
      finiteCriticalPolynomial N f t *
        faithfulLogarithmicDualFunction epsilon X beta g w *
        xMellinPhase X t *
        Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)) *
          (faithfulCutoff (t / (10 * eta * |beta| * X)) : ℂ)))
        (volume.prod volume) := by
  apply faithful_equation79_integrability_package
    (by linarith : 0 < X) hbeta heta
  exact faithfulLogarithmicDualFunction_integrable hX hg hgSupport

/-- The product of the source dual with the packet using the canonical
compact outer cutoff is integrable.  This is the bounded-multiplier argument
on the literal packet, independent of the equation-(79) Fubini package. -/
theorem faithfulDual_packet_literalOuter_integrable
    {epsilon X beta packetT : ℝ} {g : ℝ → ℂ}
    (hX : 4 ≤ X) (hg : Integrable g) :
    Integrable (fun x : ℝ ↦ g x *
      sourceStationaryPacket X (baseAperture epsilon X) x beta packetT
        faithfulCutoff faithfulCutoff) := by
  have hpacketCont : Continuous (fun x : ℝ ↦
      sourceStationaryPacket X (baseAperture epsilon X) x beta packetT
        faithfulCutoff faithfulCutoff) :=
    MAPMRTSourcePacketSupport.continuous_sourceStationaryPacket_in_x
      faithfulCutoff_continuous faithfulCutoff_continuous
      (fun y hy ↦ faithfulCutoff_zero_of_one_le hy)
  have hmul := hg.bdd_mul hpacketCont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦
      MAPMRTSourcePacketSupport.norm_sourceStationaryPacket_le_outer
        (X := X) (H := baseAperture epsilon X) (beta := beta) (t := packetT)
        (x := x) (cutoff := faithfulCutoff) (outerCutoff := faithfulCutoff)
        (fun y hy ↦ faithfulCutoff_zero_of_one_le hy)
        abs_faithfulCutoff_le_one abs_faithfulCutoff_le_one)
  simpa [mul_comm] using hmul

/-- Integrability before outer-cutoff insertion.  On the compact support of
`g`, the no-outer packet equals the packet with the canonical literal outer
cutoff; off that support both products vanish. -/
theorem faithfulDual_packet_noOuter_integrable
    {epsilon X beta packetT : ℝ} {g : ℝ → ℂ}
    (hX : 4 ≤ X) (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0) :
    Integrable (fun x : ℝ ↦ g x *
      sourceStationaryPacket X (baseAperture epsilon X) x beta packetT
        faithfulCutoff (fun _ ↦ 1)) := by
  have hbase := faithfulDual_packet_literalOuter_integrable
    (epsilon := epsilon) (beta := beta) (packetT := packetT) hX hg
  apply hbase.congr
  filter_upwards with x
  by_cases hx : x ∈ Set.Icc (X / 2) (4 * X)
  · have hXpos : 0 < X := by linarith
    have hHpos : 0 < baseAperture epsilon X := baseAperture_pos hXpos
    have hQuarter : baseAperture epsilon X ≤ X / 4 :=
      MAPMRTSourceBaseApertureOuterCutoffWeld.baseAperture_le_quarter_of_four_le hX
    have hp :=
      MAPMRTSourceBaseApertureOuterCutoffWeld.sourceStationaryPacket_eq_withoutOuter_of_quarterRange
        (X := X) (H := baseAperture epsilon X) (x := x)
        (beta := beta) (t := packetT)
        (cutoff := faithfulCutoff) (outer := faithfulCutoff)
        hXpos hHpos hQuarter hx
        (fun y hy ↦ faithfulCutoff_zero_of_one_le hy)
        (fun y hy ↦ faithfulCutoff_one (hy.trans (by norm_num)))
    rw [hp]
  · simp [hgSupport x hx]

/-- Integrability after insertion of any outer cutoff with the source plateau.
This remains a separate fact from the no-outer case: exact packet equality on
the support of `g` transports the already-proved integrability. -/
theorem faithfulDual_packet_outer_integrable
    {epsilon X beta packetT : ℝ} {outer : ℝ → ℝ} {g : ℝ → ℂ}
    (hX : 4 ≤ X) (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1) :
    Integrable (fun x : ℝ ↦ g x *
      sourceStationaryPacket X (baseAperture epsilon X) x beta packetT
        faithfulCutoff outer) := by
  have hbase := faithfulDual_packet_noOuter_integrable
    (epsilon := epsilon) (beta := beta) (packetT := packetT)
    hX hg hgSupport
  apply hbase.congr
  filter_upwards with x
  by_cases hx : x ∈ Set.Icc (X / 2) (4 * X)
  · have hXpos : 0 < X := by linarith
    have hHpos : 0 < baseAperture epsilon X := baseAperture_pos hXpos
    have hQuarter : baseAperture epsilon X ≤ X / 4 :=
      MAPMRTSourceBaseApertureOuterCutoffWeld.baseAperture_le_quarter_of_four_le hX
    have hp :=
      MAPMRTSourceBaseApertureOuterCutoffWeld.sourceStationaryPacket_eq_withoutOuter_of_quarterRange
        (X := X) (H := baseAperture epsilon X) (x := x)
        (beta := beta) (t := packetT)
        (cutoff := faithfulCutoff) (outer := outer)
        hXpos hHpos hQuarter hx
        (fun y hy ↦ faithfulCutoff_zero_of_one_le hy) houterOne
    rw [hp]
  · simp [hgSupport x hx]

/-- Source-facing equation-(79) weld for the actual compact logarithmic dual.
All six projection/transform integrability obligations are discharged by the
preceding package.  The two remaining packet integrability inputs are kept
separate because they concern respectively the packet before and after outer
cutoff insertion. -/
theorem faithfulDual_medium79_transform_movingWindow_and_baseAperture_collar
    {epsilon X beta eta packetT : ℝ} {outer : ℝ → ℝ}
    {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 4 ≤ X) (hbeta : beta ≠ 0)
    (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1) :
    ((∑ n ∈ Finset.Icc 1 ⌊2 * X⌋₊,
        f n * (Real.sqrt n : ℂ)⁻¹ *
          mediumFrequencyProjection X beta eta faithfulCutoff
            (faithfulLogarithmicDualFunction epsilon X beta g)
            (Real.log n - Real.log X)) =
      equation79Integral ⌊2 * X⌋₊ X beta eta faithfulCutoff f
        (faithfulLogarithmicDualFunction epsilon X beta g)) ∧
    proposition51ILintegral ⌊2 * X⌋₊ X (baseAperture epsilon X)
        f beta eta = ENNReal.ofReal
          (proposition51I X (baseAperture epsilon X) f beta eta) ∧
    (∫ x : ℝ, g x *
        sourceStationaryPacket X (baseAperture epsilon X) x beta packetT
          faithfulCutoff (fun _ ↦ 1)) =
      ∫ x : ℝ, g x *
        sourceStationaryPacket X (baseAperture epsilon X) x beta packetT
          faithfulCutoff outer := by
  have hpkg := faithfulDual_equation79_integrability_package
    (N := ⌊2 * X⌋₊) (epsilon := epsilon) (f := f)
    hX hbeta heta hg hgSupport
  have hNoOuter : Integrable (fun x : ℝ ↦ g x *
      sourceStationaryPacket X (baseAperture epsilon X) x beta packetT
        faithfulCutoff (fun _ ↦ 1)) :=
    faithfulDual_packet_noOuter_integrable hX hg hgSupport
  have hOuter : Integrable (fun x : ℝ ↦ g x *
      sourceStationaryPacket X (baseAperture epsilon X) x beta packetT
        faithfulCutoff outer) :=
    faithfulDual_packet_outer_integrable hX hg hgSupport houterOne
  exact medium79_transform_movingWindow_and_baseAperture_collar_of_integrable
    hX hbeta heta hetaOne
    hpkg.1 hpkg.2.1 hpkg.2.2.1 hpkg.2.2.2.1
    hpkg.2.2.2.2.1 hpkg.2.2.2.2.2
    hgSupport (fun y hy ↦ faithfulCutoff_zero_of_one_le hy)
    houterOne hNoOuter hOuter

#print axioms oneScaleFubiniKernel_faithful_eq
#print axioms faithful_oneScaleFubiniKernel_integrable
#print axioms faithful_transformedOneScaleSummand_integrable
#print axioms faithful_oneScale_source_integrand_integrable
#print axioms faithful_equation79_integrability_package
#print axioms faithfulDual_equation79_integrability_package
#print axioms faithfulDual_packet_literalOuter_integrable
#print axioms faithfulDual_packet_noOuter_integrable
#print axioms faithfulDual_packet_outer_integrable
#print axioms faithfulDual_medium79_transform_movingWindow_and_baseAperture_collar

end
end MAPFinishP51FaithfulIntegrability
