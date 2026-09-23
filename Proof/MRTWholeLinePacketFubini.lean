import MRTSourceWholeLineExtension
import MRTWholeLineOffDiagonalTwoIBP
import MRTWholeLineOffDiagonalAmplitudeL1

/-!
# Source-faithful Fubini and shear for the whole-line MRT packet

This module expands the unrestricted packet correlation only after the legal
whole-line extension.  It then performs the literal source substitutions
`w' = w+h` and the affine `x` integration.  All Fubini hypotheses are proved
from the compact supports of the two cutoffs.
-/

namespace MAPMRTWholeLinePacketFubini

open MeasureTheory Set
open MAPMRTProposition51HardBranch MAPMRTSourceWholeLineExtension
open MAPMRTPacketEquation82 MAPMRTCorollary53Source
open MAPMRTOffDiagonalPhase
open MAPMRTWholeLineCutoffAutocorrelation
open MAPMRTWholeLineOffDiagonalAmplitude
open MAPMRTWholeLineOffDiagonalAmplitudeL1

noncomputable section

def sourcePacketIntegrand
    (X H beta t x : ℝ) (cutoff outer : ℝ → ℝ) (w : ℝ) : ℂ :=
  additivePhase (stationaryPacketPhase X beta t w) *
    sourcePacketAmplitude X H x cutoff outer w

def sourcePacketTripleKernel
    (X H beta t t' : ℝ) (cutoff outer : ℝ → ℝ)
    (z : ℝ × (ℝ × ℝ)) : ℂ :=
  sourcePacketIntegrand X H beta t z.1 cutoff outer z.2.1 *
    star (sourcePacketIntegrand X H beta t' z.1 cutoff outer z.2.2)

private theorem continuous_additivePhase : Continuous additivePhase :=
  continuous_iff_continuousAt.mpr fun z ↦
    (MAPMRTVanDerCorputProof.hasDerivAt_additivePhase z).continuousAt

theorem continuous_sourcePacketIntegrand
    {X H beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hcutoff : Continuous cutoff) (houter : Continuous outer) :
    Continuous fun p : ℝ × ℝ ↦
      sourcePacketIntegrand X H beta t p.1 cutoff outer p.2 := by
  unfold sourcePacketIntegrand sourcePacketAmplitude stationaryPacketPhase
  exact (continuous_additivePhase.comp (by fun_prop)).mul (by fun_prop)

theorem continuous_sourcePacketTripleKernel
    {X H beta t t' : ℝ} {cutoff outer : ℝ → ℝ}
    (hcutoff : Continuous cutoff) (houter : Continuous outer) :
    Continuous (sourcePacketTripleKernel X H beta t t' cutoff outer) := by
  have ht := continuous_sourcePacketIntegrand
    (X := X) (H := H) (beta := beta) (t := t) hcutoff houter
  have ht' := continuous_sourcePacketIntegrand
    (X := X) (H := H) (beta := beta) (t := t') hcutoff houter
  have hm : Continuous fun z : ℝ × (ℝ × ℝ) ↦ (z.1, z.2.1) := by
    fun_prop
  have hm' : Continuous fun z : ℝ × (ℝ × ℝ) ↦ (z.1, z.2.2) := by
    fun_prop
  unfold sourcePacketTripleKernel
  exact (ht.comp hm).mul (Complex.continuous_conj.comp (ht'.comp hm'))

private theorem one_le_abs_div_hundred {w : ℝ} (hw : 100 ≤ |w|) :
    1 ≤ |w / 100| := by
  rw [abs_div]
  norm_num
  linarith

theorem sourcePacketIntegrand_eq_zero_of_outer
    {X H beta t x w : ℝ} {cutoff outer : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (hw : 100 ≤ |w|) :
    sourcePacketIntegrand X H beta t x cutoff outer w = 0 := by
  have hz := houterSupport (w / 100) (one_le_abs_div_hundred hw)
  simp [sourcePacketIntegrand, sourcePacketAmplitude, hz]

private theorem cutoff_center_eq_zero_of_x_outside
    {X H x w : ℝ} {cutoff : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hw : |w| ≤ 100)
    (hx : x ∉ Set.Icc (-(X * Real.exp 100 + H)) (X * Real.exp 100 + H)) :
    cutoff ((X * Real.exp w - x) / H) = 0 := by
  apply hcutoffSupport
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · have hnum : H ≤ X * Real.exp w - x := by
      have hpos : 0 < X * Real.exp w := mul_pos hX (Real.exp_pos w)
      have hM0 : 0 ≤ X * Real.exp 100 := by positivity
      linarith
    have hq : 1 ≤ (X * Real.exp w - x) / H := by
      rw [le_div_iff₀ hH]
      simpa only [one_mul] using hnum
    rw [abs_of_nonneg (by linarith)]
    exact hq
  · have hew : Real.exp w ≤ Real.exp 100 :=
      Real.exp_le_exp.mpr ((abs_le.mp hw).2)
    have hcenter : X * Real.exp w ≤ X * Real.exp 100 := by gcongr
    have hnum : X * Real.exp w - x ≤ -H := by linarith
    have hq : (X * Real.exp w - x) / H ≤ -1 := by
      rw [div_le_iff₀ hH]
      linarith
    rw [abs_of_nonpos (hq.trans (by norm_num))]
    linarith

theorem sourcePacketTripleKernel_eq_zero_outside_box
    {X H beta t t' : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (z : ℝ × (ℝ × ℝ))
    (hz : z ∉
      Set.Icc (-(X * Real.exp 100 + H)) (X * Real.exp 100 + H) ×ˢ
        (Set.Icc (-100 : ℝ) 100 ×ˢ Set.Icc (-100 : ℝ) 100)) :
    sourcePacketTripleKernel X H beta t t' cutoff outer z = 0 := by
  let Ix := Set.Icc (-(X * Real.exp 100 + H)) (X * Real.exp 100 + H)
  let Iw := Set.Icc (-100 : ℝ) 100
  by_cases hx : z.1 ∈ Ix
  · by_cases hw : z.2.1 ∈ Iw
    · by_cases hw' : z.2.2 ∈ Iw
      · exact (hz ⟨hx, hw, hw'⟩).elim
      · simp only [Iw, Set.mem_Icc, not_and_or, not_le] at hw'
        have hwo : 100 ≤ |z.2.2| := by
          rcases hw' with hw' | hw'
          · rw [abs_of_nonpos (by linarith)]
            linarith
          · rw [abs_of_nonneg (by linarith)]
            exact hw'.le
        simp [sourcePacketTripleKernel,
          sourcePacketIntegrand_eq_zero_of_outer houterSupport hwo]
    · simp only [Iw, Set.mem_Icc, not_and_or, not_le] at hw
      have hwo : 100 ≤ |z.2.1| := by
        rcases hw with hw | hw
        · rw [abs_of_nonpos (by linarith)]
          linarith
        · rw [abs_of_nonneg (by linarith)]
          exact hw.le
      simp [sourcePacketTripleKernel,
        sourcePacketIntegrand_eq_zero_of_outer houterSupport hwo]
  · by_cases hw : z.2.1 ∈ Iw
    · have hwIcc : z.2.1 ∈ Set.Icc (-100 : ℝ) 100 := by
        simpa [Iw] using hw
      have hcz := cutoff_center_eq_zero_of_x_outside hX hH hcutoffSupport
        (w := z.2.1) (x := z.1) (abs_le.mpr hwIcc) hx
      simp [sourcePacketTripleKernel, sourcePacketIntegrand,
        sourcePacketAmplitude, hcz]
    · simp only [Iw, Set.mem_Icc, not_and_or, not_le] at hw
      have hwo : 100 ≤ |z.2.1| := by
        rcases hw with hw | hw
        · rw [abs_of_nonpos (by linarith)]
          linarith
        · rw [abs_of_nonneg (by linarith)]
          exact hw.le
      simp [sourcePacketTripleKernel,
        sourcePacketIntegrand_eq_zero_of_outer houterSupport hwo]

theorem integrable_sourcePacketTripleKernel
    {X H beta t t' : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0) :
    Integrable (sourcePacketTripleKernel X H beta t t' cutoff outer) := by
  let S : Set (ℝ × (ℝ × ℝ)) :=
    Set.Icc (-(X * Real.exp 100 + H)) (X * Real.exp 100 + H) ×ˢ
      (Set.Icc (-100 : ℝ) 100 ×ˢ Set.Icc (-100 : ℝ) 100)
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hOn : IntegrableOn
      (sourcePacketTripleKernel X H beta t t' cutoff outer) S :=
    ContinuousOn.integrableOn_compact hS
      (continuous_sourcePacketTripleKernel hcutoffCont houterCont).continuousOn
  have hInd := hOn.integrable_indicator hS.measurableSet
  apply hInd.congr
  filter_upwards with z
  by_cases hz : z ∈ S
  · simp [hz]
  · have hzero := sourcePacketTripleKernel_eq_zero_outside_box
      (beta := beta) (t := t) (t' := t')
      hX hH hcutoffSupport houterSupport z hz
    simp [hz, hzero]

theorem integrable_sourcePacketIntegrand
    {X H beta t x : ℝ} {cutoff outer : ℝ → ℝ}
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0) :
    Integrable (sourcePacketIntegrand X H beta t x cutoff outer) := by
  have hc : Continuous (sourcePacketIntegrand X H beta t x cutoff outer) := by
    unfold sourcePacketIntegrand sourcePacketAmplitude stationaryPacketPhase
    exact (continuous_additivePhase.comp (by fun_prop)).mul (by fun_prop)
  have hOn : IntegrableOn (sourcePacketIntegrand X H beta t x cutoff outer)
      (Set.Icc (-100 : ℝ) 100) :=
    ContinuousOn.integrableOn_compact isCompact_Icc hc.continuousOn
  have hInd : Integrable ((Set.Icc (-100 : ℝ) 100).indicator
      (sourcePacketIntegrand X H beta t x cutoff outer)) :=
    hOn.integrable_indicator measurableSet_Icc
  apply hInd.congr
  filter_upwards with w
  by_cases hw : w ∈ Set.Icc (-100 : ℝ) 100
  · simp [hw]
  · have hw' : 100 ≤ |w| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hw
      rcases hw with hw | hw
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith)]
        exact hw.le
    have hz := sourcePacketIntegrand_eq_zero_of_outer
      (X := X) (H := H) (beta := beta) (t := t) (x := x)
      (cutoff := cutoff) houterSupport hw'
    simp [hw, hz]

private theorem integral_star_sourcePacketIntegrand
    {X H beta t x : ℝ} {cutoff outer : ℝ → ℝ}
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0) :
    (∫ w : ℝ, star (sourcePacketIntegrand X H beta t x cutoff outer w)) =
      star (∫ w : ℝ, sourcePacketIntegrand X H beta t x cutoff outer w) := by
  have hi := integrable_sourcePacketIntegrand
    (X := X) (H := H) (beta := beta) (t := t) (x := x)
    hcutoffCont houterCont houterSupport
  have h := Complex.conjCLE.toContinuousLinearMap.integral_comp_comm hi
  simpa [RCLike.star_def] using h

/-- Full Fubini expansion of the unrestricted packet correlation.  This is
the correlation produced after the legal pre-Cauchy whole-line extension;
it is not an identification with the sharp restricted correlation. -/
theorem packetCorrelation_unrestricted_eq_pair_integral_x
    {X H beta t t' : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0) :
    packetCorrelation
        (fun s x ↦ sourceStationaryPacket X H x beta s cutoff outer) t t' =
      ∫ z : ℝ × ℝ, ∫ x : ℝ,
        sourcePacketTripleKernel X H beta t t' cutoff outer (x, z) := by
  have hK := integrable_sourcePacketTripleKernel
    (beta := beta) (t := t) (t' := t')
    hX hH hcutoffCont houterCont hcutoffSupport houterSupport
  have hpoint : ∀ x : ℝ,
      sourceStationaryPacket X H x beta t cutoff outer *
          star (sourceStationaryPacket X H x beta t' cutoff outer) =
        ∫ z : ℝ × ℝ,
          sourcePacketTripleKernel X H beta t t' cutoff outer (x, z) := by
    intro x
    have hstar := integral_star_sourcePacketIntegrand
      (X := X) (H := H) (beta := beta) (t := t') (x := x)
      hcutoffCont houterCont houterSupport
    rw [show sourceStationaryPacket X H x beta t cutoff outer =
        ∫ w : ℝ, sourcePacketIntegrand X H beta t x cutoff outer w by rfl,
      show sourceStationaryPacket X H x beta t' cutoff outer =
        ∫ w : ℝ, sourcePacketIntegrand X H beta t' x cutoff outer w by rfl,
      ← hstar]
    rw [← MeasureTheory.integral_prod_mul]
    rfl
  unfold packetCorrelation
  rw [show (∫ x : ℝ,
      sourceStationaryPacket X H x beta t cutoff outer *
        star (sourceStationaryPacket X H x beta t' cutoff outer)) =
      ∫ x : ℝ, ∫ z : ℝ × ℝ,
        sourcePacketTripleKernel X H beta t t' cutoff outer (x, z) by
      apply integral_congr_ae
      filter_upwards with x
      exact hpoint x]
  exact MeasureTheory.integral_integral_swap hK

/-- The measure-preserving shear `w'=w+h`, before evaluating the `x`
integral. -/
theorem pair_integral_x_eq_sheared_integrals
    {X H beta t t' : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0) :
    (∫ z : ℝ × ℝ, ∫ x : ℝ,
        sourcePacketTripleKernel X H beta t t' cutoff outer (x, z)) =
      ∫ w : ℝ, ∫ h : ℝ, ∫ x : ℝ,
        sourcePacketTripleKernel X H beta t t' cutoff outer (x, (w, w + h)) := by
  have hK := integrable_sourcePacketTripleKernel
    (beta := beta) (t := t) (t' := t')
    hX hH hcutoffCont houterCont hcutoffSupport houterSupport
  have hF : Integrable (fun z : ℝ × ℝ ↦ ∫ x : ℝ,
      sourcePacketTripleKernel X H beta t t' cutoff outer (x, z)) :=
    hK.integral_prod_right
  calc
    (∫ z : ℝ × ℝ, ∫ x : ℝ,
        sourcePacketTripleKernel X H beta t t' cutoff outer (x, z)) =
        ∫ w : ℝ, ∫ wp : ℝ, ∫ x : ℝ,
          sourcePacketTripleKernel X H beta t t' cutoff outer (x, (w, wp)) := by
      exact MeasureTheory.integral_prod
        (fun z : ℝ × ℝ ↦ ∫ x : ℝ,
          sourcePacketTripleKernel X H beta t t' cutoff outer (x, z)) hF
    _ = ∫ w : ℝ, ∫ h : ℝ, ∫ x : ℝ,
        sourcePacketTripleKernel X H beta t t' cutoff outer (x, (w, w + h)) := by
      apply integral_congr_ae
      filter_upwards with w
      exact (MeasureTheory.integral_add_left_eq_self
        (fun wp : ℝ ↦ ∫ x : ℝ,
          sourcePacketTripleKernel X H beta t t' cutoff outer (x, (w, wp))) w).symm

private theorem additivePhase_mul_star (a b : ℝ) :
    additivePhase a * star (additivePhase b) = additivePhase (a - b) := by
  unfold additivePhase
  change Complex.exp (2 * (Real.pi : ℂ) * (a : ℂ) * Complex.I) *
    (starRingEnd ℂ) (Complex.exp (2 * (Real.pi : ℂ) * (b : ℂ) * Complex.I)) = _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem wholeLineCutoffAutocorrelation_neg
    {cutoff : ℝ → ℝ}
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (delta : ℝ) :
    wholeLineCutoffAutocorrelation cutoff (-delta) =
      wholeLineCutoffAutocorrelation cutoff delta := by
  have hforward := integral_cutoffPair_eq_wholeLineCutoffAutocorrelation
    (X0 := 0) (X1 := delta) (H := 1) (cutoff := cutoff)
    (by norm_num) hcutoffSupport
  have hbackward := integral_cutoffPair_eq_wholeLineCutoffAutocorrelation
    (X0 := delta) (X1 := 0) (H := 1) (cutoff := cutoff)
    (by norm_num) hcutoffSupport
  have hswap :
      (∫ x : ℝ, cutoff ((0 - x) / 1) * cutoff ((delta - x) / 1)) =
        ∫ x : ℝ, cutoff ((delta - x) / 1) * cutoff ((0 - x) / 1) := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hswap, hbackward] at hforward
  simpa using hforward

private theorem integrable_cutoffPair
    {X0 X1 H : ℝ} {cutoff : ℝ → ℝ}
    (hH : 0 < H) (hcutoffCont : Continuous cutoff)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0) :
    Integrable (fun x : ℝ ↦
      cutoff ((X0 - x) / H) * cutoff ((X1 - x) / H)) := by
  let f : ℝ → ℝ := fun x ↦
    cutoff ((X0 - x) / H) * cutoff ((X1 - x) / H)
  have hfCont : Continuous f := by
    unfold f
    fun_prop
  have hfZero : ∀ x ∉ Set.Icc (X0 - H) (X0 + H), f x = 0 := by
    intro x hx
    have hcut : cutoff ((X0 - x) / H) = 0 := by
      apply hcutoffSupport
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · have hq : 1 ≤ (X0 - x) / H := by
          rw [le_div_iff₀ hH]
          linarith
        rw [abs_of_nonneg (by linarith)]
        exact hq
      · have hq : (X0 - x) / H ≤ -1 := by
          rw [div_le_iff₀ hH]
          linarith
        rw [abs_of_nonpos (hq.trans (by norm_num))]
        linarith
    simp [f, hcut]
  have hOn : IntegrableOn f (Set.Icc (X0 - H) (X0 + H)) :=
    ContinuousOn.integrableOn_compact isCompact_Icc hfCont.continuousOn
  have hInd : Integrable ((Set.Icc (X0 - H) (X0 + H)).indicator f) :=
    hOn.integrable_indicator measurableSet_Icc
  have hfInt : Integrable f := by
    apply hInd.congr
    filter_upwards with x
    by_cases hx : x ∈ Set.Icc (X0 - H) (X0 + H)
    · simp [hx]
    · simp [hx, hfZero x hx]
  simpa [f] using hfInt

private theorem integral_complex_cutoffPair
    {X0 X1 H : ℝ} {cutoff : ℝ → ℝ}
    (hH : 0 < H) (hcutoffCont : Continuous cutoff)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0) :
    (∫ x : ℝ,
        ((cutoff ((X0 - x) / H) * cutoff ((X1 - x) / H) : ℝ) : ℂ)) =
      (H * wholeLineCutoffAutocorrelation cutoff ((X1 - X0) / H) : ℝ) := by
  have hi := integrable_cutoffPair (X0 := X0) (X1 := X1)
    hH hcutoffCont hcutoffSupport
  have hmap := Complex.ofRealCLM.integral_comp_comm hi
  have hreal := integral_cutoffPair_eq_wholeLineCutoffAutocorrelation
    (X0 := X0) (X1 := X1) (H := H) (cutoff := cutoff) hH hcutoffSupport
  rw [hreal] at hmap
  simpa using hmap

private theorem sourcePacketTripleKernel_shear_eq
    (X H beta t t' x w h : ℝ) (cutoff outer : ℝ → ℝ) :
    sourcePacketTripleKernel X H beta t t' cutoff outer (x, (w, w + h)) =
      additivePhase (offDiagonalPhase X beta t t' h w) *
        (((Real.exp (w / 2) * Real.exp ((w + h) / 2) *
          outer (w / 100) * outer ((w + h) / 100) : ℝ) : ℂ) *
        ((cutoff ((X * Real.exp w - x) / H) *
          cutoff ((X * Real.exp (w + h) - x) / H) : ℝ) : ℂ)) := by
  unfold sourcePacketTripleKernel sourcePacketIntegrand sourcePacketAmplitude
    offDiagonalPhase
  simp only [Prod.fst, Prod.snd]
  rw [star_mul]
  have hstarAmp :
      star ((Real.exp ((w + h) / 2) : ℂ) *
          (cutoff ((X * Real.exp (w + h) - x) / H) : ℂ) *
          (outer ((w + h) / 100) : ℂ)) =
        (Real.exp ((w + h) / 2) : ℂ) *
          (cutoff ((X * Real.exp (w + h) - x) / H) : ℂ) *
          (outer ((w + h) / 100) : ℂ) := by
    rw [show star ((Real.exp ((w + h) / 2) : ℂ) *
          (cutoff ((X * Real.exp (w + h) - x) / H) : ℂ) *
          (outer ((w + h) / 100) : ℂ)) =
        (starRingEnd ℂ) ((Real.exp ((w + h) / 2) : ℂ) *
          (cutoff ((X * Real.exp (w + h) - x) / H) : ℂ) *
          (outer ((w + h) / 100) : ℂ)) by rfl]
    simp only [map_mul, Complex.conj_ofReal]
  rw [hstarAmp]
  rw [show
      additivePhase (stationaryPacketPhase X beta t w) *
          ((Real.exp (w / 2) : ℂ) *
            (cutoff ((X * Real.exp w - x) / H) : ℂ) *
            (outer (w / 100) : ℂ)) *
        (((Real.exp ((w + h) / 2) : ℂ) *
            (cutoff ((X * Real.exp (w + h) - x) / H) : ℂ) *
            (outer ((w + h) / 100) : ℂ)) *
          star (additivePhase (stationaryPacketPhase X beta t' (w + h)))) =
        (additivePhase (stationaryPacketPhase X beta t w) *
          star (additivePhase (stationaryPacketPhase X beta t' (w + h)))) *
        (((Real.exp (w / 2) : ℂ) *
            (cutoff ((X * Real.exp w - x) / H) : ℂ) *
            (outer (w / 100) : ℂ)) *
          ((Real.exp ((w + h) / 2) : ℂ) *
            (cutoff ((X * Real.exp (w + h) - x) / H) : ℂ) *
            (outer ((w + h) / 100) : ℂ))) by ring]
  rw [additivePhase_mul_star]
  push_cast
  ring

theorem integral_x_sourcePacketTripleKernel_shear
    {X H beta t t' w h : ℝ} {cutoff outer : ℝ → ℝ}
    (hH : 0 < H) (hcutoffCont : Continuous cutoff)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0) :
    (∫ x : ℝ,
        sourcePacketTripleKernel X H beta t t' cutoff outer (x, (w, w + h))) =
      additivePhase (offDiagonalPhase X beta t t' h w) *
        (wholeLineOffDiagonalAmplitude X H cutoff outer h w : ℂ) := by
  let c : ℂ := additivePhase (offDiagonalPhase X beta t t' h w) *
    ((Real.exp (w / 2) * Real.exp ((w + h) / 2) *
      outer (w / 100) * outer ((w + h) / 100) : ℝ) : ℂ)
  rw [show (∫ x : ℝ,
      sourcePacketTripleKernel X H beta t t' cutoff outer (x, (w, w + h))) =
      ∫ x : ℝ, c *
        ((cutoff ((X * Real.exp w - x) / H) *
          cutoff ((X * Real.exp (w + h) - x) / H) : ℝ) : ℂ) by
    apply integral_congr_ae
    filter_upwards with x
    rw [sourcePacketTripleKernel_shear_eq]
    unfold c
    ring]
  rw [integral_const_mul]
  rw [integral_complex_cutoffPair hH hcutoffCont hcutoffSupport]
  have heven := wholeLineCutoffAutocorrelation_neg hcutoffSupport
    (wholeLinePacketShift X H h w)
  have harg :
      (X * Real.exp (w + h) - X * Real.exp w) / H =
        -wholeLinePacketShift X H h w := by
    unfold wholeLinePacketShift
    ring
  rw [harg, heven]
  unfold c wholeLineOffDiagonalAmplitude wholeLinePacketWeight
    wholeLineCorrelationAlong wholeLineOuterProduct
  push_cast
  ring

def wholeLineEvaluatedKernel
    (X H beta t t' : ℝ) (cutoff outer : ℝ → ℝ)
    (z : ℝ × ℝ) : ℂ :=
  additivePhase (offDiagonalPhase X beta t t' z.2 z.1) *
    (wholeLineOffDiagonalAmplitude X H cutoff outer z.2 z.1 : ℂ)

def wholeLineOffDiagonalDoubleIntegral
    (X H beta t t' : ℝ) (cutoff outer : ℝ → ℝ) : ℂ :=
  ∫ h : ℝ, ∫ w : ℝ,
    wholeLineEvaluatedKernel X H beta t t' cutoff outer (w, h)

private theorem continuous_wholeLineCutoffAutocorrelation
    {cutoff : ℝ → ℝ} (hcutoffCont : Continuous cutoff) :
    Continuous (wholeLineCutoffAutocorrelation cutoff) := by
  unfold wholeLineCutoffAutocorrelation
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry
  fun_prop

theorem continuous_wholeLineEvaluatedKernel
    {X H beta t t' : ℝ} {cutoff outer : ℝ → ℝ}
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer) :
    Continuous (wholeLineEvaluatedKernel X H beta t t' cutoff outer) := by
  have hC := continuous_wholeLineCutoffAutocorrelation hcutoffCont
  unfold wholeLineEvaluatedKernel wholeLineOffDiagonalAmplitude
    wholeLinePacketWeight wholeLineCorrelationAlong wholeLineOuterProduct
    wholeLinePacketShift offDiagonalPhase stationaryPacketPhase
  exact (continuous_additivePhase.comp (by fun_prop)).mul
    (Complex.continuous_ofReal.comp (by fun_prop))

theorem wholeLineEvaluatedKernel_eq_zero_outside_box
    {X H beta t t' : ℝ} {cutoff outer : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (z : ℝ × ℝ)
    (hz : z ∉ Set.Icc (-100 : ℝ) 100 ×ˢ Set.Icc (-200 : ℝ) 200) :
    wholeLineEvaluatedKernel X H beta t t' cutoff outer z = 0 := by
  let Iw := Set.Icc (-100 : ℝ) 100
  let Ih := Set.Icc (-200 : ℝ) 200
  by_cases hw : z.1 ∈ Iw
  · have hh : z.2 ∉ Ih := by
      intro hh
      exact hz ⟨hw, hh⟩
    have hwIcc : z.1 ∈ Set.Icc (-100 : ℝ) 100 := by simpa [Iw] using hw
    have hwh : 100 ≤ |z.1 + z.2| := by
      simp only [Ih, Set.mem_Icc, not_and_or, not_le] at hh
      rcases hh with hh | hh
      · have hsum : z.1 + z.2 ≤ -100 := by linarith [hwIcc.2, hh]
        rw [abs_of_nonpos (hsum.trans (by norm_num))]
        linarith
      · have hsum : 100 ≤ z.1 + z.2 := by linarith [hwIcc.1, hh]
        rw [abs_of_nonneg (by linarith)]
        exact hsum
    have hzero :=
      wholeLineOffDiagonalAmplitude_eq_zero_of_right_outer_support
        (X := X) (H := H) (h := z.2) (w := z.1) (cutoff := cutoff)
        houterSupport hwh
    simp [wholeLineEvaluatedKernel, hzero]
  · have hw' : z.1 ∉ Set.Icc (-100 : ℝ) 100 := by simpa [Iw] using hw
    have hwo : 100 ≤ |z.1| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hw'
      rcases hw' with hw' | hw'
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith)]
        exact hw'.le
    have hzero :=
      wholeLineOffDiagonalAmplitude_eq_zero_of_left_outer_support
        (X := X) (H := H) (h := z.2) (w := z.1) (cutoff := cutoff)
        houterSupport hwo
    simp [wholeLineEvaluatedKernel, hzero]

theorem integrable_wholeLineEvaluatedKernel
    {X H beta t t' : ℝ} {cutoff outer : ℝ → ℝ}
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0) :
    Integrable (wholeLineEvaluatedKernel X H beta t t' cutoff outer) := by
  let S : Set (ℝ × ℝ) :=
    Set.Icc (-100 : ℝ) 100 ×ˢ Set.Icc (-200 : ℝ) 200
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hOn : IntegrableOn
      (wholeLineEvaluatedKernel X H beta t t' cutoff outer) S :=
    ContinuousOn.integrableOn_compact hS
      (continuous_wholeLineEvaluatedKernel hcutoffCont houterCont).continuousOn
  have hInd := hOn.integrable_indicator hS.measurableSet
  apply hInd.congr
  filter_upwards with z
  by_cases hz : z ∈ S
  · simp [hz]
  · have hzero := wholeLineEvaluatedKernel_eq_zero_outside_box
      (X := X) (H := H) (beta := beta) (t := t) (t' := t')
      (cutoff := cutoff)
      houterSupport z hz
    simp [hz, hzero]

theorem sheared_integrals_eq_wholeLineOffDiagonalDoubleIntegral
    {X H beta t t' : ℝ} {cutoff outer : ℝ → ℝ}
    (hH : 0 < H)
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0) :
    (∫ w : ℝ, ∫ h : ℝ, ∫ x : ℝ,
        sourcePacketTripleKernel X H beta t t' cutoff outer (x, (w, w + h))) =
      wholeLineOffDiagonalDoubleIntegral X H beta t t' cutoff outer := by
  have hEval : Integrable
      (wholeLineEvaluatedKernel X H beta t t' cutoff outer) :=
    integrable_wholeLineEvaluatedKernel hcutoffCont houterCont houterSupport
  calc
    (∫ w : ℝ, ∫ h : ℝ, ∫ x : ℝ,
        sourcePacketTripleKernel X H beta t t' cutoff outer (x, (w, w + h))) =
        ∫ w : ℝ, ∫ h : ℝ,
          wholeLineEvaluatedKernel X H beta t t' cutoff outer (w, h) := by
      apply integral_congr_ae
      filter_upwards with w
      apply integral_congr_ae
      filter_upwards with h
      exact integral_x_sourcePacketTripleKernel_shear hH hcutoffCont hcutoffSupport
    _ = ∫ h : ℝ, ∫ w : ℝ,
        wholeLineEvaluatedKernel X H beta t t' cutoff outer (w, h) :=
      MeasureTheory.integral_integral_swap hEval
    _ = wholeLineOffDiagonalDoubleIntegral X H beta t t' cutoff outer := rfl

/-- Exact MRT p.50 whole-line packet identity.  The theorem deliberately
targets the unrestricted packet created before Cauchy--Schwarz and makes no
claim that it equals the later sharp restricted correlation. -/
theorem packetCorrelation_unrestricted_eq_wholeLineOffDiagonalDoubleIntegral
    {X H beta t t' : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0) :
    packetCorrelation
        (fun s x ↦ sourceStationaryPacket X H x beta s cutoff outer) t t' =
      wholeLineOffDiagonalDoubleIntegral X H beta t t' cutoff outer := by
  rw [packetCorrelation_unrestricted_eq_pair_integral_x hX hH hcutoffCont
    houterCont hcutoffSupport houterSupport]
  rw [pair_integral_x_eq_sheared_integrals hX hH hcutoffCont houterCont
    hcutoffSupport houterSupport]
  exact sheared_integrals_eq_wholeLineOffDiagonalDoubleIntegral hH hcutoffCont
    houterCont hcutoffSupport houterSupport

#print axioms packetCorrelation_unrestricted_eq_pair_integral_x
#print axioms pair_integral_x_eq_sheared_integrals
#print axioms wholeLineCutoffAutocorrelation_neg
#print axioms integral_x_sourcePacketTripleKernel_shear
#print axioms integrable_wholeLineEvaluatedKernel
#print axioms packetCorrelation_unrestricted_eq_wholeLineOffDiagonalDoubleIntegral

#print axioms integrable_sourcePacketTripleKernel

end
end MAPMRTWholeLinePacketFubini
