import MRTEquation79PacketBilinearCore
import MRTFaithfulEquation81Weld
import MRTWholeLinePacketMemLp
import MAPFinishP51FaithfulIntegrability

/-!
# Faithful equation (79) packet-bilinear bridge

This file supplies the deterministic square-expansion/Fubini bridge missing
between the faithful equation-(79) amplitude and the equation-(81) packet
correlation bilinear.
-/

namespace MAPMRTFaithfulEquation79Bilinear

set_option maxHeartbeats 800000

open MeasureTheory Set
open MAPMRTProposition51HardBranch MAPMRTMediumEq79Parallel
open MAPMRTFaithfulSmoothCutoff MAPMRTWholeLinePacketMemLp
open MAPMRTEquation79PacketBilinearCore
open MAPMRTWholeLineEquation81FromEquation82
open MAPMRTCorollary53Source MAPMRTProposition51Source

noncomputable section

/-- The faithful packet is jointly continuous in its frequency and spatial
variables.  The compact outer cutoff supplies a parameter-independent
integrable majorant in the logarithmic integration variable. -/
theorem continuous_faithfulSourcePacket_joint
    (X H beta : ℝ) :
    Continuous (fun p : ℝ × ℝ ↦
      sourceStationaryPacket X H p.2 beta p.1 faithfulCutoff faithfulCutoff) := by
  have hinterval : Continuous (fun p : ℝ × ℝ ↦
      stationaryPacketOn X beta p.1
        (sourcePacketAmplitude X H p.2 faithfulCutoff faithfulCutoff)
        (-100) 100) := by
    unfold stationaryPacketOn
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    unfold Function.uncurry sourcePacketAmplitude
    have hadd : Continuous MAPMRTCorollary53Source.additivePhase :=
      continuous_iff_continuousAt.mpr (fun y ↦
        (MAPMRTVanDerCorputProof.hasDerivAt_additivePhase y).continuousAt)
    have hphase : Continuous (fun a : (ℝ × ℝ) × ℝ ↦
        stationaryPacketPhase X beta a.1.1 a.2) := by
      unfold stationaryPacketPhase
      fun_prop
    have hcenter : Continuous (fun a : (ℝ × ℝ) × ℝ ↦
        faithfulCutoff ((X * Real.exp a.2 - a.1.2) / H)) :=
      faithfulCutoff_continuous.comp (by fun_prop)
    have houter : Continuous (fun a : (ℝ × ℝ) × ℝ ↦
        faithfulCutoff (a.2 / 100)) :=
      faithfulCutoff_continuous.comp (by fun_prop)
    exact (hadd.comp hphase).mul
      (((Complex.continuous_ofReal.comp (by fun_prop)).mul
        (Complex.continuous_ofReal.comp hcenter)).mul
        (Complex.continuous_ofReal.comp houter))
  convert hinterval using 1
  funext p
  exact MAPMRTVanDerCorput.sourceStationaryPacket_eq_onOuterWindow
    (fun y hy ↦ faithfulCutoff_zero_of_one_le hy)

theorem sourceTilde_continuous
    (N : ℕ) (X beta eta : ℝ) (f : ℕ → ℂ)
    (hX : 0 < X) (hbeta : beta ≠ 0) (heta : 0 < eta) :
    Continuous (sourceTildePolynomial N X beta eta faithfulCutoff f) := by
  unfold sourceTildePolynomial mediumCutoffMultiplier
  have hb : 0 < |beta| := abs_pos.mpr hbeta
  have hd1 : |beta| * X ≠ 0 := ne_of_gt (mul_pos hb hX)
  have hd2 : 10 * eta * |beta| * X ≠ 0 := by positivity
  have hpoly : Continuous (finiteCriticalPolynomial N f) := by
    unfold finiteCriticalPolynomial MixedMeanFrontend.mellinPhase
    fun_prop
  exact (continuous_const.mul hpoly |>.mul
    (show Continuous (xMellinPhase X) by
      unfold xMellinPhase
      fun_prop)).mul
    ((Complex.continuous_ofReal.comp
      (faithfulCutoff_continuous.comp (by fun_prop))).sub
      (Complex.continuous_ofReal.comp
        (faithfulCutoff_continuous.comp (by fun_prop))))

theorem sourceTilde_eq_zero_outside_interval
    {N : ℕ} {X beta eta t : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hbeta : beta ≠ 0)
    (heta : 0 < eta) (hetaSmall : eta < 1 / 100)
    (ht : t ∉ Set.Icc (-(|beta| * X / eta)) (|beta| * X / eta)) :
    sourceTildePolynomial N X beta eta faithfulCutoff f t = 0 := by
  apply sourceTildePolynomial_eq_zero_off_sourceFrequencyRegion
    hX hbeta heta hetaSmall
    (fun y hy ↦ faithfulCutoff_one hy)
    (fun y hy ↦ faithfulCutoff_zero_of_one_le hy)
  intro hreg
  apply ht
  rw [Set.mem_Icc]
  exact (abs_le.mp hreg.2)

/-- The exact three-variable energy kernel for the faithful equation-(79)
amplitude and packet is integrable. -/
theorem faithful_packetEnergyTripleKernel_integrable
    {N : ℕ} {X H beta eta : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hbeta : beta ≠ 0)
    (heta : 0 < eta) (hetaSmall : eta < 1 / 100) :
    Integrable (packetEnergyTripleKernel
      (sourceTildePolynomial N X beta eta faithfulCutoff f)
      (fun r x ↦ sourceStationaryPacket X H x beta r
        faithfulCutoff faithfulCutoff))
      (volume.prod (volume.prod volume)) := by
  let A : ℝ → ℂ := sourceTildePolynomial N X beta eta faithfulCutoff f
  let J : ℝ → ℝ → ℂ := fun r x ↦
    sourceStationaryPacket X H x beta r faithfulCutoff faithfulCutoff
  let B : ℝ := |beta| * X / eta
  let C : ℝ := X * Real.exp 100 + H
  let S : Set (ℝ × (ℝ × ℝ)) :=
    Set.Icc (-C) C ×ˢ (Set.Icc (-B) B ×ˢ Set.Icc (-B) B)
  have hcontA : Continuous A := sourceTilde_continuous N X beta eta f hX hbeta heta
  have hcontJ : Continuous (fun p : ℝ × ℝ ↦ J p.1 p.2) := by
    simpa [J] using continuous_faithfulSourcePacket_joint X H beta
  have hx : Continuous (fun z : ℝ × (ℝ × ℝ) ↦ z.1) := continuous_fst
  have ht1 : Continuous (fun z : ℝ × (ℝ × ℝ) ↦ z.2.1) :=
    continuous_fst.comp continuous_snd
  have ht2 : Continuous (fun z : ℝ × (ℝ × ℝ) ↦ z.2.2) :=
    continuous_snd.comp continuous_snd
  have hJ1 : Continuous (fun z : ℝ × (ℝ × ℝ) ↦ J z.2.1 z.1) := by
    change Continuous (fun z : ℝ × (ℝ × ℝ) ↦
      (fun p : ℝ × ℝ ↦ J p.1 p.2) (z.2.1, z.1))
    exact hcontJ.comp (ht1.prodMk hx)
  have hJ2 : Continuous (fun z : ℝ × (ℝ × ℝ) ↦ J z.2.2 z.1) := by
    change Continuous (fun z : ℝ × (ℝ × ℝ) ↦
      (fun p : ℝ × ℝ ↦ J p.1 p.2) (z.2.2, z.1))
    exact hcontJ.comp (ht2.prodMk hx)
  have hA1 : Continuous (fun z : ℝ × (ℝ × ℝ) ↦ A z.2.1) := hcontA.comp ht1
  have hA2 : Continuous (fun z : ℝ × (ℝ × ℝ) ↦ A z.2.2) := hcontA.comp ht2
  have hcont : Continuous (packetEnergyTripleKernel A J) := by
    unfold packetEnergyTripleKernel
    exact (hA1.mul hJ1).mul (Complex.continuous_conj.comp (hA2.mul hJ2))
  have hsupp : Function.support (packetEnergyTripleKernel A J) ⊆ S := by
    intro z hz
    have hx : z.1 ∈ Set.Icc (-C) C := by
      by_contra hx
      have hj : J z.2.1 z.1 = 0 := by
        apply sourceStationaryPacket_eq_zero_outside_compact hX hH
          (fun y hy ↦ faithfulCutoff_zero_of_one_le hy)
          (fun y hy ↦ faithfulCutoff_zero_of_one_le hy)
        simpa [C] using hx
      exact hz (by simp [packetEnergyTripleKernel, J, hj])
    have ht : z.2.1 ∈ Set.Icc (-B) B := by
      by_contra ht
      have ha : A z.2.1 = 0 := by
        apply sourceTilde_eq_zero_outside_interval hX hbeta heta hetaSmall
        simpa [B] using ht
      exact hz (by simp [packetEnergyTripleKernel, A, ha])
    have ht' : z.2.2 ∈ Set.Icc (-B) B := by
      by_contra ht'
      have ha : A z.2.2 = 0 := by
        apply sourceTilde_eq_zero_outside_interval hX hbeta heta hetaSmall
        simpa [B] using ht'
      exact hz (by simp [packetEnergyTripleKernel, A, ha])
    exact ⟨hx, ht, ht'⟩
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact
      ((isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))) hsupp)

/-- The correlation-side integrability required by the deterministic
packet-bilinear theorem follows from the preceding triple-kernel Fubini fact. -/
theorem faithful_weightedPacketCorrelation_integrable
    {N : ℕ} {X H beta eta : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hbeta : beta ≠ 0)
    (heta : 0 < eta) (hetaSmall : eta < 1 / 100) :
    Integrable (Function.uncurry (fun t t' : ℝ ↦
      sourceTildePolynomial N X beta eta faithfulCutoff f t *
      star (sourceTildePolynomial N X beta eta faithfulCutoff f t') *
      MAPMRTPacketEquation82.packetCorrelation
        (fun r x ↦ sourceStationaryPacket X H x beta r
          faithfulCutoff faithfulCutoff) t t'))
      (volume.prod volume) := by
  let A : ℝ → ℂ := sourceTildePolynomial N X beta eta faithfulCutoff f
  let J : ℝ → ℝ → ℂ := fun r x ↦
    sourceStationaryPacket X H x beta r faithfulCutoff faithfulCutoff
  have htriple := faithful_packetEnergyTripleKernel_integrable
    (N := N) (f := f) hX hH hbeta heta hetaSmall
  have hsw := htriple.swap.integral_prod_left
  apply hsw.congr
  filter_upwards [htriple.swap.prod_right_ae] with z hz
  change (∫ x : ℝ, (A z.1 * J z.1 x) * star (A z.2 * J z.2 x)) =
    A z.1 * star (A z.2) *
      ∫ x : ℝ, J z.1 x * star (J z.2 x)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [Complex.star_def, map_mul]
  ring

/-- Fully unconditional deterministic equation-(79) packet-energy bound for
the faithful source cutoff. -/
theorem faithful_equation79PacketEnergy_le_packetCorrelationBilinear
    {N : ℕ} {X H beta eta : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hbeta : beta ≠ 0)
    (heta : 0 < eta) (hetaSmall : eta < 1 / 100) :
    ENNReal.ofReal (∫ x : ℝ,
      ‖packetSuperposition
        (sourceTildePolynomial N X beta eta faithfulCutoff f)
        (fun r x ↦ sourceStationaryPacket X H x beta r
          faithfulCutoff faithfulCutoff) x‖ ^ 2) ≤
      packetCorrelationBilinear
        (fun r x ↦ sourceStationaryPacket X H x beta r
          faithfulCutoff faithfulCutoff)
        (fun t ↦ ENNReal.ofReal
          ‖sourceTildePolynomial N X beta eta faithfulCutoff f t‖) := by
  exact ofReal_integral_norm_sq_packetSuperposition_le_bilinear
    (faithful_packetEnergyTripleKernel_integrable
      (N := N) (f := f) hX hH hbeta heta hetaSmall)
    (faithful_weightedPacketCorrelation_integrable
      (N := N) (f := f) hX hH hbeta heta hetaSmall)

#print axioms continuous_faithfulSourcePacket_joint
#print axioms faithful_packetEnergyTripleKernel_integrable
#print axioms faithful_weightedPacketCorrelation_integrable
#print axioms faithful_equation79PacketEnergy_le_packetCorrelationBilinear

end
end MAPMRTFaithfulEquation79Bilinear
