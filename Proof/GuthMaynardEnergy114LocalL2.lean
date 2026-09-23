import GuthMaynardLemma117Cubic
import RamachandraWeightedCauchy
import Mathlib.MeasureTheory.Function.L2Space
import GuthMaynardEnergy114KernelEnvelope

open scoped BigOperators FourierTransform ComplexConjugate SchwartzMap
open MeasureTheory
noncomputable section
namespace GuthMaynardEnergy114LocalL2
open GuthMaynardLemma117
open GuthMaynardJIteration

/-- Whole-line local L2 reproduction from the exact finite convolution identity.
The witness is fixed before the interval anchor, finite set, frequencies, coefficients, and points. -/
theorem weightedPointMassFourierKernel_local_L2
    {ι : Type*} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P : Finset ι) (x : ι → ℝ) (a : ι → ℂ) (x0 u v : ℝ),
        (∀ i ∈ P, x0 ≤ x i ∧ x i ≤ x0+1) → |u - v| ≤ 1 →
        ‖weightedPointMassFourierKernel P x a u‖ ^ 2 ≤
          C * ∫ s : ℝ, (1 / (1 + s ^ 2)) *
            ‖weightedPointMassFourierKernel P x a (v - s)‖ ^ 2 := by
  let phi : ℝ → ℝ := fun ξ =>
    ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) ξ‖
  obtain ⟨Cphi, hCphi_pos, hCphi⟩ :=
    GuthMaynardEnergy114KernelEnvelope.sourceBump_fourier_local_quadratic_envelope
  let Mphi : ℝ := ∫ ξ : ℝ, phi ξ
  let C : ℝ := Cphi * Mphi
  have hphi : Integrable phi := by
    dsimp [phi]
    exact (𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ,ℂ)).integrable.norm
  have hphi0 : ∀ ξ, 0 ≤ phi ξ := by intro ξ; dsimp [phi]; positivity
  have hCphi0 : 0 ≤ Cphi := hCphi_pos.le
  have hMphi : 0 ≤ Mphi := integral_nonneg (fun ξ => hphi0 ξ)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro P x a x0 u v hinterval huv
  let K : ℝ → ℝ := fun t => ‖weightedPointMassFourierKernel P x a t‖
  let mass : ℝ := weightedCoefficientMass P a
  have hKcont : Continuous K := by
    dsimp [K]
    unfold weightedPointMassFourierKernel
    fun_prop
  have hmass : 0 ≤ mass := by
    dsimp [mass, weightedCoefficientMass]
    positivity
  have hK0 : ∀ t, 0 ≤ K t := by intro t; dsimp [K]; positivity
  have hKle : ∀ t, K t ≤ mass := by
    intro t
    dsimp [K, mass]
    exact norm_weightedPointMassFourierKernel_le_mass P x a t
  let w : ℝ → ℝ := phi
  let g : ℝ → ℝ := fun ξ => phi ξ * K (u - ξ) ^ 2
  have hgmeas : AEStronglyMeasurable g := by
    apply Continuous.aestronglyMeasurable
    dsimp [g, phi, K, weightedPointMassFourierKernel]
    fun_prop
  have hboundg : ∀ ξ, g ξ ≤ mass ^ 2 * phi ξ := by
    intro ξ
    dsimp [g]
    have hk := hKle (u - ξ)
    have := pow_le_pow_left₀ (hK0 _) hk 2
    have hm := mul_le_mul_of_nonneg_left this (hphi0 ξ)
    simpa [mul_comm] using hm
  have hg : Integrable g := by
    apply (hphi.mul_const (mass ^ 2)).mono' hgmeas
    filter_upwards [] with ξ
    simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ g ξ), mul_comm] using
      hboundg ξ
  have hwm : Integrable w := by simpa [w] using hphi
  have hlin : Integrable (fun ξ : ℝ => phi ξ * K (u - ξ)) := by
    have hm : AEStronglyMeasurable (fun ξ : ℝ => phi ξ * K (u - ξ)) :=
      hphi.1.mul (hKcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    apply (hphi.mul_const mass).mono' hm
    filter_upwards [] with ξ
    simpa [Real.norm_eq_abs, abs_of_nonneg (hphi0 ξ), abs_of_nonneg (hK0 (u-ξ))] using
      (mul_le_mul_of_nonneg_left (hKle (u-ξ)) (hphi0 ξ))
  have hconv := weightedPointMassFourierKernel_eq_scaled_convolution
    P x a (x0 := x0) (L := 1) (tau := u) (by norm_num) hinterval
  have hcs :
      ‖weightedPointMassFourierKernel P x a u‖ ^ 2 ≤
        Mphi * ∫ ξ : ℝ, g ξ := by
    let f : ℝ → ℂ := fun ξ =>
      (𝓕 (sourceBumpSchwartz 1 zero_lt_one)) ξ *
        intervalTranslationPhase x0 1 ξ *
        weightedPointMassFourierKernel P x a (u - ξ)
    have hfmeas : AEStronglyMeasurable f := by
      have hfour : Continuous (fun ξ : ℝ =>
          (𝓕 (sourceBumpSchwartz 1 zero_lt_one)) ξ) :=
        (𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ,ℂ)).continuous
      have hphase : Continuous (fun ξ : ℝ => intervalTranslationPhase x0 1 ξ) := by
        unfold intervalTranslationPhase
        fun_prop
      have hKshift : Continuous (fun ξ : ℝ => K (u - ξ)) :=
        hKcont.comp (continuous_const.sub continuous_id)
      have hTcont : Continuous (fun t : ℝ =>
          weightedPointMassFourierKernel P x a t) := by
        unfold weightedPointMassFourierKernel
        fun_prop
      have hTshift : Continuous (fun ξ : ℝ =>
          weightedPointMassFourierKernel P x a (u - ξ)) :=
        hTcont.comp (continuous_const.sub continuous_id)
      have hphK : Continuous (fun ξ : ℝ =>
          intervalTranslationPhase x0 1 ξ *
            weightedPointMassFourierKernel P x a (u - ξ)) :=
        hphase.mul hTshift
      simpa [f, mul_assoc, Pi.mul_def] using! (hfour.mul hphK).aestronglyMeasurable
    have hf : Integrable f := by
      apply hlin.mono' hfmeas
      filter_upwards [] with ξ
      dsimp [f, phi, K]
      rw [norm_mul, norm_mul, norm_intervalTranslationPhase]
      convert le_rfl using 1 <;> ring
    have hfg : ∀ ξ, ‖f ξ‖ ≤ Real.sqrt (w ξ) * Real.sqrt (g ξ) := by
      intro ξ
      dsimp [f, w, g, phi, K]
      rw [norm_mul, norm_mul, norm_intervalTranslationPhase]
      have hp := hphi0 ξ
      have hk := norm_nonneg (weightedPointMassFourierKernel P x a (u - ξ))
      rw [Real.sqrt_mul hp, Real.sqrt_sq hk]
      have hs : Real.sqrt (phi ξ) ^ 2 = phi ξ := Real.sq_sqrt hp
      nlinarith
    have hcw := RamachandraWeightedCauchy.norm_integral_sq_le_integral_mul_integral
      f w g hf hwm hg (fun ξ => hphi0 ξ) (fun ξ => by positivity) hfg
    rw [hconv]
    simpa [f, div_one] using hcw
  have hshift : ∀ s : ℝ, phi (s + (u-v)) ≤
      Cphi / (1 + s ^ 2) := by
    intro s
    have hh := hCphi (s + (u-v)) (v-u) (by
      simpa [abs_sub_comm] using huv)
    simpa [phi, add_assoc] using hh
  have htranslate :
      ∫ ξ : ℝ, g ξ = ∫ s : ℝ,
        phi (s + (u-v)) * K (v-s) ^ 2 := by
    let δ : ℝ := u - v
    calc
      ∫ ξ : ℝ, g ξ = ∫ s : ℝ, g (s + δ) := by
        symm
        exact integral_add_right_eq_self g δ
      _ = ∫ s : ℝ, phi (s + (u-v)) * K (v-s) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [] with s
        dsimp [g, δ]
        congr 2
        ring
  have hmono :
      (∫ s : ℝ, phi (s + (u-v)) * K (v-s) ^ 2) ≤
        Cphi * ∫ s : ℝ, (1 / (1 + s ^ 2)) * K (v-s) ^ 2 := by
    have hphi_shift : Integrable (fun s : ℝ => phi (s + (u-v))) := by
      simpa [add_comm] using hphi.comp_add_right (u-v)
    have hleft : Integrable (fun s : ℝ => phi (s + (u-v)) * K (v-s)^2) := by
      have hm : AEStronglyMeasurable (fun s : ℝ => phi (s + (u-v)) * K (v-s)^2) :=
        hphi_shift.1.mul ((hKcont.comp (continuous_const.sub continuous_id)).pow 2).aestronglyMeasurable
      apply (hphi_shift.mul_const (mass ^ 2)).mono' hm
      filter_upwards [] with s
      simpa [Real.norm_eq_abs, abs_of_nonneg (hphi0 (s + (u-v))),
        abs_of_nonneg (hK0 (v-s))] using
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hK0 _) (hKle _) 2)
          (hphi0 _))
    have hI : Integrable (fun s : ℝ => (1 / (1 + s^2)) * K (v-s)^2) := by
      have hb : Integrable (fun s : ℝ => (1 : ℝ) / (1 + s^2)) :=
        GuthMaynardEnergy114KernelEnvelope.inv_one_add_sq_integrable
      have hweightcont : Continuous (fun s : ℝ => (1 / (1 + s^2) : ℝ)) := by
        apply continuous_const.div₀ (continuous_const.add (continuous_id.pow 2))
        intro s
        dsimp
        nlinarith [sq_nonneg s]
      have hKshift : Continuous (fun s : ℝ => K (v-s)) :=
        hKcont.comp (continuous_const.sub continuous_id)
      have hm : AEStronglyMeasurable (fun s : ℝ => (1 / (1 + s^2)) * K (v-s)^2) := by
        exact (hweightcont.mul (hKshift.pow 2)).aestronglyMeasurable
      apply (hb.mul_const (mass ^ 2)).mono' hm
      filter_upwards [] with s
      have hk := pow_le_pow_left₀ (hK0 _) (hKle (v-s)) 2
      have hdenpos : 0 < (1 + s^2 : ℝ) := by positivity
      simpa [Real.norm_eq_abs, abs_of_pos hdenpos,
        abs_of_nonneg (hK0 (v-s))] using
        (mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ (1 / (1 + s^2) : ℝ)))
    have hI' : Integrable (fun s : ℝ => (Cphi / (1 + s^2)) * K (v-s)^2) := by
      have hconst := hI.const_mul Cphi
      convert hconst using 1 <;> ext s <;> ring
    exact calc
      _ ≤ ∫ s : ℝ, (Cphi / (1 + s ^ 2)) * K (v-s) ^ 2 := by
        apply integral_mono hleft hI'
        intro s
        exact mul_le_mul_of_nonneg_right (hshift s) (sq_nonneg _)
      _ = Cphi * ∫ s : ℝ, (1 / (1 + s ^ 2)) * K (v-s)^2 := by
        rw [← integral_const_mul Cphi]
        apply integral_congr_ae
        filter_upwards [] with s
        ring
  change ‖weightedPointMassFourierKernel P x a u‖ ^ 2 ≤
    (Cphi * Mphi) * ∫ s : ℝ, (1 / (1 + s ^ 2)) *
      ‖weightedPointMassFourierKernel P x a (v - s)‖ ^ 2
  exact calc
    ‖weightedPointMassFourierKernel P x a u‖ ^ 2 ≤ Mphi * ∫ ξ, g ξ := hcs
    _ = Mphi * ∫ s, phi (s + (u-v)) * K (v-s)^2 := by rw [htranslate]
    _ ≤ Mphi * (Cphi * ∫ s, (1/(1+s^2))*K (v-s)^2) :=
      mul_le_mul_of_nonneg_left hmono hMphi
    _ = _ := by ring

#print axioms GuthMaynardEnergy114LocalL2.weightedPointMassFourierKernel_local_L2
end GuthMaynardEnergy114LocalL2
