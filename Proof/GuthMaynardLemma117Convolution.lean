import AppendixA8A9Certified
import GuthMaynardJIterationBumpWeld
import GuthMaynardRatioKernelIdentity

/-!
# Exact convolution identity behind Guth--Maynard Lemma 11.7

The source smooths the finite point-mass Fourier kernel after placing `W` in
an interval of length `T`.  This file certifies that identity with the exact
Fourier signs and scaling.  No tail estimate or local-constancy inequality is
assumed here.
-/

open scoped BigOperators FourierTransform ComplexConjugate SchwartzMap
open MeasureTheory

namespace GuthMaynardLemma117

open FourierRealPartRemoval GuthMaynardJIteration
open GuthMaynardRatioKernelIdentity

noncomputable section

/-- The harmless unit-modulus translation phase in Lemma 11.7. -/
def intervalTranslationPhase (x0 T xi : ℝ) : ℂ :=
  Complex.exp (-((2 * Real.pi * x0 * xi / T : ℝ) : ℂ) * Complex.I)

theorem norm_intervalTranslationPhase (x0 T xi : ℝ) :
    ‖intervalTranslationPhase x0 T xi‖ = 1 := by
  unfold intervalTranslationPhase
  rw [Complex.norm_exp]
  simp

/-- Exact source identity

`W-hat(tau) = integral psi-hat(xi) e(-x0 xi/T)
                         W-hat(tau-xi/T) dxi`,

where `psi` is one on `[0,1]`. -/
theorem pointMassFourierKernel_eq_scaled_convolution
    (W : Finset ℝ) {x0 T tau : ℝ} (hT : 0 < T)
    (hinterval : ∀ t ∈ W, x0 ≤ t ∧ t ≤ x0 + T) :
    pointMassFourierKernel W tau =
      ∫ xi : ℝ,
        (𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi *
          intervalTranslationPhase x0 T xi *
          pointMassFourierKernel W (tau - xi/T) := by
  let psi : 𝓢(ℝ, ℂ) := sourceBumpSchwartz 1 zero_lt_one
  let a : ℝ → ℂ := fun t =>
    Complex.exp (-((2 * Real.pi * t * tau : ℝ) : ℂ) * Complex.I)
  let u : ℝ → ℝ := fun t => (t-x0)/T
  have hu : ∀ t ∈ W, |u t| ≤ 1 := by
    intro t ht
    have hi := hinterval t ht
    have hu0 : 0 ≤ u t := div_nonneg (sub_nonneg.mpr hi.1) hT.le
    have hu1 : u t ≤ 1 := by
      apply (div_le_one hT).2
      linarith
    rw [abs_of_nonneg hu0]
    exact hu1
  have hpsi : ∀ t ∈ W, psi (u t) = 1 := by
    intro t ht
    change (sourceBump 1 zero_lt_one (u t) : ℂ) = 1
    rw [sourceBump_eq_one_of_abs_le 1 zero_lt_one (hu t ht)]
    norm_num
  have hfourier := finite_fourier_real_part_removal W a u psi
  calc
    pointMassFourierKernel W tau = ∑ t ∈ W, a t * psi (u t) := by
      unfold pointMassFourierKernel a
      apply Finset.sum_congr rfl
      intro t ht
      rw [hpsi t ht]
      simp
    _ = ∫ xi : ℝ, (𝓕 psi : 𝓢(ℝ, ℂ)) xi *
          ∑ t ∈ W, a t * positiveFourierPhase (u t) xi := hfourier
    _ = ∫ xi : ℝ,
        (𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi *
          intervalTranslationPhase x0 T xi *
          pointMassFourierKernel W (tau-xi/T) := by
      apply integral_congr_ae
      filter_upwards with xi
      dsimp only [psi]
      calc
        (𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi *
            (∑ t ∈ W, a t * positiveFourierPhase (u t) xi) =
          (𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi *
            (intervalTranslationPhase x0 T xi *
              pointMassFourierKernel W (tau-xi/T)) := by
          congr 1
          unfold pointMassFourierKernel intervalTranslationPhase
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          dsimp only [a, u, positiveFourierPhase]
          rw [← Complex.exp_add, ← Complex.exp_add]
          congr 1
          push_cast
          field_simp [hT.ne']
          ring
        _ = (𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi *
              intervalTranslationPhase x0 T xi *
                pointMassFourierKernel W (tau-xi/T) := by ring
    _ = ∫ xi : ℝ,
        (𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi *
          intervalTranslationPhase x0 T xi *
          pointMassFourierKernel W (tau-xi/T) := rfl
  all_goals rfl

set_option maxHeartbeats 800000 in
/-- Taking norms in the certified convolution identity loses only the
absolute Fourier weight.  The ratio kernel is finite, so the majorant is
integrable without an additional hypothesis. -/
theorem norm_pointMassFourierKernel_le_scaled_convolution
    (W : Finset ℝ) {x0 T tau : ℝ} (hT : 0 < T)
    (hinterval : ∀ t ∈ W, x0 ≤ t ∧ t ≤ x0 + T) :
    ‖pointMassFourierKernel W tau‖ ≤
      ∫ xi : ℝ,
        ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ *
          ‖pointMassFourierKernel W (tau-xi/T)‖ := by
  rw [pointMassFourierKernel_eq_scaled_convolution W hT hinterval]
  let psiHat : 𝓢(ℝ, ℂ) := 𝓕 (sourceBumpSchwartz 1 zero_lt_one)
  let g : ℝ → ℝ := fun xi => ‖psiHat xi‖ * (W.card : ℝ)
  have hg : Integrable g := by
    exact psiHat.integrable.norm.mul_const (W.card : ℝ)
  let f : ℝ → ℝ := fun xi =>
    ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ *
      ‖pointMassFourierKernel W (tau-xi/T)‖
  have hfmeas : AEStronglyMeasurable f := by
    apply Continuous.aestronglyMeasurable
    dsimp [f, pointMassFourierKernel]
    fun_prop
  have hfg : ∀ xi, f xi ≤ g xi := by
    intro xi
    have hkernel : ‖pointMassFourierKernel W (tau-xi/T)‖ ≤ (W.card:ℝ) := by
      unfold pointMassFourierKernel
      calc
        ‖∑ t ∈ W,
            Complex.exp (-((2 * Real.pi * t * (tau-xi/T) : ℝ) : ℂ) *
              Complex.I)‖ ≤
            ∑ _t ∈ W, (1:ℝ) := by
          apply norm_sum_le_of_le
          intro t ht
          rw [Complex.norm_exp]
          simp
        _ = (W.card:ℝ) := by simp
    exact mul_le_mul_of_nonneg_left hkernel (norm_nonneg _)
  have hfint : Integrable f :=
    hg.mono' hfmeas (Filter.Eventually.of_forall fun xi => by
      have hf0 : 0 ≤ f xi := by dsimp [f]; positivity
      simpa only [Real.norm_eq_abs, abs_of_nonneg hf0] using hfg xi)
  apply MeasureTheory.norm_integral_le_of_norm_le hfint
  filter_upwards with xi
  calc
    ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi *
        intervalTranslationPhase x0 T xi *
          pointMassFourierKernel W (tau-xi/T)‖ =
      ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ *
        ‖pointMassFourierKernel W (tau-xi/T)‖ := by
      rw [norm_mul, norm_mul, norm_intervalTranslationPhase]
      ring
    _ = f xi := rfl
    _ ≤ f xi := le_rfl

set_option maxHeartbeats 800000 in
/-- The nonnegative norm convolution is integrable, uniformly in its center.
This packages the finite-kernel bound needed for central/tail splitting. -/
theorem integrable_scaledConvolutionNorm
    (W : Finset ℝ) (T tau : ℝ) :
    Integrable (fun xi : ℝ =>
      ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ *
        ‖pointMassFourierKernel W (tau-xi/T)‖) := by
  let psiHat : 𝓢(ℝ, ℂ) := 𝓕 (sourceBumpSchwartz 1 zero_lt_one)
  let f : ℝ → ℝ := fun xi => ‖psiHat xi‖ *
    ‖pointMassFourierKernel W (tau-xi/T)‖
  let g : ℝ → ℝ := fun xi => ‖psiHat xi‖ * (W.card:ℝ)
  have hg : Integrable g := psiHat.integrable.norm.mul_const _
  have hfmeas : AEStronglyMeasurable f := by
    apply Continuous.aestronglyMeasurable
    dsimp [f, pointMassFourierKernel]
    fun_prop
  apply hg.mono' hfmeas
  filter_upwards with xi
  have hk : ‖pointMassFourierKernel W (tau-xi/T)‖ ≤ (W.card:ℝ) := by
    unfold pointMassFourierKernel
    calc
      ‖∑ t ∈ W, Complex.exp
          (-((2 * Real.pi * t * (tau-xi/T) : ℝ) : ℂ) * Complex.I)‖ ≤
          ∑ _t ∈ W, (1:ℝ) := by
        apply norm_sum_le_of_le
        intro t ht
        rw [Complex.norm_exp]
        simp
      _ = (W.card:ℝ) := by simp
  have hf0 : 0 ≤ f xi := by dsimp [f]; positivity
  change ‖f xi‖ ≤ g xi
  rw [Real.norm_eq_abs, abs_of_nonneg hf0]
  exact mul_le_mul_of_nonneg_left hk (norm_nonneg _)

set_option maxHeartbeats 800000 in
/-- Exact central/tail decomposition in Lemma 11.7.  The central term keeps
the translated kernel; the tail pays only `|W|` times the Schwartz Fourier
tail. -/
theorem norm_pointMassFourierKernel_le_central_add_tail
    (W : Finset ℝ) {x0 T tau A : ℝ} (hT : 0 < T)
    (hinterval : ∀ t ∈ W, x0 ≤ t ∧ t ≤ x0 + T) :
    ‖pointMassFourierKernel W tau‖ ≤
      (∫ xi in Set.Icc (-A) A,
        ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ *
          ‖pointMassFourierKernel W (tau-xi/T)‖) +
      (W.card:ℝ) *
        ∫ xi in (Set.Icc (-A) A)ᶜ,
          ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ := by
  let f : ℝ → ℝ := fun xi =>
    ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ *
      ‖pointMassFourierKernel W (tau-xi/T)‖
  have hf : Integrable f := integrable_scaledConvolutionNorm W T tau
  have hbase := norm_pointMassFourierKernel_le_scaled_convolution W
    (tau:=tau) hT hinterval
  have hsplit := MeasureTheory.integral_add_compl
    (s := Set.Icc (-A) A) measurableSet_Icc hf
  have htail :
      (∫ xi in (Set.Icc (-A) A)ᶜ, f xi) ≤
        (W.card:ℝ) * ∫ xi in (Set.Icc (-A) A)ᶜ,
          ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ := by
    calc
      (∫ xi in (Set.Icc (-A) A)ᶜ, f xi) ≤
          ∫ xi in (Set.Icc (-A) A)ᶜ,
            (W.card:ℝ) *
              ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ := by
        apply MeasureTheory.setIntegral_mono_on hf.integrableOn
          ((𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ,ℂ)).integrable.norm.const_mul _).integrableOn
          measurableSet_Icc.compl
        intro xi hxi
        have hk : ‖pointMassFourierKernel W (tau-xi/T)‖ ≤ (W.card:ℝ) := by
          unfold pointMassFourierKernel
          calc
            ‖∑ t ∈ W, Complex.exp
                (-((2*Real.pi*t*(tau-xi/T):ℝ):ℂ)*Complex.I)‖ ≤
                ∑ _t ∈ W, (1:ℝ) := by
              apply norm_sum_le_of_le
              intro t ht
              rw [Complex.norm_exp]
              simp
            _ = (W.card:ℝ) := by simp
        dsimp [f]
        nlinarith [norm_nonneg ((𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi)]
      _ = (W.card:ℝ) * ∫ xi in (Set.Icc (-A) A)ᶜ,
          ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ := by
        rw [MeasureTheory.integral_const_mul]
      _ ≤ (W.card:ℝ) * ∫ xi in (Set.Icc (-A) A)ᶜ,
          ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ := le_rfl
    all_goals exact le_rfl
  rw [← hsplit] at hbase
  dsimp [f] at hbase ⊢
  exact hbase.trans (add_le_add le_rfl htail)

/-- Exact affine substitution used to turn the central Fourier interval into
the `1/T` local window in Lemma 11.7. -/
theorem integral_Icc_tau_sub_div
    (F : ℝ → ℝ) {T tau A : ℝ} (hT : 0 < T) (hA : 0 ≤ A) :
    (∫ xi in Set.Icc (-A) A, F (tau-xi/T)) =
      T * ∫ v in Set.Icc (tau-A/T) (tau+A/T), F v := by
  have hbounds : -A ≤ A := by linarith
  have hwindow : tau-A/T ≤ tau+A/T := by
    have : 0 ≤ A/T := div_nonneg hA hT.le
    linarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hbounds]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hwindow]
  let c : ℝ := -1/T
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hscale := intervalIntegral.integral_comp_mul_left
    (fun y : ℝ => F (y+tau)) (a := -A) (b := A) hc
  have hshift := intervalIntegral.integral_comp_add_right F tau
    (a := c*(-A)) (b := c*A)
  have harg : (fun xi : ℝ => F (tau-xi/T)) =
      (fun xi : ℝ => F (c*xi+tau)) := by
    funext xi
    congr 1
    dsimp [c]
    field_simp [hT.ne']
    ring
  have hrewrite :
      (∫ xi in -A..A, F (tau-xi/T)) =
        c⁻¹ * ∫ y in c*(-A)..c*A, F (y+tau) := by
    rw [harg]
    simpa only [smul_eq_mul] using hscale
  rw [hrewrite, hshift]
  have hca : c*(-A)+tau = tau+A/T := by dsimp [c]; field_simp [hT.ne']; ring
  have hcb : c*A+tau = tau-A/T := by dsimp [c]; field_simp [hT.ne']; ring
  rw [hca, hcb, intervalIntegral.integral_symm]
  have hcinv : c⁻¹ = -T := by dsimp [c]; field_simp [hT.ne']
  rw [hcinv]
  ring

/-- The complement of the symmetric central interval is the exact Schwartz
tail used in the source proof of Lemma 11.7.  Keeping the intrinsic Fourier
moment explicit avoids hiding the dependence on the requested decay order. -/
theorem sourceBump_fourier_compl_Icc_le
    {A : ℝ} (k : ℕ) (hA : 0 < A) :
    (∫ xi in (Set.Icc (-A) A)ᶜ,
        ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ, ℂ)) xi‖) ≤
      (A ^ k)⁻¹ *
        ∫ xi : ℝ, |xi| ^ k *
          ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ, ℂ)) xi‖ := by
  apply le_trans ?_
    (FourierRealPartRemoval.fourier_tail_le_inv_pow_mul
      (sourceBumpSchwartz 1 zero_lt_one) A k hA)
  apply MeasureTheory.setIntegral_mono_set
  · exact
      (𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ, ℂ)).integrable.norm.integrableOn
  · filter_upwards with xi
    exact norm_nonneg _
  · filter_upwards with xi hxi
    change xi ∉ Set.Icc (-A) A at hxi
    simp only [Set.mem_Icc, not_and_or] at hxi
    dsimp [FourierRealPartRemoval.fourierTailSet]
    change A ≤ |xi|
    rcases hxi with hlo | hhi
    · have : xi < -A := lt_of_not_ge hlo
      rw [abs_of_neg (this.trans (neg_neg_of_pos hA))]
      linarith
    · have : A < xi := lt_of_not_ge hhi
      rw [abs_of_pos (hA.trans this)]
      exact this.le

set_option maxHeartbeats 800000 in
/-- Fully explicit local-constancy inequality behind Guth--Maynard Lemma
11.7.  The central interval has the genuine width `A/T`; the tail is an
arbitrary-order Schwartz remainder.  Choosing `A = T^o(1)` is precisely the
source convention hidden by `\precsim`. -/
theorem pointMassFourierKernel_localConstancy_explicit
    (W : Finset ℝ) {x0 T tau A : ℝ} (k : ℕ)
    (hT : 0 < T) (hA : 0 < A)
    (hinterval : ∀ t ∈ W, x0 ≤ t ∧ t ≤ x0 + T) :
    ‖pointMassFourierKernel W tau‖ ≤
      sourceBumpFourierConstant 1 zero_lt_one 0 * T *
        (∫ v in Set.Icc (tau-A/T) (tau+A/T),
          ‖pointMassFourierKernel W v‖) +
      (W.card : ℝ) * (A ^ k)⁻¹ *
        (∫ xi : ℝ, |xi| ^ k *
          ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ, ℂ)) xi‖) := by
  have hsplit := norm_pointMassFourierKernel_le_central_add_tail W
    (tau := tau) (A := A) hT hinterval
  have hfourier : ∀ xi : ℝ,
      ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ, ℂ)) xi‖ ≤
        sourceBumpFourierConstant 1 zero_lt_one 0 := by
    intro xi
    simpa using sourceBump_fourier_decay 1 zero_lt_one 0 xi
  have hcentral :
      (∫ xi in Set.Icc (-A) A,
        ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ *
          ‖pointMassFourierKernel W (tau-xi/T)‖) ≤
        sourceBumpFourierConstant 1 zero_lt_one 0 * T *
          (∫ v in Set.Icc (tau-A/T) (tau+A/T),
            ‖pointMassFourierKernel W v‖) := by
    have hcont : Continuous (fun xi : ℝ =>
        sourceBumpFourierConstant 1 zero_lt_one 0 *
          ‖pointMassFourierKernel W (tau-xi/T)‖) := by
      unfold pointMassFourierKernel
      fun_prop
    calc
      (∫ xi in Set.Icc (-A) A,
          ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ *
            ‖pointMassFourierKernel W (tau-xi/T)‖) ≤
        ∫ xi in Set.Icc (-A) A,
          sourceBumpFourierConstant 1 zero_lt_one 0 *
            ‖pointMassFourierKernel W (tau-xi/T)‖ := by
          apply MeasureTheory.setIntegral_mono_on
          · exact (integrable_scaledConvolutionNorm W T tau).integrableOn
          · exact hcont.continuousOn.integrableOn_compact isCompact_Icc
          · exact measurableSet_Icc
          · intro xi hxi
            exact mul_le_mul_of_nonneg_right (hfourier xi) (norm_nonneg _)
      _ = sourceBumpFourierConstant 1 zero_lt_one 0 *
          (∫ xi in Set.Icc (-A) A,
            ‖pointMassFourierKernel W (tau-xi/T)‖) := by
          rw [MeasureTheory.integral_const_mul]
      _ = sourceBumpFourierConstant 1 zero_lt_one 0 * T *
          (∫ v in Set.Icc (tau-A/T) (tau+A/T),
            ‖pointMassFourierKernel W v‖) := by
          rw [integral_Icc_tau_sub_div
            (fun v => ‖pointMassFourierKernel W v‖) hT hA.le]
          ring
  have htail := sourceBump_fourier_compl_Icc_le k hA
  calc
    ‖pointMassFourierKernel W tau‖ ≤
      (∫ xi in Set.Icc (-A) A,
        ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ *
          ‖pointMassFourierKernel W (tau-xi/T)‖) +
      (W.card : ℝ) *
        ∫ xi in (Set.Icc (-A) A)ᶜ,
          ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ := hsplit
    _ ≤ sourceBumpFourierConstant 1 zero_lt_one 0 * T *
        (∫ v in Set.Icc (tau-A/T) (tau+A/T),
          ‖pointMassFourierKernel W v‖) +
      (W.card : ℝ) * ((A ^ k)⁻¹ *
        ∫ xi : ℝ, |xi| ^ k *
          ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ, ℂ)) xi‖) := by
      exact add_le_add hcentral
        (mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _))
    _ = _ := by ring

/-- Source-facing Lemma 11.7 for the actual ratio kernel `R(v)`.  This is the
same certified local-constancy estimate centered at the exact logarithmic
frequency from equation (7.2), before the elementary compact-range transport
from log-frequency to the rational variable. -/
theorem ratioDirichletKernel_localConstancy_logFrequency
    (W : Finset ℝ) {x0 T A v : ℝ} (k : ℕ)
    (hT : 0 < T) (hA : 0 < A)
    (hinterval : ∀ t ∈ W, x0 ≤ t ∧ t ≤ x0 + T) :
    ‖ratioDirichletKernel W v‖ ≤
      sourceBumpFourierConstant 1 zero_lt_one 0 * T *
        (∫ u in Set.Icc
          (Real.log |v| / (-2 * Real.pi) - A/T)
          (Real.log |v| / (-2 * Real.pi) + A/T),
          ‖pointMassFourierKernel W u‖) +
      (W.card : ℝ) * (A ^ k)⁻¹ *
        (∫ xi : ℝ, |xi| ^ k *
          ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one) : 𝓢(ℝ, ℂ)) xi‖) := by
  rw [ratioDirichletKernel_eq_pointMassFourierKernel]
  exact pointMassFourierKernel_localConstancy_explicit W k hT hA hinterval

end
end GuthMaynardLemma117

#print axioms GuthMaynardLemma117.norm_intervalTranslationPhase
#print axioms GuthMaynardLemma117.pointMassFourierKernel_eq_scaled_convolution
#print axioms GuthMaynardLemma117.norm_pointMassFourierKernel_le_scaled_convolution
#print axioms GuthMaynardLemma117.integrable_scaledConvolutionNorm
#print axioms GuthMaynardLemma117.norm_pointMassFourierKernel_le_central_add_tail
#print axioms GuthMaynardLemma117.integral_Icc_tau_sub_div
#print axioms GuthMaynardLemma117.sourceBump_fourier_compl_Icc_le
#print axioms GuthMaynardLemma117.pointMassFourierKernel_localConstancy_explicit
#print axioms GuthMaynardLemma117.ratioDirichletKernel_localConstancy_logFrequency
