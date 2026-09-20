import GuthMaynardRatioKernelIdentity
import GuthMaynardJIterationBumpWeld
import GuthMaynardJIterationPoisson
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Lemma 8.3: unsmoothed L4 moment by unit-collar additive energy

Source (1.7) defines `E(W)` as the number of ordered quadruples with
`|w1 + w2 - w3 - w4| ≤ 1`. The log-coordinate fourth moment of the
ratio kernel expands as a Fourier sum; the Schwartz decay of the
source plateau bump localizes that sum onto the unit collar, leaving
an explicit rapidly decaying cardinality tail. Smoothing stability
then transfers the bound to `smoothedRatio`.
-/

namespace GuthMaynardS3LiteralLemma83Energy

open MeasureTheory
open scoped BigOperators FourierTransform Real
open GuthMaynardJIteration GuthMaynardRatioKernelIdentity

noncomputable section

set_option maxHeartbeats 800000

/-- Source (1.7): approximate additive energy with the unit collar. -/
def sourceApproximateAdditiveEnergy (W : Finset ℝ) : ℕ :=
  (((W.product W) ×ˢ (W.product W)).filter fun pq =>
    |(pq.1.1 + pq.1.2) - (pq.2.1 + pq.2.2)| ≤ 1).card

def logDirichletKernel (W : Finset ℝ) (τ : ℝ) : ℂ :=
  ∑ t ∈ W, Complex.exp (Complex.I * ((t * τ : ℝ) : ℂ))

def additivePhase (pq : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  (pq.1.1 + pq.1.2) - (pq.2.1 + pq.2.2)

theorem sourceApproximateAdditiveEnergy_le_card_pow_four (W : Finset ℝ) :
    sourceApproximateAdditiveEnergy W ≤ W.card ^ 4 := by
  unfold sourceApproximateAdditiveEnergy
  have hcard : (((W.product W) ×ˢ (W.product W)).card) = W.card ^ 4 := by
    simp [Finset.card_product]
    ring
  exact (Finset.card_filter_le _ _).trans (by rw [hcard])

theorem ratioDirichletKernel_eq_logDirichletKernel (W : Finset ℝ) (v : ℝ) :
    ratioDirichletKernel W v = logDirichletKernel W (Real.log |v|) :=
  rfl

theorem logDirichletKernel_continuous (W : Finset ℝ) :
    Continuous (logDirichletKernel W) := by
  unfold logDirichletKernel
  exact continuous_finset_sum W fun t _ => by fun_prop

theorem exp_add_phase (a b τ : ℝ) :
    Complex.exp (Complex.I * ((a * τ : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((b * τ : ℝ) : ℂ)) =
    Complex.exp (Complex.I * (((a + b) * τ : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem star_exp_phase (t τ : ℝ) :
    star (Complex.exp (Complex.I * ((t * τ : ℝ) : ℂ))) =
      Complex.exp (Complex.I * (((-t) * τ : ℝ) : ℂ)) := by
  have h := (Complex.exp_conj (Complex.I * ((t * τ : ℝ) : ℂ))).symm
  simpa [Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal,
    mul_comm, mul_left_comm, mul_neg] using h

theorem logDirichletKernel_sq (W : Finset ℝ) (τ : ℝ) :
    logDirichletKernel W τ * logDirichletKernel W τ =
      ∑ t1 ∈ W, ∑ t2 ∈ W,
        Complex.exp (Complex.I * (((t1 + t2) * τ : ℝ) : ℂ)) := by
  unfold logDirichletKernel
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun t1 _ => Finset.sum_congr rfl fun t2 _ => ?_
  exact exp_add_phase t1 t2 τ

theorem star_logDirichletKernel (W : Finset ℝ) (τ : ℝ) :
    star (logDirichletKernel W τ) =
      ∑ t ∈ W, Complex.exp (Complex.I * (((-t) * τ : ℝ) : ℂ)) := by
  unfold logDirichletKernel
  rw [star_sum]
  refine Finset.sum_congr rfl fun t _ => star_exp_phase t τ

theorem star_logDirichletKernel_sq (W : Finset ℝ) (τ : ℝ) :
    star (logDirichletKernel W τ) * star (logDirichletKernel W τ) =
      ∑ t3 ∈ W, ∑ t4 ∈ W,
        Complex.exp (Complex.I * (((-(t3 + t4)) * τ : ℝ) : ℂ)) := by
  rw [star_logDirichletKernel, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun t3 _ => Finset.sum_congr rfl fun t4 _ => ?_
  have h := exp_add_phase (-t3) (-t4) τ
  simpa [neg_add, add_comm, add_left_comm, add_assoc] using h

theorem logDirichletKernel_norm_sq (W : Finset ℝ) (τ : ℝ) :
    (‖logDirichletKernel W τ‖ ^ 2 : ℂ) =
      logDirichletKernel W τ * star (logDirichletKernel W τ) := by
  calc
    (‖logDirichletKernel W τ‖ ^ 2 : ℂ) =
    (Complex.normSq (logDirichletKernel W τ) : ℂ) := by
      rw [Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    _ = logDirichletKernel W τ * star (logDirichletKernel W τ) := by
      rw [Complex.star_def]
      exact (Complex.mul_conj _).symm

theorem logDirichletKernel_norm_pow_four (W : Finset ℝ) (τ : ℝ) :
    (‖logDirichletKernel W τ‖ ^ 4 : ℂ) =
      ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ∑ t4 ∈ W,
        Complex.exp (Complex.I * (((t1 + t2 - t3 - t4) * τ : ℝ) : ℂ)) := by
  have hz : (‖logDirichletKernel W τ‖ ^ 4 : ℂ) =
      (star (logDirichletKernel W τ) * star (logDirichletKernel W τ)) *
        (logDirichletKernel W τ * logDirichletKernel W τ) := by
    have hsq := logDirichletKernel_norm_sq W τ
    have hpow : (‖logDirichletKernel W τ‖ ^ 4 : ℂ) =
        (‖logDirichletKernel W τ‖ ^ 2 : ℂ) *
          (‖logDirichletKernel W τ‖ ^ 2 : ℂ) := by
      push_cast
      ring
    rw [hpow, hsq]
    ring
  rw [hz, logDirichletKernel_sq, star_logDirichletKernel_sq]
  simp only [Finset.sum_mul, Finset.mul_sum]
  try simp only [Finset.sum_mul, Finset.mul_sum]
  try simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t1 ht1
  apply Finset.sum_congr rfl
  intro t2 ht2
  apply Finset.sum_congr rfl
  intro t3 ht3
  apply Finset.sum_congr rfl
  intro t4 ht4
  have h := exp_add_phase (t1 + t2) (-(t3 + t4)) τ
  calc
    Complex.exp (Complex.I * (((-(t3 + t4)) * τ : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (((t1 + t2) * τ : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (((t1 + t2) * τ : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (((-(t3 + t4)) * τ : ℝ) : ℂ)) := mul_comm _ _
    _ = Complex.exp (Complex.I * (((t1 + t2 - t3 - t4) * τ : ℝ) : ℂ)) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, neg_add] using h

theorem sum_four_eq_sum_quadruple (W : Finset ℝ)
    (g : ℝ → ℝ → ℝ → ℝ → ℂ) :
    (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ∑ t4 ∈ W, g t1 t2 t3 t4) =
      ∑ pq ∈ (W.product W) ×ˢ (W.product W),
        g pq.1.1 pq.1.2 pq.2.1 pq.2.2 := by
  calc
    (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ∑ t4 ∈ W,
        g t1 t2 t3 t4) =
      ∑ p ∈ W ×ˢ W, ∑ q ∈ W ×ˢ W,
        g p.1 p.2 q.1 q.2 := by
      calc
        (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ∑ t4 ∈ W,
            g t1 t2 t3 t4) =
          ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ r ∈ W ×ˢ W,
            g t1 t2 r.1 r.2 := by
          apply Finset.sum_congr rfl
          intro t1 ht1
          apply Finset.sum_congr rfl
          intro t2 ht2
          exact (Finset.sum_product' W W (fun t3 t4 : ℝ =>
            g t1 t2 t3 t4)).symm
        _ = ∑ p ∈ W ×ˢ W, ∑ q ∈ W ×ˢ W,
            g p.1 p.2 q.1 q.2 := by
          exact (Finset.sum_product' W W (fun p q : ℝ =>
            ∑ r ∈ W ×ˢ W, g p q r.1 r.2)).symm
    _ = ∑ pq ∈ (W.product W) ×ˢ (W.product W),
        g pq.1.1 pq.1.2 pq.2.1 pq.2.2 := by
      exact (Finset.sum_product' (W.product W) (W.product W)
        (fun p q : ℝ × ℝ => g p.1 p.2 q.1 q.2)).symm

theorem integral_sum_four (W : Finset ℝ)
    (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℂ)
    (hf : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ∀ d ∈ W, Integrable (f a b c d)) :
    (∫ τ : ℝ, ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ∑ d ∈ W, f a b c d τ) =
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ∑ d ∈ W, ∫ τ : ℝ, f a b c d τ := by
  rw [integral_finsetSum W (fun a ha => integrable_finsetSum W (fun b hb =>
    integrable_finsetSum W (fun c hc => integrable_finsetSum W (fun d hd =>
      hf a ha b hb c hc d hd))))]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [integral_finsetSum W (fun b hb => integrable_finsetSum W (fun c hc =>
    integrable_finsetSum W (fun d hd => hf a ha b hb c hc d hd)))]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [integral_finsetSum W (fun c hc => integrable_finsetSum W (fun d hd =>
    hf a ha b hb c hc d hd))]
  refine Finset.sum_congr rfl fun c hc => ?_
  exact integral_finsetSum W (fun d hd => hf a ha b hb c hc d hd)

theorem integrable_bump_mul_exp {R : ℝ} (hR : 0 < R) (Δ : ℝ) :
    Integrable fun τ : ℝ =>
      (sourceBump R hR τ : ℂ) *
        Complex.exp (Complex.I * ((Δ * τ : ℝ) : ℂ)) := by
  refine ((sourceBump_complex_contDiff R hR).continuous.mul ?_).integrable_of_hasCompactSupport
    (sourceBump_complex_hasCompactSupport R hR).mul_right
  fun_prop

theorem integrable_bump_mul_logDirichlet_four (W : Finset ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable fun τ : ℝ =>
      sourceBump R hR τ * ‖logDirichletKernel W τ‖ ^ 4 :=
  ((sourceBump_contDiff R hR).continuous.mul
    ((logDirichletKernel_continuous W).norm.pow 4)).integrable_of_hasCompactSupport
    (sourceBump_hasCompactSupport R hR).mul_right

theorem fourier_sourceBump_phase {R : ℝ} (hR : 0 < R) (Δ : ℝ) :
    FourierTransform.fourier (fun x : ℝ => (sourceBump R hR x : ℂ))
        (-Δ / (2 * Real.pi)) =
      ∫ τ : ℝ, (sourceBump R hR τ : ℂ) *
        Complex.exp (Complex.I * ((Δ * τ : ℝ) : ℂ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with τ
  have hπ : (2 * Real.pi : ℝ) ≠ 0 :=
    mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hphase : (-2 * Real.pi * τ * (-Δ / (2 * Real.pi)) : ℝ) = Δ * τ := by
    field_simp [hπ]
  rw [smul_eq_mul]
  have hexp :
      Complex.exp ((↑(-2 * Real.pi * τ * (-Δ / (2 * Real.pi))) : ℂ) * Complex.I) =
        Complex.exp (Complex.I * ((Δ * τ : ℝ) : ℂ)) := by
    congr 1
    rw [hphase]
    push_cast
    ring
  rw [hexp, mul_comm]

theorem sourceBump_eq_unit_dilation
    (R : ℝ) (hR : 0 < R) (x : ℝ) :
    sourceBump R hR x = sourceBump 1 zero_lt_one (x / R) := by
  have hratio : R⁻¹ * (R * 2) = (2 : ℝ) := by field_simp
  simp [sourceBump, ContDiffBump.apply, div_eq_mul_inv, mul_comm, hratio]

theorem fourier_sourceBump_eq_radius_mul_unit
    (R : ℝ) (hR : 0 < R) (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ => (sourceBump R hR x : ℂ)) xi =
      (R : ℂ) * FourierTransform.fourier
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) (R * xi) := by
  have hfun : (fun x : ℝ => (sourceBump R hR x : ℂ)) =
      (fun x : ℝ => (sourceBump 1 zero_lt_one (R⁻¹ * x) : ℂ)) := by
    funext x
    congr 1
    rw [sourceBump_eq_unit_dilation]
    congr 1
    field_simp
  rw [hfun, fourier_dilation
    (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
    (inv_ne_zero hR.ne') xi]
  simp [abs_of_pos hR, Complex.real_smul, mul_comm]

theorem abs_fourier_sourceBump_radius {R : ℝ} (hR : 0 < R) (q : ℕ) (ξ : ℝ) :
    ‖FourierTransform.fourier (fun x : ℝ => (sourceBump R hR x : ℂ)) ξ‖ ≤
      R * sourceBumpFourierConstant 1 zero_lt_one q / (1 + |R * ξ|) ^ q := by
  rw [fourier_sourceBump_eq_radius_mul_unit R hR ξ, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  simpa only [mul_div_assoc] using
    (mul_le_mul_of_nonneg_left
      (sourceBump_fourier_decay 1 zero_lt_one q (R * ξ)) hR.le)

theorem abs_fourier_sourceBump_collar {R : ℝ} (hR : 0 < R) (Δ : ℝ) :
    ‖FourierTransform.fourier (fun x : ℝ => (sourceBump R hR x : ℂ))
        (-Δ / (2 * Real.pi))‖ ≤
      R * sourceBumpFourierConstant 1 zero_lt_one 0 := by
  have h := abs_fourier_sourceBump_radius hR 0 (-Δ / (2 * Real.pi))
  simpa using h

theorem abs_fourier_sourceBump_tail {R : ℝ} (hR : 0 < R) (q : ℕ) {Δ : ℝ}
    (hΔ : 1 < |Δ|) :
    ‖FourierTransform.fourier (fun x : ℝ => (sourceBump R hR x : ℂ))
        (-Δ / (2 * Real.pi))‖ ≤
      R * sourceBumpFourierConstant 1 zero_lt_one q /
        (1 + R / (2 * Real.pi)) ^ q := by
  have hπ : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  have hξ : 1 / (2 * Real.pi) < |(-Δ / (2 * Real.pi))| := by
    rw [abs_div, abs_neg, abs_of_pos hπ]
    exact (div_lt_div_iff_of_pos_right hπ).2 hΔ
  have hRξ : R / (2 * Real.pi) < |R * (-Δ / (2 * Real.pi))| := by
    rw [abs_mul, abs_of_pos hR]
    have : R * (1 / (2 * Real.pi)) < R * |(-Δ / (2 * Real.pi))| :=
      mul_lt_mul_of_pos_left hξ hR
    simpa [div_eq_mul_inv] using this
  have hden : (1 + R / (2 * Real.pi)) ^ q ≤
      (1 + |R * (-Δ / (2 * Real.pi))|) ^ q :=
    pow_le_pow_left₀ (by positivity) (by linarith) q
  have hbound := abs_fourier_sourceBump_radius hR q (-Δ / (2 * Real.pi))
  have hC : 0 ≤ sourceBumpFourierConstant 1 zero_lt_one q :=
    sourceBumpFourierConstant_nonneg 1 zero_lt_one q
  have hnum : 0 ≤ R * sourceBumpFourierConstant 1 zero_lt_one q :=
    mul_nonneg hR.le hC
  have hdenpos : 0 < (1 + |R * (-Δ / (2 * Real.pi))|) ^ q := by positivity
  have hdiv := div_le_div_of_nonneg_left hnum (by positivity) hden
  exact hbound.trans hdiv

theorem integral_ofReal_bump_mul_four (W : Finset ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ τ : ℝ, (sourceBump R hR τ : ℂ) * (‖logDirichletKernel W τ‖ ^ 4 : ℂ)) =
      ((∫ τ : ℝ, sourceBump R hR τ * ‖logDirichletKernel W τ‖ ^ 4 : ℝ) : ℂ) := by
  have heq : (fun τ : ℝ => (sourceBump R hR τ : ℂ) *
        (‖logDirichletKernel W τ‖ ^ 4 : ℂ)) =
      fun τ : ℝ => ((sourceBump R hR τ * ‖logDirichletKernel W τ‖ ^ 4 : ℝ) : ℂ) := by
    funext τ
    push_cast
    rfl
  rw [heq]
  exact integral_ofReal

theorem integral_bump_logDirichlet_four_eq_fourier_sum
    (W : Finset ℝ) {R : ℝ} (hR : 0 < R) :
    ((∫ τ : ℝ, sourceBump R hR τ * ‖logDirichletKernel W τ‖ ^ 4 : ℝ) : ℂ) =
      ∑ pq ∈ (W.product W) ×ˢ (W.product W),
        FourierTransform.fourier (fun x : ℝ => (sourceBump R hR x : ℂ))
          (-additivePhase pq / (2 * Real.pi)) := by
  rw [← integral_ofReal_bump_mul_four W hR]
  have hpt : ∀ τ,
      (sourceBump R hR τ : ℂ) * (‖logDirichletKernel W τ‖ ^ 4 : ℂ) =
        ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ∑ t4 ∈ W,
          (sourceBump R hR τ : ℂ) *
            Complex.exp (Complex.I * (((t1 + t2 - t3 - t4) * τ : ℝ) : ℂ)) := by
    intro τ
    rw [logDirichletKernel_norm_pow_four, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t1 _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t2 _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t3 _ => ?_
    rw [Finset.mul_sum]
  simp_rw [hpt]
  have hf : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ∀ d ∈ W,
      Integrable fun τ : ℝ =>
        (sourceBump R hR τ : ℂ) *
          Complex.exp (Complex.I * (((a + b - c - d) * τ : ℝ) : ℂ)) :=
    fun a _ b _ c _ d _ => integrable_bump_mul_exp hR (a + b - c - d)
  rw [integral_sum_four W _ hf]
  rw [sum_four_eq_sum_quadruple W (fun t1 t2 t3 t4 =>
      ∫ τ : ℝ, (sourceBump R hR τ : ℂ) *
        Complex.exp (Complex.I * (((t1 + t2 - t3 - t4) * τ : ℝ) : ℂ)))]
  refine Finset.sum_congr rfl fun pq _ => ?_
  have hphase := (fourier_sourceBump_phase hR (additivePhase pq)).symm
  convert hphase using 1 <;>
    simp [additivePhase, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    <;> ring

/-- Weighted log-coordinate fourth moment, localized to the unit collar. -/
theorem integral_bump_logDirichlet_four_le_energy
    (W : Finset ℝ) {R : ℝ} (hR : 0 < R) (q : ℕ) :
    (∫ τ : ℝ, sourceBump R hR τ * ‖logDirichletKernel W τ‖ ^ 4) ≤
      R * sourceBumpFourierConstant 1 zero_lt_one 0 *
        (sourceApproximateAdditiveEnergy W : ℝ) +
      R * sourceBumpFourierConstant 1 zero_lt_one q /
        (1 + R / (2 * Real.pi)) ^ q * (W.card : ℝ) ^ 4 := by
  have hfInt := integrable_bump_mul_logDirichlet_four W hR
  have hnonneg : 0 ≤ ∫ τ : ℝ, sourceBump R hR τ * ‖logDirichletKernel W τ‖ ^ 4 :=
    integral_nonneg fun τ =>
      mul_nonneg (sourceBump_nonneg R hR τ) (by positivity)
  have hC := integral_bump_logDirichlet_four_eq_fourier_sum W hR
  have habs :
      ‖((∫ τ : ℝ, sourceBump R hR τ * ‖logDirichletKernel W τ‖ ^ 4 : ℝ) : ℂ)‖ ≤
        ∑ pq ∈ (W.product W) ×ˢ (W.product W),
          ‖FourierTransform.fourier (fun x : ℝ => (sourceBump R hR x : ℂ))
            (-additivePhase pq / (2 * Real.pi))‖ := by
    rw [hC]
    exact norm_sum_le _ _
  have hnorm :
      ‖((∫ τ : ℝ, sourceBump R hR τ * ‖logDirichletKernel W τ‖ ^ 4 : ℝ) : ℂ)‖ =
        ∫ τ : ℝ, sourceBump R hR τ * ‖logDirichletKernel W τ‖ ^ 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [← hnorm]
  let Q := (W.product W) ×ˢ (W.product W)
  let P : (ℝ × ℝ) × (ℝ × ℝ) → Prop := fun pq => |additivePhase pq| ≤ 1
  have hsplit :
      (∑ pq ∈ Q, ‖FourierTransform.fourier (fun x : ℝ => (sourceBump R hR x : ℂ))
          (-additivePhase pq / (2 * Real.pi))‖) =
        (∑ pq ∈ Q.filter P, ‖FourierTransform.fourier
            (fun x : ℝ => (sourceBump R hR x : ℂ))
            (-additivePhase pq / (2 * Real.pi))‖) +
        (∑ pq ∈ Q.filter (fun pq => ¬ P pq), ‖FourierTransform.fourier
            (fun x : ℝ => (sourceBump R hR x : ℂ))
            (-additivePhase pq / (2 * Real.pi))‖) :=
    (Finset.sum_filter_add_sum_filter_not Q P _).symm
  rw [hsplit] at habs
  have hC0 : 0 ≤ R * sourceBumpFourierConstant 1 zero_lt_one 0 :=
    mul_nonneg hR.le (sourceBumpFourierConstant_nonneg 1 zero_lt_one 0)
  have hCq : 0 ≤ R * sourceBumpFourierConstant 1 zero_lt_one q /
      (1 + R / (2 * Real.pi)) ^ q :=
    div_nonneg (mul_nonneg hR.le (sourceBumpFourierConstant_nonneg 1 zero_lt_one q))
      (by positivity)
  have hcollar :
      (∑ pq ∈ Q.filter P, ‖FourierTransform.fourier
          (fun x : ℝ => (sourceBump R hR x : ℂ))
          (-additivePhase pq / (2 * Real.pi))‖) ≤
        R * sourceBumpFourierConstant 1 zero_lt_one 0 *
          (sourceApproximateAdditiveEnergy W : ℝ) := by
    have hpt : ∀ pq ∈ Q.filter P,
        ‖FourierTransform.fourier (fun x : ℝ => (sourceBump R hR x : ℂ))
          (-additivePhase pq / (2 * Real.pi))‖ ≤
          R * sourceBumpFourierConstant 1 zero_lt_one 0 :=
      fun pq _ => abs_fourier_sourceBump_collar hR _
    have hsum := Finset.sum_le_sum hpt
    have hcard : ((Q.filter P).card : ℝ) = (sourceApproximateAdditiveEnergy W : ℝ) := by
      unfold sourceApproximateAdditiveEnergy Q P additivePhase
      rfl
    have hconst :
        (∑ pq ∈ Q.filter P, R * sourceBumpFourierConstant 1 zero_lt_one 0) =
          R * sourceBumpFourierConstant 1 zero_lt_one 0 *
            (sourceApproximateAdditiveEnergy W : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm, hcard]
    exact hsum.trans (by simpa [hconst])
  have htail :
      (∑ pq ∈ Q.filter (fun pq => ¬ P pq), ‖FourierTransform.fourier
          (fun x : ℝ => (sourceBump R hR x : ℂ))
          (-additivePhase pq / (2 * Real.pi))‖) ≤
        R * sourceBumpFourierConstant 1 zero_lt_one q /
          (1 + R / (2 * Real.pi)) ^ q * (W.card : ℝ) ^ 4 := by
    have hpt : ∀ pq ∈ Q.filter (fun pq => ¬ P pq),
        ‖FourierTransform.fourier (fun x : ℝ => (sourceBump R hR x : ℂ))
          (-additivePhase pq / (2 * Real.pi))‖ ≤
          R * sourceBumpFourierConstant 1 zero_lt_one q /
            (1 + R / (2 * Real.pi)) ^ q := by
      intro pq hpq
      have hmem := Finset.mem_filter.mp hpq
      have hΔ : 1 < |additivePhase pq| := lt_of_not_ge hmem.2
      exact abs_fourier_sourceBump_tail hR q hΔ
    have hsum := Finset.sum_le_sum hpt
    have hQcard : (Q.card : ℝ) = (W.card : ℝ) ^ 4 := by
      unfold Q
      simp [Finset.card_product]
      ring
    have hcardle : ((Q.filter (fun pq => ¬ P pq)).card : ℝ) ≤ (W.card : ℝ) ^ 4 := by
      have := Finset.card_filter_le Q (fun pq => ¬ P pq)
      have hQcardNat : Q.card = W.card ^ 4 := by
        unfold Q
        simp [Finset.card_product]
        ring
      exact_mod_cast this.trans (by rw [hQcardNat])
    have hconst :
        (∑ pq ∈ Q.filter (fun pq => ¬ P pq),
          R * sourceBumpFourierConstant 1 zero_lt_one q /
            (1 + R / (2 * Real.pi)) ^ q) =
          (R * sourceBumpFourierConstant 1 zero_lt_one q /
            (1 + R / (2 * Real.pi)) ^ q) *
            ((Q.filter (fun pq => ¬ P pq)).card : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hmul := mul_le_mul_of_nonneg_left hcardle hCq
    exact hsum.trans (by
      rw [hconst]
      exact hmul)
  exact habs.trans (add_le_add hcollar htail)

theorem log_sixteen_lt_four : Real.log 16 < 4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 16)]
  have htwo : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have hpow : (2 : ℝ) ^ 4 < Real.exp 1 ^ 4 :=
    pow_lt_pow_left₀ htwo (by norm_num) (by norm_num)
  have hexp : Real.exp 1 ^ 4 = Real.exp 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h16 : (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
  rw [h16]
  exact hpow.trans_eq hexp

theorem log_six_lt_four : Real.log 6 < 4 := by
  have h16 : Real.log 16 < 4 := log_sixteen_lt_four
  have hle : Real.log 6 ≤ Real.log 16 :=
    Real.log_le_log (by norm_num) (by norm_num)
  exact hle.trans_lt h16

theorem log_two_lt_four : Real.log 2 < 4 :=
  (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 6)).trans_lt
    log_six_lt_four

theorem mem_Icc_abs_le {a b x R : ℝ} (hx : x ∈ Set.Icc a b)
    (ha : |a| ≤ R) (hb : |b| ≤ R) : |x| ≤ R := by
  have hx' := Set.mem_Icc.mp hx
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem integral_Icc_le_weighted_four
    (W : Finset ℝ) {R a b : ℝ} (hR : 0 < R)
    (ha : |a| ≤ R) (hb : |b| ≤ R) :
    (∫ τ in Set.Icc a b, ‖logDirichletKernel W τ‖ ^ 4) ≤
      ∫ τ : ℝ, sourceBump R hR τ * ‖logDirichletKernel W τ‖ ^ 4 := by
  have hpt : ∀ τ ∈ Set.Icc a b,
      ‖logDirichletKernel W τ‖ ^ 4 =
        sourceBump R hR τ * ‖logDirichletKernel W τ‖ ^ 4 := by
    intro τ hτ
    have habs : |τ| ≤ R := mem_Icc_abs_le hτ ha hb
    rw [sourceBump_eq_one_of_abs_le R hR habs, one_mul]
  have hf0 : 0 ≤ᵐ[volume] fun τ : ℝ =>
      sourceBump R hR τ * ‖logDirichletKernel W τ‖ ^ 4 :=
    Filter.Eventually.of_forall fun τ =>
      mul_nonneg (sourceBump_nonneg R hR τ) (by positivity)
  rw [setIntegral_congr_fun measurableSet_Icc hpt]
  exact setIntegral_le_integral (integrable_bump_mul_logDirichlet_four W hR) hf0

end
end GuthMaynardS3LiteralLemma83Energy

#print axioms GuthMaynardS3LiteralLemma83Energy.sourceApproximateAdditiveEnergy_le_card_pow_four
#print axioms GuthMaynardS3LiteralLemma83Energy.logDirichletKernel_norm_pow_four
#print axioms GuthMaynardS3LiteralLemma83Energy.integral_bump_logDirichlet_four_le_energy
#print axioms GuthMaynardS3LiteralLemma83Energy.integral_Icc_le_weighted_four
