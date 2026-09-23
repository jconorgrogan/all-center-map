import GuthMaynardJIterationDeterministic
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Changes of variables and second Poisson step in Guth--Maynard Lemma 9.2

This module formalizes the analytic identities in TeX lines 1534--1542 and
1591--1645 of `LargevaluesDirichlet17.tex`:

* Fourier dilation, with the absolute Jacobian required when `m₁ < 0`;
* the affine frequency substitution `xi = ell*m₁ + (m₁/M₃)*tau`;
* the scaled and modulated Poisson formula with its exact `T/M₂` factor;
* constant-one domination of a `C/T`-localized integral by the affine
  smoothing used in Lemma 9.2.

The source changes the affine denominator from `M₃` in TeX 1598 to `M₁`
in TeX 1606.  `source_frequency_affine_argument` proves that the stated
substitution gives `M₃`; no silent correction is made here.
-/

open scoped BigOperators Real FourierTransform SchwartzMap ContDiff
open MeasureTheory

noncomputable section

namespace GuthMaynardJIteration

def sourcePhase (x : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

/-- The exact constant bound behind the source's `|Z₁| \lesssim 1` when
the `tau` cutoff is `[-C,C]`. -/
theorem norm_sourcePhase_intervalIntegral_le
    {C : ℝ} (hC : 0 ≤ C) (y : ℝ) :
    ‖∫ tau in -C..C, sourcePhase (tau * y)‖ ≤ 2 * C := by
  have hbound : ‖∫ tau in -C..C, sourcePhase (tau * y)‖ ≤
      1 * |C - (-C)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro tau htau
    rw [sourcePhase, Complex.norm_exp]
    simp
  rw [abs_of_nonneg (by linarith)] at hbound
  linarith

theorem schwartz_poisson_at_zero (h : SchwartzMap ℝ ℂ) :
    ∑' n : ℤ, h n = ∑' n : ℤ, FourierTransform.fourier h n := by
  simpa using h.tsum_eq_tsum_fourier 0

theorem integral_affine_change (F : ℝ → ℂ) (a b : ℝ) :
    (∫ tau : ℝ, F (b + a * tau)) =
      |a⁻¹| • ∫ xi : ℝ, F xi := by
  calc
    (∫ tau : ℝ, F (b + a * tau)) =
        ∫ tau : ℝ, (fun x : ℝ => F (b + x)) (a * tau) := by rfl
    _ = |a⁻¹| • ∫ x : ℝ, F (b + x) :=
      Measure.integral_comp_mul_left (fun x : ℝ => F (b + x)) a
    _ = |a⁻¹| • ∫ xi : ℝ, F xi := by
      congr 1
      exact (measurePreserving_add_left volume b).integral_comp
        (Homeomorph.addLeft b).measurableEmbedding F

/-- Inverse form of `integral_affine_change`: an affine substitution has the
absolute Jacobian `|a|`.  The absolute value is essential when the source's
`m₁` is negative. -/
theorem integral_eq_abs_smul_affine (F : ℝ → ℂ) {a : ℝ}
    (ha : a ≠ 0) (b : ℝ) :
    (∫ xi : ℝ, F xi) = |a| • ∫ tau : ℝ, F (b + a * tau) := by
  calc
    (∫ xi : ℝ, F xi) =
        ∫ xi : ℝ, (fun tau : ℝ => F (b + a * tau))
          (-b / a + a⁻¹ * xi) := by
      apply integral_congr_ae
      filter_upwards with xi
      congr 1
      field_simp [ha]
      ring
    _ = |(a⁻¹)⁻¹| • ∫ tau : ℝ, F (b + a * tau) :=
      integral_affine_change (fun tau : ℝ => F (b + a * tau)) a⁻¹ (-b / a)
    _ = |a| • ∫ tau : ℝ, F (b + a * tau) := by rw [inv_inv]

/-- The exact affine frequency argument after TeX line 1595.  It gives `M₃`
in the denominator, documenting the later `M₁` in line 1606 as a distinct
expression rather than a consequence of this substitution. -/
theorem source_frequency_affine_argument
    {m1 M3 : ℝ} (hm1 : m1 ≠ 0) (hM3 : M3 ≠ 0)
    (ell m2 tau : ℝ) :
    (m2 / m1) * (ell * m1 + (m1 / M3) * tau) =
      ell * m2 + (m2 / M3) * tau := by
  field_simp [hm1, hM3]

/-- Fourier dilation with the correct absolute Jacobian. -/
theorem fourier_dilation (f : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0) (w : ℝ) :
    FourierTransform.fourier (fun v : ℝ => f (a * v)) w =
      |a⁻¹| • FourierTransform.fourier f (w / a) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  let g : ℝ → ℂ := fun t =>
    Complex.exp ((-2 * Real.pi * t * (w / a) : ℝ) * Complex.I) • f t
  have hpoint (v : ℝ) :
      Complex.exp ((-2 * Real.pi * v * w : ℝ) * Complex.I) • f (a * v) =
        g (a * v) := by
    dsimp only [g]
    congr 2
    push_cast
    field_simp [ha]
  calc
    (∫ v : ℝ, Complex.exp ((-2 * Real.pi * v * w : ℝ) * Complex.I) •
        f (a * v)) = ∫ v : ℝ, g (a * v) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = |a⁻¹| • ∫ t : ℝ, g t := Measure.integral_comp_mul_left g a

/-- Source specialization of the first dilation in Lemma 9.2.  The TeX writes
`m₂/m₁`; the literal Lebesgue identity has `|m₂/m₁|` when `m₁`
may be negative. -/
theorem source_fourier_dilation
    (f : ℝ → ℂ) {m1 m2 : ℝ} (hm1 : m1 ≠ 0) (hm2 : m2 ≠ 0)
    (xi : ℝ) :
    FourierTransform.fourier (fun u : ℝ => f (m1 * u / m2)) xi =
      |m2 / m1| • FourierTransform.fourier f ((m2 / m1) * xi) := by
  have hratio : m1 / m2 ≠ 0 := div_ne_zero hm1 hm2
  have hinv : (m1 / m2)⁻¹ = m2 / m1 := by
    field_simp [hm1, hm2]
  rw [← hinv]
  calc
    FourierTransform.fourier (fun u : ℝ => f (m1 * u / m2)) xi =
        FourierTransform.fourier (fun v : ℝ => f ((m1 / m2) * v)) xi := by
      apply congrArg (fun g : ℝ → ℂ => FourierTransform.fourier g xi)
      funext v
      congr 1
      ring
    _ = |(m1 / m2)⁻¹| •
        FourierTransform.fourier f (xi / (m1 / m2)) :=
      fourier_dilation f hratio xi
    _ = |(m1 / m2)⁻¹| •
        FourierTransform.fourier f ((m1 / m2)⁻¹ * xi) := by
      congr 3
      field_simp [hratio]

/-- The smoothing used in Lemma 9.2, with the source normalization `T` kept
outside the kernel. -/
def affineSmoothing (T : ℝ) (psi f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u : ℝ, T * psi (T * (x - u)) * f u

/-- Positive-kernel domination of a localized integral by the affine
smoothing from TeX 1637--1645.  There is no hidden loss: a kernel majorant by
`1` gives constant `1`. -/
theorem localized_integral_le_affineSmoothing
    (S : Set ℝ) (hS : MeasurableSet S) {T x : ℝ} (psi f : ℝ → ℝ)
    (hT : 0 ≤ T) (hf0 : ∀ u, 0 ≤ f u) (hpsi0 : ∀ z, 0 ≤ psi z)
    (hmajor : ∀ u ∈ S, 1 ≤ psi (T * (x - u)))
    (hlocal : IntegrableOn (fun u => T * f u) S)
    (hsmooth : Integrable (fun u => T * psi (T * (x - u)) * f u)) :
    (∫ u in S, T * f u) ≤ affineSmoothing T psi f x := by
  rw [← integral_indicator hS]
  unfold affineSmoothing
  apply integral_mono (hlocal.integrable_indicator hS) hsmooth
  intro u
  by_cases hu : u ∈ S
  · rw [Set.indicator_of_mem hu]
    have hkernel := hmajor u hu
    nlinarith [mul_nonneg hT (hf0 u),
      mul_nonneg (hpsi0 (T * (x - u))) (hf0 u)]
  · rw [Set.indicator_of_notMem hu]
    exact mul_nonneg (mul_nonneg hT (hpsi0 (T * (x - u)))) (hf0 u)

/-- Source-shaped specialization: a bump which is at least one on `|z| ≤ C`
dominates every `C / T` neighborhood after the `T`-scale smoothing. -/
theorem source_localized_integral_le_affineSmoothing
    {C T x : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hf0 : ∀ u, 0 ≤ f u) (hpsi0 : ∀ z, 0 ≤ psi z)
    (hpsi_major : ∀ z, |z| ≤ C → 1 ≤ psi z)
    (hlocal : IntegrableOn (fun u => T * f u) (Metric.closedBall x (C / T)))
    (hsmooth : Integrable (fun u => T * psi (T * (x - u)) * f u)) :
    (∫ u in Metric.closedBall x (C / T), T * f u) ≤
      affineSmoothing T psi f x := by
  apply localized_integral_le_affineSmoothing
    (Metric.closedBall x (C / T)) Metric.isClosed_closedBall.measurableSet
    psi f hT.le hf0 hpsi0
  · intro u hu
    apply hpsi_major
    have hudist : dist u x ≤ C / T := Metric.mem_closedBall.mp hu
    have huabs : |x - u| ≤ C / T := by
      simpa only [Real.dist_eq, abs_sub_comm] using hudist
    rw [abs_mul, abs_of_pos hT]
    calc
      T * |x - u| ≤ T * (C / T) := mul_le_mul_of_nonneg_left huabs hT.le
      _ = C := by field_simp [hT.ne']
  · exact hlocal
  · exact hsmooth

theorem fourier_scaled_modulated
    (psi : ℝ → ℂ) {A : ℝ} (hA : 0 < A) (y w : ℝ) :
    FourierTransform.fourier
        (fun v : ℝ => psi (A * v) * sourcePhase (y * v)) w =
      (A⁻¹ : ℝ) • FourierTransform.fourier psi ((w - y) / A) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  have hpoint (v : ℝ) :
      Complex.exp ((-(2 * Real.pi * v * w) : ℝ) * Complex.I) •
          (psi (A * v) * sourcePhase (y * v)) =
        (fun t : ℝ =>
          Complex.exp ((-2 * Real.pi * t * ((w - y) / A) : ℝ) * Complex.I) •
            psi t) (A * v) := by
    simp only [sourcePhase, smul_eq_mul]
    calc
      Complex.exp ((-(2 * Real.pi * v * w) : ℝ) * Complex.I) *
          (psi (A * v) * Complex.exp ((2 * Real.pi * (y * v) : ℝ) * Complex.I)) =
          (Complex.exp ((-(2 * Real.pi * v * w) : ℝ) * Complex.I) *
            Complex.exp ((2 * Real.pi * (y * v) : ℝ) * Complex.I)) *
              psi (A * v) := by ring
      _ = Complex.exp ((-2 * Real.pi * (A * v) * ((w - y) / A) : ℝ) *
            Complex.I) * psi (A * v) := by
        rw [← Complex.exp_add]
        congr 2
        push_cast
        field_simp [ne_of_gt hA]
        ring
  calc
    (∫ v : ℝ, Complex.exp ((-2 * Real.pi * v * w : ℝ) * Complex.I) •
        (psi (A * v) * sourcePhase (y * v))) =
        ∫ v : ℝ, (fun t : ℝ =>
          Complex.exp ((-2 * Real.pi * t * ((w - y) / A) : ℝ) * Complex.I) •
            psi t) (A * v) := by
      apply integral_congr_ae
      filter_upwards with v
      convert hpoint v using 1
      ring_nf
    _ = (A⁻¹ : ℝ) • ∫ t : ℝ,
        Complex.exp ((-2 * Real.pi * t * ((w - y) / A) : ℝ) * Complex.I) •
          psi t := by
      simpa only [abs_of_pos (inv_pos.mpr hA)] using
        (Measure.integral_comp_mul_left
          (g := fun t : ℝ =>
            Complex.exp ((-2 * Real.pi * t * ((w - y) / A) : ℝ) * Complex.I) •
              psi t) A)

theorem scaled_modulated_poisson
    (psi : ℝ → ℂ) (hpsi_compact : HasCompactSupport psi)
    (hpsi_smooth : ContDiff ℝ ∞ psi) {A : ℝ} (hA : 0 < A) (y : ℝ) :
    ∑' ell : ℤ, psi (A * ell) * sourcePhase (y * ell) =
      (A⁻¹ : ℝ) • ∑' j : ℤ,
        FourierTransform.fourier psi ((j - y) / A) := by
  have hscaled_compact : HasCompactSupport (fun x : ℝ => psi (A * x)) := by
    let Au : ℝˣ := Units.mk0 A hA.ne'
    simpa only [Function.comp_apply, Units.smul_def, Au, Units.val_mk0] using!
      hpsi_compact.comp_homeomorph (Homeomorph.smul Au)
  have hcompact : HasCompactSupport
      (fun x : ℝ => psi (A * x) * sourcePhase (y * x)) := by
    simpa only [Pi.mul_apply] using! hscaled_compact.mul_right
  have hsmooth : ContDiff ℝ ∞
      (fun x : ℝ => psi (A * x) * sourcePhase (y * x)) := by
    apply ContDiff.mul
    · fun_prop
    · unfold sourcePhase
      apply Complex.contDiff_exp.comp
      apply ContDiff.mul
      · simpa only [Complex.ofRealCLM_apply] using!
          Complex.ofRealCLM.contDiff.comp
            (show ContDiff ℝ ∞ (fun x : ℝ => 2 * Real.pi * (y * x)) by fun_prop)
      · exact contDiff_const
  let h : SchwartzMap ℝ ℂ := hcompact.toSchwartzMap hsmooth
  calc
    ∑' ell : ℤ, psi (A * ell) * sourcePhase (y * ell) =
        ∑' ell : ℤ, h ell := by rfl
    _ = ∑' j : ℤ, FourierTransform.fourier h j := schwartz_poisson_at_zero h
    _ = ∑' j : ℤ, (A⁻¹ : ℝ) •
        FourierTransform.fourier psi ((j - y) / A) := by
      apply tsum_congr
      intro j
      simpa [h, HasCompactSupport.toSchwartzMap] using!
        fourier_scaled_modulated psi hA y j
    _ = (A⁻¹ : ℝ) • ∑' j : ℤ,
        FourierTransform.fourier psi ((j - y) / A) := by
      rw [tsum_const_smul'']

/-- The second Poisson formula in the exact `M₂ / T` normalization of
Guth--Maynard TeX 1623--1625. -/
theorem second_poisson_source_scale
    (psi : ℝ → ℂ) (hpsi_compact : HasCompactSupport psi)
    (hpsi_smooth : ContDiff ℝ ∞ psi)
    {M2 T : ℝ} (hM2 : 0 < M2) (hT : 0 < T) (y : ℝ) :
    ∑' ell : ℤ, psi (M2 * ell / T) * sourcePhase (y * ell) =
      (T / M2 : ℝ) • ∑' j : ℤ,
        FourierTransform.fourier psi ((j - y) / (M2 / T)) := by
  have hscale : 0 < M2 / T := div_pos hM2 hT
  have hinv : (M2 / T)⁻¹ = T / M2 := by
    field_simp [hM2.ne', hT.ne']
  rw [← hinv]
  convert scaled_modulated_poisson psi hpsi_compact hpsi_smooth hscale y using 1
  apply tsum_congr
  intro ell
  congr 2
  ring

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.schwartz_poisson_at_zero
#print axioms GuthMaynardJIteration.norm_sourcePhase_intervalIntegral_le
#print axioms GuthMaynardJIteration.integral_affine_change
#print axioms GuthMaynardJIteration.integral_eq_abs_smul_affine
#print axioms GuthMaynardJIteration.source_frequency_affine_argument
#print axioms GuthMaynardJIteration.fourier_dilation
#print axioms GuthMaynardJIteration.source_fourier_dilation
#print axioms GuthMaynardJIteration.localized_integral_le_affineSmoothing
#print axioms GuthMaynardJIteration.source_localized_integral_le_affineSmoothing
#print axioms GuthMaynardJIteration.fourier_scaled_modulated
#print axioms GuthMaynardJIteration.scaled_modulated_poisson
#print axioms GuthMaynardJIteration.second_poisson_source_scale
