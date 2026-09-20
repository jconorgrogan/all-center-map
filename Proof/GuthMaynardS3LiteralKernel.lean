import GuthMaynardSectorFactorization
import GuthMaynardRatioKernelIdentity
import GuthMaynardLemma62FarTail

/-!
# Literal integral kernel for the S3 affine reduction

This is equation (7.3), before the common radial variable is integrated out.
All three integer frequencies are retained. The ratio factors have the exact
orientations u1/u3, u2/u1, u3/u2 printed in the source.
-/

namespace GuthMaynardS3LiteralKernel

open MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap
open GuthMaynardS1Source GuthMaynardSectionThreeCutoff
open GuthMaynardSectionThreeCutoffDerivativeBudget
open GuthMaynardRatioKernelIdentity GuthMaynardEquation55Split

noncomputable section

def fourierIntegrand (t xi u : ℝ) : ℂ :=
  Complex.exp (((-2*Real.pi*u*xi : ℝ) : ℂ)*Complex.I) *
    sectionThreeOscillatory t u

theorem sourceHhat_eq_integral (t xi : ℝ) :
    sourceHhat t xi = ∫ u : ℝ, fourierIntegrand t xi u := by
  unfold sourceHhat
  rw [congrFun (SchwartzMap.fourier_coe (sectionThreeOscillatorySchwartz t)) xi]
  rw [Real.fourier_real_eq_integral_exp_smul]
  rfl

theorem integrable_fourierIntegrand (t xi : ℝ) :
    Integrable (fourierIntegrand t xi) := by
  have hc : Continuous (fourierIntegrand t xi) := by
    unfold fourierIntegrand
    apply Continuous.mul
    · fun_prop
    · exact (sectionThreeOscillatory_contDiff t).continuous
  apply (sectionThreeOscillatorySchwartz t).integrable.norm.mono' hc.aestronglyMeasurable
  filter_upwards with u
  have he : ‖Complex.exp (((-2*Real.pi*u*xi : ℝ) : ℂ)*Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  simp only [fourierIntegrand,norm_mul,he,one_mul,sectionThreeOscillatorySchwartz_apply]
  exact le_rfl

theorem integral_sum_three (W : Finset ℝ)
    (f : ℝ → ℝ → ℝ → ℝ → ℂ)
    (hf : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, Integrable (f a b c)) :
    (∫ u : ℝ, ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, f a b c u) =
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ∫ u : ℝ, f a b c u := by
  rw [integral_finsetSum W (fun a ha => integrable_finsetSum W
    (fun b hb => integrable_finsetSum W (fun c hc => hf a ha b hb c hc)))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_finsetSum W (fun b hb => integrable_finsetSum W
    (fun c hc => hf a ha b hb c hc))]
  apply Finset.sum_congr rfl
  intro b hb
  exact integral_finsetSum W (fun c hc => hf a ha b hb c hc)

/-- Exact unfolding of the three Fourier coefficients into iterated integrals. -/
theorem sourceIm_eq_iteratedIntegral_expanded (N : ℕ) (W : Finset ℝ)
    (m1 m2 m3 : ℤ) :
    sourceIm N W m1 m2 m3 = (N : ℂ)^3 *
      ∫ u1 : ℝ, ∫ u2 : ℝ, ∫ u3 : ℝ,
        ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
          fourierIntegrand (a-b) ((m1 : ℝ)*N) u1 *
          fourierIntegrand (b-c) ((m2 : ℝ)*N) u2 *
          fourierIntegrand (c-a) ((m3 : ℝ)*N) u3 := by
  unfold sourceIm
  congr 1
  symm
  have hinner (u1 u2 : ℝ) :
      (∫ u3 : ℝ, ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
        fourierIntegrand (a-b) ((m1 : ℝ)*N) u1 *
        fourierIntegrand (b-c) ((m2 : ℝ)*N) u2 *
        fourierIntegrand (c-a) ((m3 : ℝ)*N) u3) =
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
        fourierIntegrand (a-b) ((m1 : ℝ)*N) u1 *
        fourierIntegrand (b-c) ((m2 : ℝ)*N) u2 *
        sourceHhat (c-a) ((m3 : ℝ)*N) := by
    rw [integral_sum_three W _ (by
      intro a ha b hb c hc
      exact (integrable_fourierIntegrand _ _).const_mul _)]
    simp_rw [integral_const_mul, ← sourceHhat_eq_integral]
  simp_rw [hinner]
  have hmiddle (u1 : ℝ) :
      (∫ u2 : ℝ, ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
        fourierIntegrand (a-b) ((m1 : ℝ)*N) u1 *
        fourierIntegrand (b-c) ((m2 : ℝ)*N) u2 *
        sourceHhat (c-a) ((m3 : ℝ)*N)) =
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
        fourierIntegrand (a-b) ((m1 : ℝ)*N) u1 *
        sourceHhat (b-c) ((m2 : ℝ)*N) * sourceHhat (c-a) ((m3 : ℝ)*N) := by
    rw [integral_sum_three W _ (by
      intro a ha b hb c hc
      exact ((integrable_fourierIntegrand _ _).const_mul _).mul_const _)]
    simp_rw [integral_mul_const, integral_const_mul, ← sourceHhat_eq_integral]
  simp_rw [hmiddle]
  rw [integral_sum_three W _ (by
    intro a ha b hb c hc
    exact ((integrable_fourierIntegrand _ _).mul_const _).mul_const _)]
  simp_rw [integral_mul_const, ← sourceHhat_eq_integral]

/-- The exponent identity responsible for the source's ratio kernel. -/
theorem cpow_three_cycle
    (a b c : ℝ) {u1 u2 u3 : ℝ} (h1 : 0<u1) (h2 : 0<u2) (h3 : 0<u3) :
    (u1 : ℂ)^(Complex.I*((a-b : ℝ) : ℂ)) *
      (u2 : ℂ)^(Complex.I*((b-c : ℝ) : ℂ)) *
      (u3 : ℂ)^(Complex.I*((c-a : ℝ) : ℂ)) =
    Complex.exp (Complex.I*((a*Real.log |u1/u3| : ℝ) : ℂ)) *
      Complex.exp (Complex.I*((b*Real.log |u2/u1| : ℝ) : ℂ)) *
      Complex.exp (Complex.I*((c*Real.log |u3/u2| : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr h1.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr h2.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr h3.ne')]
  rw [← Complex.ofReal_log h1.le, ← Complex.ofReal_log h2.le, ← Complex.ofReal_log h3.le]
  rw [abs_of_pos (div_pos h1 h3),abs_of_pos (div_pos h2 h1),abs_of_pos (div_pos h3 h2)]
  rw [Real.log_div h1.ne' h3.ne',Real.log_div h2.ne' h1.ne',Real.log_div h3.ne' h2.ne']
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Pointwise finite ratio factorization with the literal cutoff and phase. -/
theorem integrand_sum_eq_ratio_kernel (N : ℕ) (W : Finset ℝ)
    (m1 m2 m3 : ℤ) (u1 u2 u3 : ℝ) :
    (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
      fourierIntegrand (a-b) ((m1 : ℝ)*N) u1 *
      fourierIntegrand (b-c) ((m2 : ℝ)*N) u2 *
      fourierIntegrand (c-a) ((m3 : ℝ)*N) u3) =
    Complex.exp (((-2*Real.pi*(N : ℝ)*
      ((m1 : ℝ)*u1+(m2 : ℝ)*u2+(m3 : ℝ)*u3) : ℝ) : ℂ)*Complex.I) *
      (sectionThreeCutoff u1*sectionThreeCutoff u2*sectionThreeCutoff u3) *
      (ratioDirichletKernel W (u1/u3)*ratioDirichletKernel W (u2/u1)*
        ratioDirichletKernel W (u3/u2)) := by
  by_cases h1 : 0<u1
  · by_cases h2 : 0<u2
    · by_cases h3 : 0<u3
      · have hproduct (f g h : ℝ → ℂ) (k : ℂ) :
            k*((∑ a ∈ W,f a)*(∑ b ∈ W,g b)*(∑ c ∈ W,h c)) =
              ∑ a ∈ W,∑ b ∈ W,∑ c ∈ W,k*(f a*g b*h c) := by
          rw [Finset.sum_mul_sum]
          simp_rw [Finset.sum_mul]
          simp_rw [Finset.mul_sum]
        unfold ratioDirichletKernel
        rw [hproduct]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        have hcycle := cpow_three_cycle a b c h1 h2 h3
        have hphase :
            Complex.exp (((-2*Real.pi*u1*((m1 : ℝ)*N) : ℝ) : ℂ)*Complex.I)*
            Complex.exp (((-2*Real.pi*u2*((m2 : ℝ)*N) : ℝ) : ℂ)*Complex.I)*
            Complex.exp (((-2*Real.pi*u3*((m3 : ℝ)*N) : ℝ) : ℂ)*Complex.I) =
          Complex.exp (((-2*Real.pi*(N : ℝ)*
            ((m1 : ℝ)*u1+(m2 : ℝ)*u2+(m3 : ℝ)*u3) : ℝ) : ℂ)*Complex.I) := by
          rw [← Complex.exp_add,← Complex.exp_add]
          congr 1
          push_cast
          ring
        unfold fourierIntegrand sectionThreeOscillatory
        calc
          _ = (Complex.exp (((-2*Real.pi*u1*((m1 : ℝ)*N) : ℝ) : ℂ)*Complex.I)*
              Complex.exp (((-2*Real.pi*u2*((m2 : ℝ)*N) : ℝ) : ℂ)*Complex.I)*
              Complex.exp (((-2*Real.pi*u3*((m3 : ℝ)*N) : ℝ) : ℂ)*Complex.I)) *
              (sectionThreeCutoff u1*sectionThreeCutoff u2*sectionThreeCutoff u3) *
              ((u1 : ℂ)^(Complex.I*((a-b : ℝ) : ℂ))*
                (u2 : ℂ)^(Complex.I*((b-c : ℝ) : ℂ))*
                (u3 : ℂ)^(Complex.I*((c-a : ℝ) : ℂ))) := by ring
          _ = _ := by rw [hcycle,hphase]
      · have hz := sectionThreeCutoff_supported u3 (by
          intro h; have := h.1; linarith)
        simp [fourierIntegrand,sectionThreeOscillatory,hz]
    · have hz := sectionThreeCutoff_supported u2 (by
        intro h; have := h.1; linarith)
      simp [fourierIntegrand,sectionThreeOscillatory,hz]
  · have hz := sectionThreeCutoff_supported u1 (by
      intro h; have := h.1; linarith)
    simp [fourierIntegrand,sectionThreeOscillatory,hz]

/-- Equation (7.3), with all three frequencies and the exact N³ normalization. -/
theorem sourceIm_eq_ratio_integral (N : ℕ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    sourceIm N W m1 m2 m3 = (N : ℂ)^3 *
      ∫ u1 : ℝ, ∫ u2 : ℝ, ∫ u3 : ℝ,
        Complex.exp (((-2*Real.pi*(N : ℝ)*
          ((m1 : ℝ)*u1+(m2 : ℝ)*u2+(m3 : ℝ)*u3) : ℝ) : ℂ)*Complex.I) *
          (sectionThreeCutoff u1*sectionThreeCutoff u2*sectionThreeCutoff u3) *
          (ratioDirichletKernel W (u1/u3)*ratioDirichletKernel W (u2/u1)*
            ratioDirichletKernel W (u3/u2)) := by
  rw [sourceIm_eq_iteratedIntegral_expanded]
  simp_rw [integrand_sum_eq_ratio_kernel]

end
end GuthMaynardS3LiteralKernel

#print axioms GuthMaynardS3LiteralKernel.sourceIm_eq_ratio_integral
