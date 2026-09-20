import KhaleAppendixBLFunctionEulerCertified
import KhaleCoshSqKernelIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Fubini step for the Khale Lemma-5.1 logarithmic L-integrals

The real part of the spectral point is fixed above one; its imaginary part is
an affine function of the integration variable.  Absolute convergence is
uniformly dominated by the already-certified zeta prime-power mass times the
integrable `cosh^{-2}` kernel.
-/

namespace MAPKhaleAppendixBLFunctionFubiniCertified

open MeasureTheory
open MAPKhaleAppendixBLemma51ExpansionReduction
open MAPKhaleAppendixBLFunctionEulerCertified

noncomputable section

/-- Affine vertical point used in the logarithmic L-integrals. -/
def affineSpectralPoint (x t a u : ℝ) : ℂ :=
  (x : ℂ) + Complex.I * (((t + a * u : ℝ) : ℂ))

/-- One prime-power summand after taking real parts and inserting the
`cosh^{-2}` weight. -/
def weightedLPrimePowerIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (x t a : ℝ)
    (k : PrimePowerIndex) (u : ℝ) : ℝ :=
  (appendixBLPrimePowerTerm chi (affineSpectralPoint x t a u) k).re /
    (Real.cosh u) ^ 2

private theorem affine_re (x t a u : ℝ) :
    (affineSpectralPoint x t a u).re = x := by
  simp [affineSpectralPoint]

private theorem weighted_integrand_norm_bound
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x t a : ℝ} (hx : 1 < x) (k : PrimePowerIndex) (u : ℝ) :
    ‖weightedLPrimePowerIntegrand chi x t a k u‖ ≤
      appendixBZetaPrimePowerTerm (x - 1) k *
        (1 / (Real.cosh u) ^ 2) := by
  have hs : 1 < (affineSpectralPoint x t a u).re := by simpa [affine_re] using hx
  have hterm := primePowerTerm_norm_le_zetaTerm chi hs k
  rw [affine_re] at hterm
  have hre : |(appendixBLPrimePowerTerm chi
      (affineSpectralPoint x t a u) k).re| ≤
      ‖appendixBLPrimePowerTerm chi (affineSpectralPoint x t a u) k‖ :=
    Complex.abs_re_le_norm _
  have hkernel : 0 ≤ 1 / (Real.cosh u) ^ 2 := by positivity
  unfold weightedLPrimePowerIntegrand
  rw [Real.norm_eq_abs, abs_div]
  simp only [abs_of_nonneg (sq_nonneg (Real.cosh u))]
  have hnum := hre.trans hterm
  exact (div_le_div_of_nonneg_right hnum (sq_nonneg _)).trans_eq (by ring)

private theorem weighted_integrand_continuous
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (x t a : ℝ) (k : PrimePowerIndex) :
    Continuous (weightedLPrimePowerIntegrand chi x t a k) := by
  have hs : Continuous (fun u : ℝ =>
      -(affineSpectralPoint x t a u)) := by
    unfold affineSpectralPoint
    fun_prop
  have hp : Continuous (fun u : ℝ =>
      (k.1 : ℂ) ^ (-(affineSpectralPoint x t a u))) :=
    hs.const_cpow (Or.inl (by exact_mod_cast k.1.property.ne_zero))
  have hz : Continuous (fun u : ℝ =>
      (appendixBLPrimePowerTerm chi (affineSpectralPoint x t a u) k)) := by
    unfold appendixBLPrimePowerTerm
    fun_prop
  have hre : Continuous (fun u : ℝ =>
      (appendixBLPrimePowerTerm chi (affineSpectralPoint x t a u) k).re) :=
    Complex.continuous_re.comp hz
  have hden : Continuous (fun u : ℝ => (Real.cosh u) ^ 2) :=
    Real.continuous_cosh.pow 2
  unfold weightedLPrimePowerIntegrand
  exact hre.div hden (fun u => pow_ne_zero 2 (Real.cosh_pos u).ne')

private theorem weighted_integrand_integrable
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x t a : ℝ} (hx : 1 < x) (k : PrimePowerIndex) :
    Integrable (weightedLPrimePowerIntegrand chi x t a k) := by
  let M : ℝ := appendixBZetaPrimePowerTerm (x - 1) k
  have hdom : Integrable (fun u : ℝ => M * (1 / (Real.cosh u) ^ 2)) :=
    MAPKhaleCoshSqKernelIntegrable.invCoshSq_integrable.const_mul M
  apply hdom.mono'
  · exact (weighted_integrand_continuous chi x t a k).aestronglyMeasurable
  · filter_upwards with u
    exact weighted_integrand_norm_bound chi hx k u

/-- Public integrability statement used by the finite four-coefficient weld in
Khale Lemma 5.1. -/
theorem weightedLPrimePowerIntegrand_integrable
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x t a : ℝ} (hx : 1 < x) (k : PrimePowerIndex) :
    Integrable (weightedLPrimePowerIntegrand chi x t a k) :=
  weighted_integrand_integrable chi hx k

private theorem summable_integral_norm
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x t a : ℝ} (hx : 1 < x) :
    Summable (fun k : PrimePowerIndex =>
      ∫ u : ℝ, ‖weightedLPrimePowerIntegrand chi x t a k u‖) := by
  have heta : 0 < x - 1 := by linarith
  have hz := MAPKhaleAppendixBZetaPrimePowerCertified.appendixBZetaPrimePowerIdentity
    (x - 1) heta
  let K : ℝ := ∫ u : ℝ, 1 / (Real.cosh u) ^ 2
  have hK0 : 0 ≤ K := integral_nonneg (fun u => by positivity)
  have hmajor : Summable (fun k : PrimePowerIndex =>
      appendixBZetaPrimePowerTerm (x - 1) k * K) := hz.1.mul_right K
  apply hmajor.of_nonneg_of_le
  · intro k
    exact integral_nonneg (fun u => norm_nonneg _)
  · intro k
    have hraw := weighted_integrand_integrable chi (t := t) (a := a) hx k
    have hdom : Integrable (fun u : ℝ =>
        appendixBZetaPrimePowerTerm (x - 1) k *
          (1 / (Real.cosh u) ^ 2)) :=
      MAPKhaleCoshSqKernelIntegrable.invCoshSq_integrable.const_mul _
    calc
      (∫ u : ℝ, ‖weightedLPrimePowerIntegrand chi x t a k u‖) ≤
          ∫ u : ℝ, appendixBZetaPrimePowerTerm (x - 1) k *
            (1 / (Real.cosh u) ^ 2) := by
        apply integral_mono hraw.norm hdom
        intro u
        exact weighted_integrand_norm_bound chi hx k u
      _ = appendixBZetaPrimePowerTerm (x - 1) k * K := by
        rw [integral_const_mul]

/-- Absolute summability of the integrated prime-power coefficients. -/
theorem integral_weightedLPrimePowerIntegrand_summable
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x t a : ℝ} (hx : 1 < x) :
    Summable (fun k : PrimePowerIndex =>
      ∫ u : ℝ, weightedLPrimePowerIntegrand chi x t a k u) := by
  exact (summable_integral_norm chi hx).of_norm_bounded
    (fun k => norm_integral_le_integral_norm _)

/-- Exact Fubini identity for an affine vertical L-function integral. -/
theorem logNorm_affine_integral_eq_tsum_integrals
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x t a : ℝ} (hx : 1 < x) :
    (∫ u : ℝ,
      Real.log ‖DirichletCharacter.LFunction chi
        (affineSpectralPoint x t a u)‖ / (Real.cosh u) ^ 2) =
      ∑' k : PrimePowerIndex,
        ∫ u : ℝ, weightedLPrimePowerIntegrand chi x t a k u := by
  have hpoint (u : ℝ) :
      Real.log ‖DirichletCharacter.LFunction chi
          (affineSpectralPoint x t a u)‖ / (Real.cosh u) ^ 2 =
        ∑' k : PrimePowerIndex,
          weightedLPrimePowerIntegrand chi x t a k u := by
    have hs : 1 < (affineSpectralPoint x t a u).re := by
      simpa [affine_re] using hx
    have hsum := appendixBLPrimePowerTerm_summable chi hs
    rw [log_norm_LFunction_eq_tsum_primePowers chi hs,
      Complex.re_tsum hsum]
    rw [← tsum_div_const]
    apply tsum_congr
    intro k
    rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  exact (integral_tsum_of_summable_integral_norm
    (fun k => weighted_integrand_integrable chi hx k)
    (summable_integral_norm chi hx)).symm

end
end MAPKhaleAppendixBLFunctionFubiniCertified

#print axioms MAPKhaleAppendixBLFunctionFubiniCertified.logNorm_affine_integral_eq_tsum_integrals
