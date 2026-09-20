import GuthMaynardJIterationBumpWeld

open scoped BigOperators FourierTransform ComplexConjugate SchwartzMap
open MeasureTheory
noncomputable section
namespace GuthMaynardEnergy114KernelEnvelope
open FourierTransform GuthMaynardJIteration

theorem sourceBump_fourier_local_quadratic_envelope :
    ∃ Cphi : ℝ, 0 < Cphi ∧
      ∀ (xi h : ℝ), |h| ≤ 1 →
        ‖(𝓕 (sourceBumpSchwartz 1 zero_lt_one)) xi‖ ≤
          Cphi / (1 + (xi + h)^2) := by
  let bhat : 𝓢(ℝ, ℂ) := 𝓕 (sourceBumpSchwartz 1 zero_lt_one)
  let S0 : ℝ := SchwartzMap.seminorm ℂ 0 0 bhat
  let S2 : ℝ := SchwartzMap.seminorm ℂ 2 0 bhat
  let Cphi : ℝ := 3 * (S0 + S2 + 1)
  refine ⟨Cphi, ?_, ?_⟩
  · dsimp [Cphi]
    positivity
  intro xi h hh
  have h0 : 0 ≤ S0 := by dsimp [S0]; positivity
  have h2 : 0 ≤ S2 := by dsimp [S2]; positivity
  have hs0 : ‖bhat xi‖ ≤ S0 := by
    dsimp [S0]
    simpa only [pow_zero, norm_iteratedFDeriv_zero, one_mul] using
      SchwartzMap.le_seminorm ℂ 0 0 bhat xi
  have hs2 : |xi|^2 * ‖bhat xi‖ ≤ S2 := by
    dsimp [S2]
    simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_zero] using
      SchwartzMap.le_seminorm ℂ 2 0 bhat xi
  have hweighted : (1 + xi^2) * ‖bhat xi‖ ≤ S0 + S2 := by
    have hs2' : xi^2 * ‖bhat xi‖ ≤ S2 := by simpa [sq_abs] using hs2
    nlinarith [sq_nonneg xi, norm_nonneg (bhat xi)]
  have hshift : 1 + (xi + h)^2 ≤ 3 * (1 + xi^2) := by
    have hh' := (abs_le.mp hh)
    nlinarith [sq_nonneg (xi - h), sq_nonneg (xi + h)]
  have hden : 0 < 1 + (xi + h)^2 := by positivity
  have hbase : 0 < 1 + xi^2 := by positivity
  have hfrac : (S0 + S2) / (1 + xi^2) ≤
      Cphi / (1 + (xi + h)^2) := by
    apply (div_le_div_iff₀ hbase hden).2
    dsimp [Cphi]
    nlinarith [hshift, hweighted]
  have hfour : ‖bhat xi‖ ≤ (S0 + S2) / (1 + xi^2) := by
    apply (le_div_iff₀ hbase).2
    nlinarith [hweighted]
  exact hfour.trans hfrac

theorem inv_one_add_sq_integrable :
    Integrable (fun s : ℝ => (1 : ℝ) / (1 + s^2)) := by
  simpa [one_div] using integrable_inv_one_add_sq

theorem inv_one_add_sq_nonneg (s : ℝ) : 0 ≤ (1 : ℝ) / (1 + s^2) := by positivity

end GuthMaynardEnergy114KernelEnvelope

#print axioms GuthMaynardEnergy114KernelEnvelope.sourceBump_fourier_local_quadratic_envelope
#print axioms GuthMaynardEnergy114KernelEnvelope.inv_one_add_sq_integrable
