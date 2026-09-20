import Mathlib.Analysis.MellinInversion
import GuthMaynardReflectionKernelVdC

/-!
# Mellin line and finite factorization in Guth--Maynard Lemma 6.2

This file certifies the exact Mellin-inversion normalization and the finite
sum factorization used immediately before the oscillatory kernel estimate in
Guth--Maynard, pp. 19--20.  Together with
`GuthMaynardReflectionKernelVdC`, it leaves no ambiguity about signs,
`2π` factors, or which part of the proof is still a truncation estimate.
-/

namespace GuthMaynardReflectionMellin

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- A continuous compactly supported cutoff is Mellin-convergent on the
source line `Re(s)=1`.  This discharges the easy half of the analytic
hypotheses in `mellin_inversion_line_one`; only vertical decay of the Mellin
transform remains. -/
theorem mellinConvergent_one_of_compactSupport
    {f : ℝ → ℂ} (hf : Continuous f) (hcompact : HasCompactSupport f) :
    MellinConvergent f (1 : ℂ) := by
  unfold MellinConvergent
  have hi : IntegrableOn f (Set.Ioi 0) :=
    (hf.integrable_of_hasCompactSupport hcompact).integrableOn
  apply hi.congr_fun
  intro x hx
  simp
  exact measurableSet_Ioi

/-- Quadratic vertical decay is enough for the exact vertical-integrability
hypothesis of Mellin inversion.  The source obtains much faster decay by
repeated integration by parts; this theorem isolates the weakest concrete
decay estimate still needed for Lemma 6.2. -/
theorem verticalIntegrable_mellin_of_quadratic_decay
    {f : ℝ → ℂ} {C : ℝ}
    (hcontinuous : Continuous (fun r : ℝ =>
      mellin f ((1 : ℂ) + r * Complex.I)))
    (hdecay : ∀ r : ℝ,
      ‖mellin f ((1 : ℂ) + r * Complex.I)‖ ≤ C * (1 + r ^ 2)⁻¹) :
    Complex.VerticalIntegrable (mellin f) 1 := by
  unfold Complex.VerticalIntegrable
  have hmajor : Integrable (fun r : ℝ => C * (1 + r ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  exact hmajor.mono' hcontinuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hdecay)

/-- Mathlib's Mellin inversion theorem written on the literal source line
`Re(s)=1`, with `s=1+ir`. -/
theorem mellin_inversion_line_one
    (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x)
    (hconv : MellinConvergent f (1 : ℂ))
    (hvertical : Complex.VerticalIntegrable (mellin f) 1)
    (hcontinuous : ContinuousAt f x) :
    f x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ,
          (x : ℂ) ^ (-((1 : ℂ) + r * Complex.I)) *
            mellin f ((1 : ℂ) + r * Complex.I) := by
  have h := mellinInv_mellin_eq 1 f hx hconv hvertical hcontinuous
  rw [mellinInv] at h
  simpa only [Complex.real_smul] using h.symm

/-- The collected positive-frequency sum factors exactly after the source
change of variables makes the kernel independent of `m`.  This is the finite
Fubini/algebra step preceding the triangle inequality in Lemma 6.2. -/
theorem finite_reflection_factorization
    (S : Finset ℕ) (H K : ℝ → ℂ) (N τ : ℝ) :
    (∑ m ∈ S,
        H τ * Complex.exp (-Complex.I * (τ * Real.log N)) *
          Complex.exp (-Complex.I * (τ * Real.log m)) * K τ) =
      H τ * Complex.exp (-Complex.I * (τ * Real.log N)) * K τ *
        ∑ m ∈ S, Complex.exp (-Complex.I * (τ * Real.log m)) := by
  calc
    (∑ m ∈ S,
        H τ * Complex.exp (-Complex.I * (τ * Real.log N)) *
          Complex.exp (-Complex.I * (τ * Real.log m)) * K τ) =
      ∑ m ∈ S,
        (H τ * Complex.exp (-Complex.I * (τ * Real.log N)) * K τ) *
          Complex.exp (-Complex.I * (τ * Real.log m)) := by
        apply Finset.sum_congr rfl
        intro m hm
        ring
    _ = H τ * Complex.exp (-Complex.I * (τ * Real.log N)) * K τ *
        ∑ m ∈ S, Complex.exp (-Complex.I * (τ * Real.log m)) := by
      rw [Finset.mul_sum]

/-- The exponent after Mellin inversion separates into the common `N` phase
and the Dirichlet-polynomial `m` phase. -/
theorem exp_log_mul_separates
    {m : ℕ} (hm : 0 < m) {N τ : ℝ} (hN : 0 < N) :
    Complex.exp (-Complex.I * (τ * Real.log (m * N))) =
      Complex.exp (-Complex.I * (τ * Real.log N)) *
        Complex.exp (-Complex.I * (τ * Real.log m)) := by
  rw [show Real.log (m * N) = Real.log N + Real.log m by
    rw [Real.log_mul (by positivity : (m : ℝ) ≠ 0) hN.ne']
    ring]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end

end GuthMaynardReflectionMellin

#print axioms GuthMaynardReflectionMellin.mellin_inversion_line_one
#print axioms GuthMaynardReflectionMellin.mellinConvergent_one_of_compactSupport
#print axioms GuthMaynardReflectionMellin.verticalIntegrable_mellin_of_quadratic_decay
#print axioms GuthMaynardReflectionMellin.finite_reflection_factorization
#print axioms GuthMaynardReflectionMellin.exp_log_mul_separates
