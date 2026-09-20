import GuthMaynardWholeFrequencyUniformInputs
import GuthMaynardJIterationBumpWeld

/-!
# Concrete source package for the first Poisson truncation

The corrected whole-frequency theorem asks for smoothness, three Fourier
envelopes, and one scalar tail budget.  The concrete source bump supplies the
envelopes; the tail constant is then chosen explicitly, so the budget is an
identity rather than an analytic premise.
-/

open scoped Real FourierTransform ContDiff

noncomputable section
namespace GuthMaynardJIteration

/-- The concrete unit bump and an explicit tail constant inhabit the complete
first-Poisson package used in regions I and II. -/
theorem exists_sourceBump_firstPoissonPackage
    {T Y M3 B : ℝ} (hT : 0 < T) (hY : 0 ≤ Y)
    (hM3 : 0 < M3) (hB : 0 < B) (q : ℕ) :
    ∃ K0 K Kpsi C : ℝ,
      0 ≤ K ∧ 0 ≤ Kpsi ∧ 0 ≤ C ∧
      HasCompactSupport (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) ∧
      ContDiff ℝ ∞ (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) ∧
      (∀ z, ‖FourierTransform.fourier
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) z‖ ≤ Kpsi) ∧
      (∀ z, ‖FourierTransform.fourier
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) z‖ ≤
          K0 / (1 + |z|) ^ 2) ∧
      (∀ z, ‖FourierTransform.fourier
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) z‖ ≤
          K / (1 + |z|) ^ (q + 2)) ∧
      M3 * K *
        ((1 + Y / (1 / M3)) ^ 2 * max 1 ((1 / M3) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ q := by
  obtain ⟨K0, K, Kpsi, hK, hKpsi, hdecay2, hdecay, hsup⟩ :=
    exists_sourceBump_fourier_package 1 zero_lt_one q
  let numerator : ℝ := M3 * K *
    ((1 + Y / (1 / M3)) ^ 2 * max 1 ((1 / M3) ^ 2) *
      integerQuadraticMass) * T ^ 100
  let C : ℝ := numerator / B ^ q
  have hmass : 0 ≤ integerQuadraticMass := by
    unfold integerQuadraticMass
    exact tsum_nonneg fun j => by
      unfold integerQuadraticEnvelope
      split_ifs <;> positivity
  have hnum : 0 ≤ numerator := by
    dsimp only [numerator]
    have hmax : 0 ≤ max 1 ((1 / M3) ^ 2) :=
      zero_le_one.trans (le_max_left _ _)
    positivity
  have hBpow : 0 < B ^ q := pow_pos hB q
  have hC : 0 ≤ C := div_nonneg hnum hBpow.le
  refine ⟨K0, K, Kpsi, C, hK, hKpsi, hC,
    sourceBump_complex_hasCompactSupport 1 zero_lt_one,
    sourceBump_complex_contDiff 1 zero_lt_one,
    hsup, hdecay2, hdecay, ?_⟩
  dsimp only [C]
  rw [div_mul_cancel₀ numerator hBpow.ne']

#print axioms GuthMaynardJIteration.exists_sourceBump_firstPoissonPackage

end GuthMaynardJIteration
