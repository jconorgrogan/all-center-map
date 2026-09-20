import MRTMediumEq79ParallelCore

/-!
# MRT (79): the exact transform seam

The medium projection is reduced here, without estimates, to the single-scale
Fourier/change-of-variables identity printed immediately before (79).  The
single-scale identity is named as a proposition and deliberately left
uninhabited: it is the first remaining source statement, not an assumption
silently installed into Proposition 5.1.
-/

namespace MAPMRTMediumEq79Parallel

open MeasureTheory
open MAPMRTProposition51HardBranch MAPMRTProposition51Source

noncomputable section

/-- The left side of the source's transform calculation at a single positive
scale `T`. -/
def oneScaleProjectedCriticalSum
    (N : ℕ) (X T : ℝ) (cutoff : ℝ → ℝ)
    (f : ℕ → ℂ) (G : ℝ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    f n * (Real.sqrt n : ℂ)⁻¹ *
      rescaledProjection (cutoffFourierKernel cutoff) T G
        (Real.log n - Real.log X)

/-- The right side after opening `φ̂`, then changing `t=Ty` and
`w=log n-log X-2πv/T`.  Every coefficient and phase is literal. -/
def oneScaleEquation79Integral
    (N : ℕ) (X T : ℝ) (cutoff : ℝ → ℝ)
    (f : ℕ → ℂ) (G : ℝ → ℂ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ, ∫ w : ℝ,
      finiteCriticalPolynomial N f t * G w * xMellinPhase X t *
        Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)) *
          (cutoff (t / T) : ℂ)

/-- The exact single-scale identity used twice by MRT to obtain (79).

This is the earliest open source statement in the current Lean chain.  Its
proof is a two-dimensional affine substitution plus Fubini for the compact
smooth cutoff.  Keeping it as a named, uninhabited proposition makes that
obligation auditable and prevents downstream results from treating it as an
axiom. -/
def MRTOneScaleEquation79Transform
    (N : ℕ) (X T : ℝ) (cutoff : ℝ → ℝ)
    (f : ℕ → ℂ) (G : ℝ → ℂ) : Prop :=
  oneScaleProjectedCriticalSum N X T cutoff f G =
    oneScaleEquation79Integral N X T cutoff f G

/-- Opening the definition of the medium projection is an exact subtraction
of the two one-scale projected sums. -/
theorem mediumProjectedCriticalSum_eq_sub_oneScale
    (N : ℕ) (X beta eta : ℝ) (cutoff : ℝ → ℝ)
    (f : ℕ → ℂ) (G : ℝ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N,
      f n * (Real.sqrt n : ℂ)⁻¹ *
        mediumFrequencyProjection X beta eta cutoff G
          (Real.log n - Real.log X)) =
      oneScaleProjectedCriticalSum N X (|beta| * X / eta) cutoff f G -
        oneScaleProjectedCriticalSum N X (10 * eta * |beta| * X)
          cutoff f G := by
  unfold oneScaleProjectedCriticalSum mediumFrequencyProjection
    mediumOrLowProjection lowFrequencyProjection
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

private def oneScaleIntegrand
    (N : ℕ) (X T : ℝ) (cutoff : ℝ → ℝ)
    (f : ℕ → ℂ) (G : ℝ → ℂ) (t w : ℝ) : ℂ :=
  finiteCriticalPolynomial N f t * G w * xMellinPhase X t *
    Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I)) *
      (cutoff (t / T) : ℂ)

/-- Subtracting the two transformed one-scale integrals gives precisely the
displayed `F̃` normalization in (79).  The two hypotheses are only the
Bochner-integrability conditions required by `integral_sub`; they contain no
estimate. -/
theorem sub_oneScaleEquation79Integral_eq_equation79Integral
    {N : ℕ} {X beta eta : ℝ} {cutoff : ℝ → ℝ}
    {f : ℕ → ℂ} {G : ℝ → ℂ}
    (heta : eta ≠ 0)
    (hhi : Integrable (Function.uncurry
      (oneScaleIntegrand N X (|beta| * X / eta) cutoff f G))
        (volume.prod volume))
    (hlo : Integrable (Function.uncurry
      (oneScaleIntegrand N X (10 * eta * |beta| * X) cutoff f G))
        (volume.prod volume)) :
    oneScaleEquation79Integral N X (|beta| * X / eta) cutoff f G -
        oneScaleEquation79Integral N X (10 * eta * |beta| * X) cutoff f G =
      equation79Integral N X beta eta cutoff f G := by
  have hhi' : Integrable (fun t : ℝ ↦ ∫ w : ℝ,
      oneScaleIntegrand N X (|beta| * X / eta) cutoff f G t w) :=
    hhi.integral_prod_left
  have hlo' : Integrable (fun t : ℝ ↦ ∫ w : ℝ,
      oneScaleIntegrand N X (10 * eta * |beta| * X) cutoff f G t w) :=
    hlo.integral_prod_left
  unfold oneScaleEquation79Integral
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ, ∫ w : ℝ,
            oneScaleIntegrand N X (|beta| * X / eta) cutoff f G t w) -
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ, ∫ w : ℝ,
            oneScaleIntegrand N X (10 * eta * |beta| * X) cutoff f G t w) = _
  rw [← mul_sub, ← integral_sub hhi' hlo']
  unfold equation79Integral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hhi.prod_right_ae, hlo.prod_right_ae] with t hhit hlot
  change Integrable
    (fun w : ℝ ↦ oneScaleIntegrand N X (|beta| * X / eta) cutoff f G t w) at hhit
  change Integrable
    (fun w : ℝ ↦ oneScaleIntegrand N X (10 * eta * |beta| * X) cutoff f G t w) at hlot
  rw [← integral_sub hhit hlot, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with w
  unfold oneScaleIntegrand sourceTildePolynomial mediumCutoffMultiplier
    xMellinPhase
  have hscale : t / (|beta| * X / eta) = eta * t / (|beta| * X) := by
    field_simp [heta]
  rw [hscale]
  push_cast
  ring

/-- Conditional bookkeeping theorem, included only to show that the isolated
single-scale transform is exactly sufficient for (79).  It is not used to
inhabit Proposition 5.1 unless both explicit transform proofs are supplied. -/
theorem mediumProjectedCriticalSum_eq_equation79Integral
    {N : ℕ} {X beta eta : ℝ} {cutoff : ℝ → ℝ}
    {f : ℕ → ℂ} {G : ℝ → ℂ}
    (heta : eta ≠ 0)
    (hhiId : MRTOneScaleEquation79Transform N X (|beta| * X / eta)
      cutoff f G)
    (hloId : MRTOneScaleEquation79Transform N X
      (10 * eta * |beta| * X) cutoff f G)
    (hhi : Integrable (Function.uncurry
      (oneScaleIntegrand N X (|beta| * X / eta) cutoff f G))
        (volume.prod volume))
    (hlo : Integrable (Function.uncurry
      (oneScaleIntegrand N X (10 * eta * |beta| * X) cutoff f G))
        (volume.prod volume)) :
    (∑ n ∈ Finset.Icc 1 N,
      f n * (Real.sqrt n : ℂ)⁻¹ *
        mediumFrequencyProjection X beta eta cutoff G
          (Real.log n - Real.log X)) =
      equation79Integral N X beta eta cutoff f G := by
  rw [mediumProjectedCriticalSum_eq_sub_oneScale]
  rw [hhiId, hloId]
  exact sub_oneScaleEquation79Integral_eq_equation79Integral heta hhi hlo

end
end MAPMRTMediumEq79Parallel

#print axioms MAPMRTMediumEq79Parallel.mediumProjectedCriticalSum_eq_sub_oneScale
#print axioms MAPMRTMediumEq79Parallel.sub_oneScaleEquation79Integral_eq_equation79Integral
#print axioms MAPMRTMediumEq79Parallel.mediumProjectedCriticalSum_eq_equation79Integral
