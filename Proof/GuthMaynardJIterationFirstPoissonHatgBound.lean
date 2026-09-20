import GuthMaynardJIterationFirstPoissonGhatLocalization
import GuthMaynardJIterationMediumRetained

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

def sourceFirstPoissonWindowIndicator
    (M3 B m1 xi : ℝ) (ell : ℤ) : ℝ :=
  if |xi - m1 * (ell : ℝ)| < (|m1| / M3) * B then 1 else 0

/-- The normalized cutoff used by the retained Poisson API is exactly the
source's `|ξ-m₁ℓ|` window. -/
theorem poissonRetainedIndicator_firstPoisson_eq
    {M3 m1 : ℝ} (hM3 : 0 < M3) (hm1 : m1 ≠ 0)
    (B xi : ℝ) (ell : ℤ) :
    poissonRetainedIndicator (1 / M3) B (xi / m1) ell =
      sourceFirstPoissonWindowIndicator M3 B m1 xi ell := by
  unfold poissonRetainedIndicator sourceFirstPoissonWindowIndicator
  rw [firstPoissonFrequency_eq hM3]
  have hiff := firstPoissonLocalization_iff hM3 hm1 B xi ell
  by_cases hlocal : |M3 * ((ell : ℝ) - xi / m1)| < B
  · rw [if_pos hlocal, if_pos (hiff.mp hlocal)]
  · rw [if_neg hlocal, if_neg (fun hsource => hlocal (hiff.mpr hsource))]

/-- Norm of the retained first-Poisson series as the literal source window
mass.  `Kpsi` is the named uniform Fourier-bump seminorm. -/
theorem norm_sourceFirstPoissonRetained_le_window
    (F : ℝ → ℂ) {Kpsi M3 B m1 : ℝ}
    (hM3 : 0 < M3) (hB : 0 ≤ B) (hm1 : m1 ≠ 0)
    (hF : ∀ z, ‖F z‖ ≤ Kpsi) (xi : ℝ) :
    ‖sourceFirstPoissonRetained F M3 B m1 xi‖ ≤
      M3 * Kpsi *
        ∑' ell : ℤ, sourceFirstPoissonWindowIndicator M3 B m1 xi ell := by
  unfold sourceFirstPoissonRetained
  have h := norm_sourceSecondPoissonRetained_le_indicator F
    (M2 := 1) (T := M3) (B := B)
    (show 0 < (1 : ℝ) by norm_num) hM3 hB hF (xi / m1)
  have h' :
      ‖sourceSecondPoissonRetained F 1 M3 B (xi / m1)‖ ≤
        M3 * Kpsi *
          ∑' ell : ℤ, poissonRetainedIndicator (1 / M3) B (xi / m1) ell := by
    simpa only [div_one] using h
  calc
    ‖sourceSecondPoissonRetained F 1 M3 B (xi / m1)‖ ≤
        M3 * Kpsi *
          ∑' ell : ℤ, poissonRetainedIndicator (1 / M3) B (xi / m1) ell := h'
    _ = M3 * Kpsi *
        ∑' ell : ℤ, sourceFirstPoissonWindowIndicator M3 B m1 xi ell := by
      congr 1
      apply tsum_congr
      intro ell
      exact poissonRetainedIndicator_firstPoisson_eq hM3 hm1 B xi ell

/-- Triangle bound for the retained finite `m₁` expression, preserving the
exact localized integer window and corrected Fourier inner. -/
theorem norm_sourceFirstPoissonRetainedFinite_le_window
    (m1Range m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    {Kpsi M3 B : ℝ} (hM3 : 0 < M3) (hB : 0 ≤ B)
    (hF : ∀ z, ‖F z‖ ≤ Kpsi)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0) (xi : ℝ) :
    ‖sourceFirstPoissonRetainedFinite m1Range m2Range F fhat M3 B xi‖ ≤
      ∑ m1 ∈ m1Range,
        (M3 * Kpsi *
          ∑' ell : ℤ,
            sourceFirstPoissonWindowIndicator M3 B (m1 : ℝ) xi ell) *
          ‖sourceCorrectedM2FourierInner m2Range fhat m1 xi‖ := by
  unfold sourceFirstPoissonRetainedFinite sourceFirstPoissonRetainedContribution
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro m1 hm1mem
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_sourceFirstPoissonRetained_le_window F hM3 hB
      (by exact_mod_cast hm1 m1 hm1mem) hF xi)
    (norm_nonneg _)

/-- Fully explicit finite version of (9.7).  The first term is the source
localized `ℓ` sum with exact radius `(|m₁|/M₃)B`; the second is the certified
Schwartz tail.  The corrected `|m₂/m₁|` stays inside every Fourier inner. -/
theorem norm_fourier_sourceGFinite_le_localized_add_time_neg100
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 f : ℝ → ℂ) (hf : Integrable f) (q : ℕ)
    (hcompact : HasCompactSupport psi1) (hsmooth : ContDiff ℝ ∞ psi1)
    {K0 K Kpsi M3 B Y C T : ℝ}
    (hK : 0 ≤ K) (hM3 : 0 < M3) (hB : 0 < B) (hY : 0 ≤ Y)
    (hT : 0 < T)
    (hbounded : ∀ z, ‖FourierTransform.fourier psi1 z‖ ≤ Kpsi)
    (hdecay2 : ∀ z,
      ‖FourierTransform.fourier psi1 z‖ ≤ K0 / (1 + |z|) ^ 2)
    (hdecay : ∀ z,
      ‖FourierTransform.fourier psi1 z‖ ≤ K / (1 + |z|) ^ (q + 2))
    (hbudget :
      M3 * K *
        ((1 + Y / (1 / M3)) ^ 2 * max 1 ((1 / M3) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ q)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0)
    (hsupport : ∀ m3 : ℤ,
      m3 ∉ m3Range → psi1 ((m3 : ℝ) / M3) = 0)
    (xi : ℝ) (hxi : ∀ m1 ∈ m1Range, |xi / (m1 : ℝ)| ≤ Y) :
    ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ≤
      (∑ m1 ∈ m1Range,
        (M3 * Kpsi *
          ∑' ell : ℤ,
            sourceFirstPoissonWindowIndicator M3 B (m1 : ℝ) xi ell) *
          ‖sourceCorrectedM2FourierInner m2Range
            (FourierTransform.fourier f) m1 xi‖) +
        (C / T ^ 100) *
          ∑ m1 ∈ m1Range,
            ‖sourceCorrectedM2FourierInner m2Range
              (FourierTransform.fourier f) m1 xi‖ := by
  let retained := sourceFirstPoissonRetainedFinite m1Range m2Range
    (FourierTransform.fourier psi1) (FourierTransform.fourier f) M3 B xi
  have htriangle :
      ‖FourierTransform.fourier
          (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi‖ ≤
        ‖retained‖ +
          ‖FourierTransform.fourier
              (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi -
            retained‖ := by
    calc
      _ = ‖retained +
          (FourierTransform.fourier
              (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi -
            retained)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  refine htriangle.trans (add_le_add ?_ ?_)
  · exact norm_sourceFirstPoissonRetainedFinite_le_window m1Range m2Range
      (FourierTransform.fourier psi1) (FourierTransform.fourier f)
      hM3 hB.le hbounded hm1 xi
  · exact norm_fourier_sourceGFinite_sub_retained_le_time_neg100
      m1Range m2Range m3Range psi1 f hf q hcompact hsmooth hK hM3 hB hY
      hT hdecay2 hdecay hbudget hm1 hm2 hsupport xi hxi

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.poissonRetainedIndicator_firstPoisson_eq
#print axioms GuthMaynardJIteration.norm_sourceFirstPoissonRetained_le_window
#print axioms GuthMaynardJIteration.norm_sourceFirstPoissonRetainedFinite_le_window
#print axioms GuthMaynardJIteration.norm_fourier_sourceGFinite_le_localized_add_time_neg100
