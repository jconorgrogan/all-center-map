import KhaleAppendixBFirstPartScaleCorrected

/-!
# Source-faithful pointwise statement of Khale Lemma 4.1

The remaining analytic assertion is stated here before any Appendix-B
specialization.  Its selected set, strip hypotheses, actual ordinate, right
boundary integral, and parity/principality correction are all visible.

Source: T. Khale, *An Explicit Vinogradov--Korobov Zero-Free Region for
Dirichlet L-functions*, Lemma 4.1, cached source lines 601--633.
-/

namespace MAPKhaleLemma41PointwiseSource

open MAPKhaleAppendixBSource
open MAPKhaleAppendixBFirstPartScaleCorrected

noncomputable section

/-- The exact right-boundary logarithmic integral in Lemma 4.1. -/
def lemma41LogIntegral {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma eta t : ℝ) : ℝ :=
  ∫ u : ℝ,
    Real.log ‖DirichletCharacter.LFunction chi
      (((sigma + eta : ℝ) : ℂ) +
        Complex.I * ((t + 2 * eta * u / Real.pi : ℝ) : ℂ))‖ /
      (Real.cosh u) ^ 2

/-- The real cotangent detector associated with one selected zero. -/
def lemma41CotKernel (sigma eta t : ℝ) (rho : ℂ) : ℝ :=
  ((Real.pi / (2 * eta) : ℝ) : ℂ) *
      Complex.cot
        ((((Real.pi : ℝ) : ℂ) *
          (((sigma : ℂ) + Complex.I * t) - rho)) /
            (((2 * eta : ℝ) : ℂ))) |>.re

/-- Exact finite-selected-set form of Khale Lemma 4.1.  The witness `e`
is the source correction `(1-a)(1-delta(chi))`, and its interval records the
only property used by Appendix B.  This proposition is the first remaining
analytic theorem; it is not an Appendix-B conclusion. -/
abbrev KhaleLemma41FiniteSelectedEstimate : Prop :=
  ∀ (A B : ℝ), 0 < A → 0 < B → FordHurwitzEquation12 A B →
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (sigma eta t : ℝ) (S : Finset ℂ),
      3 ≤ q →
      Real.exp 1938 ≤ t →
      Real.rpow (q : ℝ) (1 / 100000 : ℝ) ≤ t →
      0 < eta → eta < 10 →
      1 / 2 < sigma - eta →
      1 ≤ sigma →
      sigma ≤ 1 + eta -
        1.92 * Real.rpow (Real.log (t / 100)) (-2 / 3 : ℝ) →
      (∀ rho ∈ S,
        sigma - eta ≤ rho.re ∧ rho.re ≤ 1 ∧
          DirichletCharacter.LFunction chi rho = 0) →
      ∃ e : ℝ, 0 ≤ e ∧ e ≤ 1 ∧
        (-logDeriv (DirichletCharacter.LFunction chi)
          ((sigma : ℂ) + Complex.I * t)).re ≤
        -(∑ rho ∈ S, lemma41CotKernel sigma eta t rho) +
        (1 / (2 * eta)) * lemma41Envelope A B q sigma eta t -
        (1 / (4 * eta)) * lemma41LogIntegral chi sigma eta t +
        e * Real.exp (-1937)

/-- At a selected zero with the same ordinate, the complex cotangent kernel
is exactly the real detector used in Appendix B. -/
theorem lemma41CotKernel_aligned
    {sigma eta t beta : ℝ} (heta : eta ≠ 0) :
    lemma41CotKernel sigma eta t
        ((beta : ℂ) + (t : ℂ) * Complex.I) =
      (1 / eta) *
        ((Real.pi / 2) * Real.cot
          ((Real.pi / 2) * ((sigma - beta) / eta))) := by
  unfold lemma41CotKernel
  have hdiff :
      ((sigma : ℂ) + Complex.I * (t : ℂ)) -
          ((beta : ℂ) + (t : ℂ) * Complex.I) =
        ((sigma - beta : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hdiff]
  have harg :
      (((Real.pi : ℝ) : ℂ) * ((sigma - beta : ℝ) : ℂ)) /
          (((2 * eta : ℝ) : ℂ)) =
        ((((Real.pi / 2) * ((sigma - beta) / eta) : ℝ)) : ℂ) := by
    push_cast
    field_simp [heta]
  rw [harg, ← Complex.ofReal_cot]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  field_simp [heta]

/-- The generic right-boundary integral specializes exactly to the `j`th
Appendix-B integral. -/
theorem lemma41LogIntegral_power_eq_appendixB
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (j : ℕ) (sigma eta gamma : ℝ) :
    lemma41LogIntegral (chi ^ j) sigma eta ((j : ℝ) * gamma) =
      MAPKhaleAppendixBFirstPartAnalyticReduction.appendixBLogIntegral
        chi j sigma eta gamma := by
  rfl

end
end MAPKhaleLemma41PointwiseSource

#print axioms MAPKhaleLemma41PointwiseSource.lemma41CotKernel_aligned
#print axioms MAPKhaleLemma41PointwiseSource.lemma41LogIntegral_power_eq_appendixB
