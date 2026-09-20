import GuthMaynardLemma296SmoothingReduction
import GuthMaynardJutilaReflection2941CertifiedRecurrence

/-!
# Exact remaining source surface for the Jutila reflection recurrence

The finite Lemma-29.6 smoothing reduction is now premise-free.  Hence the
only source theorem needed to construct the reflected pair estimate, and
therefore the corrected fixed-log-power recurrence, is the pointwise
approximate functional equation of Lemma 29.5 on pp. 261--263.
-/

namespace GuthMaynardLemma295ExactSourceSurface

open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295ReflectedPairConstruction
open GuthMaynardLemma296SmoothingReduction
open GuthMaynardJutilaReflection2941CertifiedRecurrence
open GuthMaynardLengthComparison

noncomputable section

/-- The exact reflected-pair estimate now consumes only the literal
pointwise Lemma-29.5 AFE. -/
theorem lemma295ReflectedPairMoment_of_exactAFE
    (hAFE : Lemma295ApproximateFunctionalEquationExactM) :
    Lemma295ReflectedPairMoment :=
  lemma295ReflectedPairMoment_of_AFE_and_smoothing hAFE
    lemma296SmoothedSecondMomentReduction_certified

/-- Source-corrected (29.41), with the honest fixed fifth log power, now
exposes Lemma 29.5 as its sole remaining premise. -/
theorem jutila_reflection_recurrence_fixedFive_of_exactAFE
    (hAFE : Lemma295ApproximateFunctionalEquationExactM)
    {delta epsilon A : ℝ}
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) (hA : 0 < A) :
    ∃ C₁ C₂ T₀ M₀ : ℝ,
      0 < C₁ ∧ 0 < C₂ ∧ 2 ≤ T₀ ∧ 2 ≤ M₀ ∧
      ∀ (T N : ℝ) (G : Finset ℝ),
        T₀ ≤ T → 1 ≤ N → N ≤ sourceReflectionNumerator29_40 T epsilon →
        TPowerSeparated G T delta → InOpenClosedZeroT G T →
        let M := reflectedLength29_40 T epsilon N
        M₀ ≤ M →
        jutilaSecondMoment N G ≤
          C₁ * (G.card : ℝ) * N +
          C₁ * C₂ * (Real.log M) ^ (5 : ℕ) *
            jutilaSecondMoment M G +
          C₁ * Real.rpow T (-A) := by
  exact jutila_reflection_recurrence_fixedFive_of_lemma295
    (lemma295ReflectedPairMoment_of_exactAFE hAFE)
    hdelta hepsilon hA

end


end GuthMaynardLemma295ExactSourceSurface

#print axioms GuthMaynardLemma295ExactSourceSurface.lemma295ReflectedPairMoment_of_exactAFE
#print axioms GuthMaynardLemma295ExactSourceSurface.jutila_reflection_recurrence_fixedFive_of_exactAFE
