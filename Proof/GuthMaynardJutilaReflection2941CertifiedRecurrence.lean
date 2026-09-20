import GuthMaynardJutilaReflection2941Corrected

/-!
# Corrected source-derived recurrence for equation (29.41)

This is the narrow public endpoint after repairing the illegal first dyadic
block and retaining every displayed Cauchy/block logarithm.  The logarithmic
power is the certified fixed value five.  The prime-reciprocal input is
already discharged.  Consequently the only remaining source theorem in this
recurrence is the exact reflected pair estimate derived from Lemma 29.5.
-/

namespace GuthMaynardJutilaReflection2941CertifiedRecurrence

open GuthMaynardJutilaReflection2941
open GuthMaynardJutilaReflection2941Robust
open GuthMaynardJutilaReflection2941Corrected
open GuthMaynardLengthComparison

noncomputable section

/-- Source-corrected equation (29.41), with fixed log power five and no
prime-distribution premise. -/
theorem jutila_reflection_recurrence_fixedFive_of_lemma295
    (h295 : Lemma295ReflectedPairMoment)
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
  exact jutila_reflection_recurrence_fixedLogPower_explicit
    h295 prefixDyadicTransferenceFixedLogPower_five_certified
    hdelta hepsilon hA

end

end GuthMaynardJutilaReflection2941CertifiedRecurrence

#print axioms GuthMaynardJutilaReflection2941CertifiedRecurrence.jutila_reflection_recurrence_fixedFive_of_lemma295
