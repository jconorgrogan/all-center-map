import GuthMaynardJutilaReflection2941

/-!
# Polylog-robust form of equation (29.41)

The final density theorem does not depend on the printed exponent `3` in the
reflection loss.  This module exposes the exact recurrence for an arbitrary
fixed natural logarithmic power.  It is the stable consumer for a corrected
source proof which splits off the illegal `j=1` transference block and keeps
the actual coarse dyadic loss.
-/

namespace GuthMaynardJutilaReflection2941Robust

open GuthMaynardJutilaReflection2941
open GuthMaynardLengthComparison
open GuthMaynardJutilaLemma29NineKTwo

noncomputable section

def PrefixDyadicTransferenceFixedLogPower (K : ℕ) : Prop :=
  ∃ C M₀ : ℝ, 0 < C ∧ 2 ≤ M₀ ∧
    ∀ (M : ℝ) (G : Finset ℝ), M₀ ≤ M →
      jutilaReflectedPrefixMoment M G ≤
        C * (Real.log M) ^ K * jutilaSecondMoment M G

/-- Equation (29.41) with an arbitrary fixed log power.  This proof is only
the algebraic weld from the reflected-pair estimate and a corrected prefix
transference theorem; all analytic content remains visible in the two
hypotheses. -/
theorem jutila_reflection_recurrence_fixedLogPower_explicit
    (h295 : Lemma295ReflectedPairMoment)
    {K : ℕ} (hdyadic : PrefixDyadicTransferenceFixedLogPower K)
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
          C₁ * C₂ * (Real.log M) ^ K * jutilaSecondMoment M G +
          C₁ * Real.rpow T (-A) := by
  obtain ⟨C₁, T₁, hC₁, hT₁, hafe⟩ :=
    h295 delta epsilon A hdelta hepsilon hA
  obtain ⟨C₂, M₀, hC₂, hM₀, hprefix⟩ := hdyadic
  refine ⟨C₁, C₂, T₁, M₀, hC₁, hC₂, hT₁, hM₀, ?_⟩
  intro T N G hT hN hNupper hsep hheight
  dsimp only
  intro hM
  have hbase := hafe T N G hT hN hNupper hsep hheight
  have hpref := hprefix (reflectedLength29_40 T epsilon N) G hM
  calc
    jutilaSecondMoment N G ≤
        C₁ * ((G.card : ℝ) * N +
          jutilaReflectedPrefixMoment
            (reflectedLength29_40 T epsilon N) G) +
          C₁ * Real.rpow T (-A) := hbase
    _ ≤ C₁ * ((G.card : ℝ) * N +
          C₂ * (Real.log (reflectedLength29_40 T epsilon N)) ^ K *
            jutilaSecondMoment
              (reflectedLength29_40 T epsilon N) G) +
          C₁ * Real.rpow T (-A) := by
      gcongr
    _ = C₁ * (G.card : ℝ) * N +
          C₁ * C₂ *
            (Real.log (reflectedLength29_40 T epsilon N)) ^ K *
              jutilaSecondMoment
                (reflectedLength29_40 T epsilon N) G +
          C₁ * Real.rpow T (-A) := by ring

/-- The original exponent-three prefix theorem, if independently proved,
embeds into the robust interface at `K=3`. -/
theorem fixedLogPower_three_of_original
    (h : PrefixDyadicTransference29_41)
    (hprime : DyadicPrimeReciprocalLower29_32) :
    PrefixDyadicTransferenceFixedLogPower 3 := by
  simpa [PrefixDyadicTransferenceFixedLogPower] using h hprime

end

end GuthMaynardJutilaReflection2941Robust

#print axioms GuthMaynardJutilaReflection2941Robust.jutila_reflection_recurrence_fixedLogPower_explicit
#print axioms GuthMaynardJutilaReflection2941Robust.fixedLogPower_three_of_original
