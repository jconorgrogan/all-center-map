import MRTDynamicD12SmoothShell
import MRTDynamicD12ContinuumEnvelope
import MRTDynamicD12FactorExtraction

namespace MRTDynamicD12SmoothFactorMoment
open scoped BigOperators
open MRTDynamicD12SmoothShell MRTDynamicD12SmoothSampled
open MRTDynamicD12ContinuumSampling MRTDynamicD12MomentSource
open MRTDynamicD12FactorExtraction MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicSupportV3 MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MAPMRTProposition61TypeD1Factorization
noncomputable section

/-- Uniform fourth moment of each actual smooth source factor, including a
clipped or empty top shell. Constants precede all source parameters. -/
theorem dynamicD12SourceSmoothFactorMoment_proved :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 4 ≤ B ∧
    ∀ {X T K rho a b : ℝ} {q : ℕ} [NeZero q]
      (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X))) (f : NatDyadicFactor),
      3 ≤ X → DynamicD12MomentRange (8*X) T K q (hbFactorCutoff X) →
      IsSourceSmoothFactor X logIndex f → 2 ≤ f.length →
      0 < rho → rho ≤ T → 2*X ≤ rho^2 → a ≤ b → b-a+1 ≤ T →
      (∀ t ∈ Set.Icc a b, rho ≤ |t| ∧ |t| ≤ T) →
      (∑ chi : DirichletCharacter ℂ q, ∫ t in a..b,
        ‖dyadicFactorPolynomial (f.length : ℝ) (fun n ↦ chi n) f.coeff t‖^4) ≤
        C*((q : ℝ)*T)*(1+Real.log (8*X))^B := by
  obtain ⟨C,hC,B,hB,hsource⟩ := dynamicD12SmoothContinuumPowerBudget_proved
  refine ⟨C,hC,B,hB,?_⟩
  intro X T K rho a b q inst logIndex f hX hrange hf hflen hrho hrhoT hXrho hab hlen hann
  have hnonneg : 0 ≤ C*((q : ℝ)*T)*(1+Real.log (8*X))^B := by
    have hT : 0 ≤ T := by linarith [hrange.T_ge_two]
    have hlog : 0 ≤ Real.log (8*X) := Real.log_nonneg (by linarith)
    positivity
  have hpair (j : Fin (sourceDyadicCount (hbFactorCutoff X)))
      (hL : 2 ≤ 2^(j : ℕ)) :
      continuumMass (smoothIntervalPolynomial q (2^(j : ℕ))
        (min (2*2^(j : ℕ)) (hbFactorCutoff X))) a b ≤
          C*((q : ℝ)*T)*(1+Real.log (8*X))^B ∧
      continuumMass (smoothLogIntervalPolynomial q (2^(j : ℕ))
        (min (2*2^(j : ℕ)) (hbFactorCutoff X))) a b ≤
          C*((q : ℝ)*T)*(1+Real.log (8*X))^B := by
    let L := 2^(j : ℕ)
    let U := min (2*L) (hbFactorCutoff X)
    by_cases hLU : L < U
    · have hUcut : U ≤ hbFactorCutoff X := min_le_right _ _
      have hr : DynamicD12MomentRange (8*X) T K q U :=
        { hrange with
          cutoff_ge_two := by omega
          cutoff_le_X := (by exact_mod_cast hUcut : (U : ℝ) ≤ hbFactorCutoff X).trans
            hrange.cutoff_le_X }
      have hUrho : (U : ℝ) ≤ rho^2 := by
        have hcut : (hbFactorCutoff X : ℝ) ≤ 2*X :=
          Nat.floor_le (by linarith)
        exact ((by exact_mod_cast hUcut : (U : ℝ) ≤ hbFactorCutoff X).trans hcut).trans hXrho
      exact hsource hr hL hLU hab hlen hrho hrhoT hUrho hann
    · have hempty : Finset.Ioc L U = ∅ := Finset.Ioc_eq_empty (by omega)
      have hOne (chi : DirichletCharacter ℂ q) (t : ℝ) :
          smoothIntervalPolynomial q L U chi t = 0 := by
        simp [smoothIntervalPolynomial, hempty]
      have hLog (chi : DirichletCharacter ℂ q) (t : ℝ) :
          smoothLogIntervalPolynomial q L U chi t = 0 := by
        simp [smoothLogIntervalPolynomial, hempty]
      change continuumMass (smoothIntervalPolynomial q L U) a b ≤ _ ∧
        continuumMass (smoothLogIntervalPolynomial q L U) a b ≤ _
      simpa only [continuumMass, hOne, hLog, norm_zero, zero_pow (by omega : 4 ≠ 0),
        intervalIntegral.integral_zero, Finset.sum_const_zero] using And.intro hnonneg hnonneg
  rcases hf with rfl | ⟨j,rfl⟩
  · have hL : 2 ≤ 2^(logIndex : ℕ) := hflen
    have h := (hpair logIndex hL).2
    simpa only [continuumMass, dynamicLogFactor_polynomial_eq_clipped_interval] using h
  · have hL : 2 ≤ 2^(j : ℕ) := hflen
    have h := (hpair j hL).1
    simpa only [continuumMass, dynamicZetaFactor_polynomial_eq_clipped_interval] using h

end
end MRTDynamicD12SmoothFactorMoment
#print axioms MRTDynamicD12SmoothFactorMoment.dynamicD12SourceSmoothFactorMoment_proved
