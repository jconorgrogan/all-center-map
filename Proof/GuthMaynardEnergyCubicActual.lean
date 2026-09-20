import GuthMaynardEnergy118Actual
import GuthMaynardEnergy119Actual

open scoped BigOperators
noncomputable section
namespace GuthMaynardEnergyCubicActual
open CGLProofDAG GuthMaynardHeathBrownInterface GuthMaynardRatioKernelIdentity
open GuthMaynardS3LiteralLemma83Energy GuthMaynardEnergy118GCD
open GuthMaynardEnergy118Actual GuthMaynardEnergy119Actual

theorem cubicMomentShape_ge_tail {T : ℝ} (hT : 0 ≤ T) (N : ℕ) (W : Finset ℝ) :
    (N : ℝ)^2*Real.sqrt (W.card : ℝ)*Real.sqrt (sourceApproximateAdditiveEnergy W : ℝ) ≤
      cubicMomentShape T N W := by
  have hfirst : 0 ≤ (N : ℝ)*(W.card : ℝ)^3 := by positivity
  have hsecond : 0 ≤ (N : ℝ)*Real.rpow T (1/4 : ℝ)*Real.rpow (W.card : ℝ) (21/8 : ℝ) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hT _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  unfold cubicMomentShape
  linarith

/-- Actual complete cubic ratio moment: small and strict high gcd carriers
partition the original open-left dyadic rectangle exactly. -/
theorem exists_actual_cubic_moment_bound {eps : ℝ} (heps : 0 < eps) :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧
      ∀ (N : ℕ) (W : Finset ℝ) (T : ℝ),
        1 ≤ N → T0 ≤ T → Real.rpow T (3/4 : ℝ) ≤ N →
        OneSeparated W → ContainedInIntervalOfLength W T →
        (∑ n ∈ Finset.Ioc N (2*N), ∑ m ∈ Finset.Ioc N (2*N),
          ‖ratioDirichletKernel W ((n : ℝ)/(m : ℝ))‖^3) ≤
          C*Real.rpow T eps*cubicMomentShape T N W := by
  obtain ⟨Cs,hCs,Ts,hTs,hsmall⟩ := exists_actual_small_gcd_cubic_bound eps heps
  obtain ⟨Ch,Th,hCh,hTh,hhigh⟩ := exists_actual_high_gcd_cubic_bound heps
  refine ⟨Cs+Ch,max 2 (max Ts Th),by positivity,le_max_left _ _,?_⟩
  intro N W T hN hT hscale hsep hcontained
  have hTs' : Ts ≤ T := (le_max_left Ts Th).trans ((le_max_right _ _).trans hT)
  have hTh' : Th ≤ T := (le_max_right Ts Th).trans ((le_max_right _ _).trans hT)
  have hT0 : 0 ≤ T := by have := (le_max_left (2 : ℝ) (max Ts Th)).trans hT; linarith
  have hs := hsmall N W T hN hTs' hsep hcontained
  have hh := hhigh N W T hN hTh' hscale hsep hcontained
  have hs' :
      (∑ p ∈ (dyadicPairs N).filter (fun p => (p.1.gcd p.2 : ℝ) ≤ (N : ℝ)^2/T),
        ‖ratioDirichletKernel W ((p.1 : ℝ)/(p.2 : ℝ))‖^3) ≤
      Cs*Real.rpow T eps*cubicMomentShape T N W := by
    apply hs.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (cubicMomentShape_ge_tail hT0 N W)
      (mul_nonneg hCs.le (Real.rpow_nonneg hT0 _))
  have hsplit := Finset.sum_filter_add_sum_filter_not (dyadicPairs N)
    (fun p => (p.1.gcd p.2 : ℝ) ≤ (N : ℝ)^2/T)
    (fun p => ‖ratioDirichletKernel W ((p.1 : ℝ)/(p.2 : ℝ))‖^3)
  have htotal : (∑ p ∈ dyadicPairs N,
      ‖ratioDirichletKernel W ((p.1 : ℝ)/(p.2 : ℝ))‖^3) ≤
      (Cs+Ch)*Real.rpow T eps*cubicMomentShape T N W := by
    have hadd := add_le_add hs' hh
    simp only [not_le] at hsplit
    rw [hsplit] at hadd
    nlinarith [hadd]
  simpa only [dyadicPairs,Finset.product_eq_sprod,Finset.sum_product] using htotal

end GuthMaynardEnergyCubicActual
#print axioms GuthMaynardEnergyCubicActual.exists_actual_cubic_moment_bound
