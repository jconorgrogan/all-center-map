import GuthMaynardEnergy119Factored
import GuthMaynardEnergy119FactorThree
import GuthMaynardEnergy119LogAbsorption
import GuthMaynardEnergyGeometry

open scoped BigOperators
noncomputable section
namespace GuthMaynardEnergy119Actual
open CGLProofDAG GuthMaynardHeathBrownInterface GuthMaynardRatioKernelIdentity
open GuthMaynardS3LiteralLemma83Energy GuthMaynardEnergyGeometry
open GuthMaynardEnergy118GCD GuthMaynardEnergy119GCDCutoff
open GuthMaynardEnergy119Factored GuthMaynardEnergy119FactorThree

def cubicMomentShape (T : ℝ) (N : ℕ) (W : Finset ℝ) : ℝ :=
  (N : ℝ)*(W.card : ℝ)^3+
    (N : ℝ)*Real.rpow T (1/4 : ℝ)*Real.rpow (W.card : ℝ) (21/8 : ℝ)+
    (N : ℝ)^2*Real.sqrt (W.card : ℝ)*
      Real.sqrt (sourceApproximateAdditiveEnergy W : ℝ)

theorem cubicMomentShape_nonneg {T : ℝ} (hT : 0 ≤ T) (N : ℕ) (W : Finset ℝ) :
    0 ≤ cubicMomentShape T N W := by
  unfold cubicMomentShape
  exact add_nonneg (add_nonneg (by positivity)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hT _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))) (by positivity)

/-- Actual high-gcd cubic estimate, with all analytic moment inputs, floor
rounding, harmonic logarithms, and one-separated energy constants supplied. -/
theorem exists_actual_high_gcd_cubic_bound {eps : ℝ} (heps : 0 < eps) :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧
      ∀ (N : ℕ) (W : Finset ℝ) (T : ℝ),
        1 ≤ N → T0 ≤ T → Real.rpow T (3/4 : ℝ) ≤ N →
        OneSeparated W → ContainedInIntervalOfLength W T →
        (∑ p ∈ (dyadicPairs N).filter
          (fun p => (N : ℝ)^2/T < (p.1.gcd p.2 : ℝ)),
          ‖ratioDirichletKernel W ((p.1 : ℝ)/(p.2 : ℝ))‖^3) ≤
          C*Real.rpow T eps*cubicMomentShape T N W := by
  obtain ⟨Cf,Tf,hCf,hTf,hfact⟩ := high_gcd_factored_cubic (show 0 < eps/2 by positivity)
  obtain ⟨CL,hCL,hlog⟩ :=
    GuthMaynardEnergy119LogAbsorption.exists_log_absorption (eps/2) (by positivity)
  refine ⟨20*Cf*CL,max 2 Tf,by positivity,le_max_left _ _,?_⟩
  intro N W T hN hT hscale hsep hcontained
  have hTone : 1 ≤ T := by have := (le_max_left (2 : ℝ) Tf).trans hT; linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  have hshape : 0 ≤ cubicMomentShape T N W := cubicMomentShape_nonneg hTpos.le N W
  by_cases hNT : 2*T ≤ (N : ℝ)
  · rw [high_gcd_empty_of_two_time_le hN hTpos hNT]
    simp only [Finset.sum_empty]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hTpos.le _)) hshape
  have hNsmall : (N : ℝ) ≤ 2*T := le_of_not_ge hNT
  by_cases hW : W.Nonempty
  swap
  · have hW0 : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    simp [ratioDirichletKernel,cubicMomentShape]
  have hR : (1 : ℝ) ≤ (W.card : ℝ) := by
    exact_mod_cast (Finset.one_le_card.mpr hW)
  have hR1 : Real.rpow (W.card : ℝ) (1 : ℝ) = (W.card : ℝ) := Real.rpow_one _
  have hR2 : Real.rpow (W.card : ℝ) (2 : ℝ) = (W.card : ℝ)^2 := Real.rpow_natCast _ 2
  have hR3 : Real.rpow (W.card : ℝ) (3 : ℝ) = (W.card : ℝ)^3 := Real.rpow_natCast _ 3
  have hR4 : Real.rpow (W.card : ℝ) (4 : ℝ) = (W.card : ℝ)^4 := Real.rpow_natCast _ 4
  have hElo : Real.rpow (W.card : ℝ) (2 : ℝ) ≤
      (sourceApproximateAdditiveEnergy W : ℝ) := by
    rw [hR2]
    exact sourceApproximateAdditiveEnergy_ge_card_sq W
  have hEhi : (sourceApproximateAdditiveEnergy W : ℝ) ≤
      3*Real.rpow (W.card : ℝ) (3 : ℝ) := by
    rw [hR3]
    exact sourceApproximateAdditiveEnergy_le_three_card_cube W hsep
  have hs := lemma11_9_scalar_factor_bound_three hTone hscale hR hElo hEhi
  have hs' :
      Real.sqrt ((W.card : ℝ)*T+(W.card : ℝ)^2*(N : ℝ)+
        Real.rpow (W.card : ℝ) (5/4 : ℝ)*Real.rpow T (1/2 : ℝ)*(N : ℝ))*
      Real.sqrt ((N : ℝ)*(W.card : ℝ)^4+(sourceApproximateAdditiveEnergy W : ℝ)*T+
        Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ)*
          (W.card : ℝ)*Real.rpow T (1/2 : ℝ)*(N : ℝ)) ≤
        20*cubicMomentShape T N W := by
    have hSR : Real.rpow (W.card : ℝ) (1/2 : ℝ) = Real.sqrt (W.card : ℝ) :=
      (Real.sqrt_eq_rpow _).symm
    have hSE : Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (1/2 : ℝ) =
        Real.sqrt (sourceApproximateAdditiveEnergy W : ℝ) := (Real.sqrt_eq_rpow _).symm
    rw [hR1,hR2,hR3,hR4,hSR,hSE] at hs
    simpa only [cubicMomentShape] using hs
  have hl := hlog N T hTone hNsmall
  have hp : Real.rpow T (eps/2)*Real.rpow T (eps/2) = Real.rpow T eps := by
    calc
      _ = Real.rpow T ((eps/2)+(eps/2)) := (Real.rpow_add hTpos _ _).symm
      _ = _ := by congr 1; ring
  have hc : Cf*Real.rpow T (eps/2)*(1+Real.log (max 1 (2*(N : ℝ)))) ≤
      Cf*CL*Real.rpow T eps := by
    calc
      _ ≤ Cf*Real.rpow T (eps/2)*(CL*Real.rpow T (eps/2)) :=
        mul_le_mul_of_nonneg_left hl (mul_nonneg hCf.le (Real.rpow_nonneg hTpos.le _))
      _ = Cf*CL*(Real.rpow T (eps/2)*Real.rpow T (eps/2)) := by ring
      _ = _ := by rw [hp]
  have hf := hfact N W T hN ((le_max_right _ _).trans hT) hscale hsep hcontained
  have hmul := mul_le_mul hc hs' (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg (mul_nonneg hCf.le hCL.le) (Real.rpow_nonneg hTpos.le _))
  calc
    _ ≤ _ := hf
    _ ≤ (Cf*CL*Real.rpow T eps)*(20*cubicMomentShape T N W) := by
      simpa only [mul_assoc] using hmul
    _ = _ := by ring

end GuthMaynardEnergy119Actual
#print axioms GuthMaynardEnergy119Actual.exists_actual_high_gcd_cubic_bound
