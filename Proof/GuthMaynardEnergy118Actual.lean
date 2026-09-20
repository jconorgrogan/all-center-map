import GuthMaynardEnergy118SmallGCDSubpower
import GuthMaynardEnergy118GCDCutoff

open scoped BigOperators
noncomputable section
namespace GuthMaynardEnergy118Actual
open CGLProofDAG GuthMaynardHeathBrownInterface
open GuthMaynardRatioKernelIdentity GuthMaynardS3LiteralLemma83Energy
open GuthMaynardEnergy118GCD GuthMaynardEnergy118SmallGCDSubpower

/-- Literal small-gcd cubic estimate: the original open-left dyadic rectangle
and real cutoff gcd(m,n) ≤ N²/T are retained. No analytic estimate is an input.
The constant and threshold precede the scale, point set, and time. -/
theorem exists_actual_small_gcd_cubic_bound :
    ∀ eps : ℝ, 0 < eps →
      ∃ C : ℝ, 0 < C ∧ ∃ T0 : ℝ, 1 ≤ T0 ∧
        ∀ (N : ℕ) (W : Finset ℝ) (T : ℝ),
          1 ≤ N → T0 ≤ T → OneSeparated W →
          ContainedInIntervalOfLength W T →
          (∑ p ∈ (dyadicPairs N).filter
            (fun p => (p.1.gcd p.2 : ℝ) ≤ (N : ℝ)^2/T),
            ‖ratioDirichletKernel W ((p.1 : ℝ)/(p.2 : ℝ))‖^3) ≤
            C*Real.rpow T eps*(N : ℝ)^2*Real.sqrt (W.card : ℝ)*
              Real.sqrt (sourceApproximateAdditiveEnergy W : ℝ) := by
  intro eps heps
  let eta : ℝ := min eps (1/2)
  have heta : 0 < eta := lt_min heps (by norm_num)
  have hetahi : eta < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hetaeps : eta ≤ eps := min_le_left _ _
  obtain ⟨C,hC,T0,hT0,hbound⟩ := exists_small_gcd_subpower_bound eta heta hetahi
  refine ⟨C,hC,T0,hT0,?_⟩
  intro N W T hN hT hsep hcontained
  have hTone : 1 ≤ T := hT0.trans hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  have hquot : 0 ≤ (N : ℝ)^2/T := by positivity
  let D : ℕ := Nat.floor ((N : ℝ)^2/T)
  have hDT : (D : ℝ)*T ≤ (N : ℝ)^2 := by
    exact (le_div_iff₀ hTpos).mp (Nat.floor_le hquot)
  have hfilter : (dyadicPairs N).filter
      (fun p => (p.1.gcd p.2 : ℝ) ≤ (N : ℝ)^2/T) =
      (dyadicPairs N).filter (fun p => p.1.gcd p.2 ≤ D) := by
    ext p
    simp only [Finset.mem_filter,D,Nat.le_floor_iff hquot]
  rw [hfilter]
  change (∑ p ∈ (dyadicPairs N).filter (fun p => p.1.gcd p.2 ≤ D),
    ratioMomentTermPow 3 W p) ≤ _
  rw [dyadicRatioKernelMomentPow_cutoff_eq_sum_reduced 3 W hN]
  have hh := hbound N D W T hN hT hDT hsep hcontained
  apply hh.trans
  have hpow := Real.rpow_le_rpow_of_exponent_le hTone hetaeps
  gcongr
  exact hpow

end GuthMaynardEnergy118Actual
#print axioms GuthMaynardEnergy118Actual.exists_actual_small_gcd_cubic_bound
