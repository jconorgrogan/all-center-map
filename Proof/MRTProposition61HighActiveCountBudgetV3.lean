import MRTLemma215DynamicHighCountV3
import MRTLemma215DynamicHighCellPruningV3

/-! # Exact high-source packet and Cauchy-weight totals -/

namespace MRTProposition61HighActiveCountBudgetV3

open scoped BigOperators
open MAPDynamicHBSourceV3 MAPDynamicHBScaledPacketSourceV3
open MAPDynamicHBScaledPacketSourceRefinedV3 MAPDynamicHBSourcePacketBoundRefinedV3
open MRTLemma215DynamicHighCountV3 MRTLemma215DynamicHighCellPruningV3
open MRTLemma215DynamicHighPacketFlattenV3 MRTLemma215DynamicTypeIIGlobalCountV3

noncomputable section
set_option maxHeartbeats 1000000

/-- Both the literal active packet count and the sum of its original Cauchy
weights have fixed-order logarithmic envelopes before every input parameter. -/
theorem exists_active_count_and_weight_polylog (delta : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ, ∀ {X H₀ : ℝ}
      (hX : 3 ≤ X) (hX₂ : 2 ≤ X) (hdelta : 0 < delta),
      ((activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX₂ hdelta).card : ℝ) ≤ C * Real.log X ^ R ∧
      (∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX₂ hdelta,
        dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX₂ hdelta packet.1) ≤ C * Real.log X ^ R := by
  classical
  let K := hbOrder delta
  obtain ⟨C, hC, R, hcard⟩ := exists_fixedOrder_branchHighPacket_card_bound K
  let D := 1 + K * C + 2 * (K : ℝ) ^ 2 * C ^ 2
  refine ⟨D, by dsimp [D]; positivity, 2 * R, ?_⟩
  intro X H₀ hX hX₂ hdelta
  have hlog : 1 ≤ Real.log X := log_one_le hX
  have hlog0 : 0 ≤ Real.log X := by linarith
  have hpow : Real.log X ^ R ≤ Real.log X ^ (2 * R) :=
    pow_le_pow_right₀ hlog (by omega)
  have htotalCard : (Fintype.card (DynamicAllHighPacketIndexV3 (H₀ := H₀) hX₂ hdelta) : ℝ) ≤
      K * C * Real.log X ^ R := by
    have hraw : Fintype.card (DynamicAllHighPacketIndexV3 (H₀ := H₀) hX₂ hdelta) =
        ∑ branch : Fin K, Fintype.card (DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX₂ hdelta branch) :=
      Fintype.card_sigma
    rw [hraw, Nat.cast_sum]
    calc
      _ ≤ ∑ branch : Fin K, C * Real.log X ^ R :=
        Finset.sum_le_sum fun branch _ => hcard hX hX₂ hdelta branch
      _ = _ := by simp; ring
  constructor
  · have ha : ((activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX₂ hdelta).card : ℝ) ≤
        Fintype.card (DynamicAllHighPacketIndexV3 (H₀ := H₀) hX₂ hdelta) := by
      exact_mod_cast Finset.card_le_univ (activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX₂ hdelta)
    have hc : (K : ℝ) * C ≤ D := by dsimp [D]; nlinarith
    exact (ha.trans htotalCard).trans (mul_le_mul hc hpow (pow_nonneg hlog0 _) (by dsimp [D]; positivity))
  · have hall : (∑ packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX₂ hdelta,
        dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX₂ hdelta packet.1) =
        ∑ branch : Fin K, 2 * (K : ℝ) *
          (Fintype.card (DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX₂ hdelta branch) : ℝ) ^ 2 := by
      change (∑ packet : (Σ branch : Fin K,
        DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX₂ hdelta branch),
        dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX₂ hdelta packet.1) = _
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro branch hb
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      unfold dynamicBranchHighWeightRefinedV3
      dsimp [K]
      ring
    calc
      _ ≤ ∑ packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX₂ hdelta,
          dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX₂ hdelta packet.1 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro packet hp hnot
        exact dynamicBranchHighWeightRefinedV3_nonneg hX₂ hdelta packet.1
      _ = _ := hall
      _ ≤ ∑ branch : Fin K, 2 * (K : ℝ) * (C * Real.log X ^ R) ^ 2 := by
        apply Finset.sum_le_sum
        intro branch hb
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (hcard hX hX₂ hdelta branch) 2) (by positivity)
      _ = 2 * (K : ℝ) ^ 2 * C ^ 2 * Real.log X ^ (2 * R) := by simp; ring
      _ ≤ D * Real.log X ^ (2 * R) :=
        mul_le_mul_of_nonneg_right (by dsimp [D]; nlinarith [mul_nonneg (Nat.cast_nonneg K) hC.le]) (pow_nonneg hlog0 _)

end
end MRTProposition61HighActiveCountBudgetV3

#print axioms MRTProposition61HighActiveCountBudgetV3.exists_active_count_and_weight_polylog
