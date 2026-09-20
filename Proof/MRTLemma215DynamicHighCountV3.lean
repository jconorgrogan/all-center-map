import MRTLemma215DynamicTypeIIGlobalCountV3
import MRTLemma215DynamicHighPacketFlattenV3

/-! Literal high-packet counts for fixed HB order. Every raw bag, log-shell,
surviving complement cell, and branch index is retained. -/
namespace MRTLemma215DynamicHighCountV3
open scoped BigOperators
open MAPDynamicHBSourceV3 MAPFinishDynamicThreeTypeTrace
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215DynamicHighPacketAggregateV3 MRTLemma215DynamicHighPacketFlattenV3
open MRTLemma215DynamicMultiplicityBoundsV3 MRTLemma215DynamicTypeIIGlobalCountV3
open MRTLemma215DynamicTypeIIFiniteEnvelopeV3
noncomputable section

/-- The raw branch index counts exactly the log shell and both complete
symmetric-bag enumerators, including every `none` entry. -/
theorem branchRaw_card_eq_multiplicity (X : ℝ) (K : ℕ) (branch : Fin K) :
    Fintype.card (DynamicBranchRawComponentIndexV3 X K branch) =
      dynamicLowComponentMultiplicityV3 X K (branch : ℕ) := by
  classical
  change Fintype.card ↥(dynamicBranchRawComponentFinsetV3 X K branch) = _
  rw [Fintype.card_coe]
  unfold dynamicBranchRawComponentFinsetV3 dynamicLowComponentMultiplicityV3
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  dsimp [dynamicLowZBagSetV3, dynamicLowMBagSetV3]
  ring


/-- Being high is a predicate on a raw component, not an additional index. -/
theorem branchHighComponent_card_le_multiplicity (X delta H₀ : ℝ) (K : ℕ) (branch : Fin K) :
    Fintype.card (DynamicBranchHighComponentIndexV3 X delta H₀ K branch) ≤
      dynamicLowComponentMultiplicityV3 X K (branch : ℕ) := by
  classical
  calc
    _ ≤ Fintype.card (DynamicBranchRawComponentIndexV3 X K branch) :=
      Fintype.card_le_of_injective _ Subtype.val_injective
    _ = _ := branchRaw_card_eq_multiplicity X K branch

/-- Removing the selected factor leaves at most `2K` factors, each of length
at most `2X`; consequently the complete complementary shell index is logarithmic. -/
theorem highComplement_sourceDyadicCount_le
    {X delta H₀ : ℝ} {K : ℕ} (hX : 3 ≤ X)
    (c : DynamicHighComponentIndexV3 X delta H₀ K) :
    (sourceDyadicCount (factorUpperProduct (highComplementV3 c)) : ℝ) ≤
      18 * K * Real.log X := by
  have hk := (rawBranchV3 c.1).isLt
  have hK : 1 ≤ K := by omega
  have hflen := sortedComponentFactorList_length_le
    (rawLogIndexV3 c.1) (rawZetaBagV3 c.1) (rawMoebiusBagV3 c.1)
  have hlen : (highComplementV3 c).length ≤ 2 * K := by
    dsimp [highComplementV3, complementFactorList]
    simp only [List.length_append, List.length_take, List.length_drop]
    dsimp [rawBranchV3] at hk
    dsimp [highFactorsV3] at *
    omega
  have hmem : ∀ f ∈ highComplementV3 c, f ∈ highFactorsV3 c := by
    intro f hf
    unfold highComplementV3 complementFactorList at hf
    rcases List.mem_append.mp hf with hf | hf
    · exact List.mem_of_mem_take hf
    · exact List.mem_of_mem_drop hf
  have hp := factorUpperProduct_le_cube_pow hX (highComplementV3 c)
    (fun f hf => sortedComponentFactor_length_le_two_mul hX hK
      (rawLogIndexV3 c.1) (rawZetaBagV3 c.1) (rawMoebiusBagV3 c.1) (hmem f hf))
  have hpow : (factorUpperProduct (highComplementV3 c) : ℝ) ≤ X ^ (6 * K) := by
    calc
      _ ≤ (X ^ 3) ^ (highComplementV3 c).length := hp
      _ = X ^ (3 * (highComplementV3 c).length) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  have hb := sourceDyadicCount_nat_le_three_mul_degree_log hX (by omega : 1 ≤ 6 * K) hpow
  push_cast at hb
  nlinarith

/-- Uniform explicit cardinality bound for the full surviving high packet index
of a fixed branch. No coefficient mask or index multiplicity is discarded. -/
theorem branchHighPacket_card_le_polylog
    {X delta H₀ : ℝ} {K : ℕ} (hX : 3 ≤ X)
    (hX₂ : 2 ≤ X) (hdelta : 0 < delta) (branch : Fin K) :
    (Fintype.card (DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX₂ hdelta branch) : ℝ) ≤
      (108 * K * ((6 + K : ℕ) : ℝ) ^ (2 * K)) * Real.log X ^ (2 * K + 2) := by
  classical
  have hlog : 0 ≤ Real.log X := (log_one_le hX).trans' (by norm_num)
  have hcomp : (Fintype.card (DynamicBranchHighComponentIndexV3 X delta H₀ K branch) : ℝ) ≤
      (dynamicLowComponentMultiplicityV3 X K (branch : ℕ) : ℝ) := by
    exact_mod_cast branchHighComponent_card_le_multiplicity X delta H₀ K branch
  have hmult := dynamicLowComponentMultiplicity_le_polylog hX branch.isLt
  have hcard : Fintype.card (DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX₂ hdelta branch) =
      ∑ c : DynamicBranchHighComponentIndexV3 X delta H₀ K branch,
        Fintype.card {cell : Fin (sourceDyadicCount (factorUpperProduct (highComplementV3 (branchHighToGlobalV3 c)))) //
          cell ∈ MRTLemma215DynamicHighPacketsV3.survivingComplementCells
            (highSelectedFactorV3 hX₂ hdelta (branchHighToGlobalV3 c)).length
            (highComplementV3 (branchHighToGlobalV3 c))} := by
    exact Fintype.card_sigma
  rw [hcard]
  push_cast
  calc
    _ ≤ ∑ c : DynamicBranchHighComponentIndexV3 X delta H₀ K branch,
        (18 * K * Real.log X : ℝ) := by
      apply Finset.sum_le_sum
      intro c hc
      have hb : Fintype.card
          {cell : Fin (sourceDyadicCount (factorUpperProduct (highComplementV3 (branchHighToGlobalV3 c)))) //
            cell ∈ MRTLemma215DynamicHighPacketsV3.survivingComplementCells
              (highSelectedFactorV3 hX₂ hdelta (branchHighToGlobalV3 c)).length
              (highComplementV3 (branchHighToGlobalV3 c))} ≤
          sourceDyadicCount (factorUpperProduct (highComplementV3 (branchHighToGlobalV3 c))) := by
        simpa using Fintype.card_le_of_injective
          (fun cell : {cell : Fin (sourceDyadicCount (factorUpperProduct (highComplementV3 (branchHighToGlobalV3 c)))) //
            cell ∈ MRTLemma215DynamicHighPacketsV3.survivingComplementCells
              (highSelectedFactorV3 hX₂ hdelta (branchHighToGlobalV3 c)).length
              (highComplementV3 (branchHighToGlobalV3 c))} => cell.val)
          Subtype.val_injective
      exact (by exact_mod_cast hb : (_ : ℝ) ≤ _).trans
        (highComplement_sourceDyadicCount_le hX (branchHighToGlobalV3 c))
    _ = (Fintype.card (DynamicBranchHighComponentIndexV3 X delta H₀ K branch) : ℝ) *
        (18 * K * Real.log X) := by simp
    _ ≤ (dynamicLowComponentMultiplicityV3 X K (branch : ℕ) : ℝ) *
        (18 * K * Real.log X) := mul_le_mul_of_nonneg_right hcomp (by positivity)
    _ ≤ ((6 * ((6 + K : ℕ) : ℝ) ^ (2 * K)) * Real.log X ^ (2 * K + 1)) *
        (18 * K * Real.log X) := mul_le_mul_of_nonneg_right hmult (by positivity)
    _ = _ := by
      rw [show 2 * K + 2 = (2 * K + 1) + 1 by omega, pow_succ]
      push_cast
      ring

/-- Constants precede every analytic parameter, including `X`, `delta`, and
`H₀`; the exponent depends only on the fixed HB order. -/
theorem exists_fixedOrder_branchHighPacket_card_bound (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ, ∀ {X delta H₀ : ℝ}
      (hX : 3 ≤ X) (hX₂ : 2 ≤ X) (hdelta : 0 < delta) (branch : Fin K),
      (Fintype.card (DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX₂ hdelta branch) : ℝ) ≤
        C * Real.log X ^ R := by
  refine ⟨1 + 108 * K * ((6 + K : ℕ) : ℝ) ^ (2 * K), by positivity, 2 * K + 2, ?_⟩
  intro X delta H₀ hX hX₂ hdelta branch
  exact (branchHighPacket_card_le_polylog hX hX₂ hdelta branch).trans
    (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg ((log_one_le hX).trans' (by norm_num)) _))

end
end MRTLemma215DynamicHighCountV3
#print axioms MRTLemma215DynamicHighCountV3.branchHighPacket_card_le_polylog
#print axioms MRTLemma215DynamicHighCountV3.exists_fixedOrder_branchHighPacket_card_bound
