import MRTDynamicD12PerronMassAssembly
import MRTDynamicD12WeightedMultiplicity
import MRTLemma215DynamicTypeIIGlobalCountV3

/-! Finite global D12 aggregation after a source-indexed per-bag estimate.

The refined branch inequality contains one literal component multiplicity, and
`dynamicD12ExtractedBranchMass` contains the exact bag sum.  Consequently the
finite weld retains a squared multiplicity.  It is still polylogarithmic by
the established source-bag count, and no analytic mass estimate is assumed.
-/
namespace MRTDynamicD12GlobalAggregation

open scoped BigOperators ArithmeticFunction
open ArithmeticFunction
open MAPMRTCorollary25 MAPMRTCorollary53Source
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MAPFinishDynamicThreeTypeTrace MAPFinishDynamicLowTypes
open MAPFinishDynamicLowTypesRefinedV3
open MAPDynamicHBSourcePacketBoundRefinedV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicTypeIIGlobalCountV3
open MRTDynamicD12LiteralMass MRTDynamicD12PerronMassAssembly
open MRTDynamicD12WeightedMultiplicity

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 1200000

/-- The squared branch-weighted multiplicity remains polylogarithmic.  The
extra multiplicity is the one already present in the refined branch inequality
before the exact extracted bag sum is inserted. -/
theorem exists_d12_weighted_branch_multiplicity_sq_polylog
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∃ E : ℕ,
      ∀ {X : ℝ}, 3 ≤ X →
        (∑ branch : Fin (hbOrder delta),
          dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
            (dynamicLowComponentMultiplicityV3 X (hbOrder delta)
              (branch : ℕ) : ℝ) ^ 2) ≤
          C * Real.log X ^ E := by
  obtain ⟨C₀, hC₀, E₀, hcount⟩ :=
    exists_d12_weighted_branch_multiplicity_polylog delta hdelta
  have hK : 1 ≤ hbOrder delta := hbOrder_one hdelta
  let Cm : ℝ := 6 * ((6 + hbOrder delta : ℕ) : ℝ) ^ (2 * hbOrder delta)
  let Em : ℕ := 2 * hbOrder delta + 1
  refine ⟨Cm * C₀, mul_pos (by
    dsimp [Cm]
    positivity) hC₀, Em + E₀, ?_⟩
  intro X hX
  have hlog : 0 ≤ Real.log X :=
    (log_one_le hX).trans' (by norm_num)
  have hterm : ∀ (branch : Fin (hbOrder delta)),
      dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
          (dynamicLowComponentMultiplicityV3 X (hbOrder delta)
            (branch : ℕ) : ℝ) ^ 2 ≤
        dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
          (dynamicLowComponentMultiplicityV3 X (hbOrder delta)
            (branch : ℕ) : ℝ) *
            (Cm * Real.log X ^ Em) := by
    intro branch
    have hm := dynamicLowComponentMultiplicity_le_polylog hX branch.isLt
    have hm0 : 0 ≤
        (dynamicLowComponentMultiplicityV3 X (hbOrder delta)
          (branch : ℕ) : ℝ) := Nat.cast_nonneg _
    have hw : 0 ≤ dynamicBranchLowWeightRefinedV3
        (K := hbOrder delta) := by
      unfold dynamicBranchLowWeightRefinedV3
      positivity
    have hmul := mul_le_mul_of_nonneg_left hm hm0
    have hCm : Cm * Real.log X ^ Em =
        6 * ((6 + hbOrder delta : ℕ) : ℝ) ^ (2 * hbOrder delta) *
          Real.log X ^ (2 * hbOrder delta + 1) := by
      dsimp [Cm, Em]
    have hmul' :
        (dynamicLowComponentMultiplicityV3 X (hbOrder delta)
          (branch : ℕ) : ℝ) ^ 2 ≤
          (dynamicLowComponentMultiplicityV3 X (hbOrder delta)
            (branch : ℕ) : ℝ) * (Cm * Real.log X ^ Em) := by
      simpa [Cm, Em, pow_two, mul_assoc] using hmul
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmul' hw
  calc
    _ ≤ ∑ branch : Fin (hbOrder delta),
        dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
          (dynamicLowComponentMultiplicityV3 X (hbOrder delta)
            (branch : ℕ) : ℝ) * (Cm * Real.log X ^ Em) := by
      exact Finset.sum_le_sum (fun branch hbranch => hterm branch)
    _ = (Cm * Real.log X ^ Em) *
        (∑ branch : Fin (hbOrder delta),
          dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
            (dynamicLowComponentMultiplicityV3 X (hbOrder delta)
              (branch : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro branch _
      ring
    _ ≤ (Cm * Real.log X ^ Em) * (C₀ * Real.log X ^ E₀) := by
      gcongr
      exact hcount hX
    _ = (Cm * C₀) * Real.log X ^ (Em + E₀) := by
      calc
        Cm * Real.log X ^ Em * (C₀ * Real.log X ^ E₀) =
            Cm * C₀ * (Real.log X ^ Em * Real.log X ^ E₀) := by ring
        _ = (Cm * C₀) * Real.log X ^ (Em + E₀) := by
          rw [← pow_add]

/-- Exact global normalized D12 weld from a uniform per-active-bag estimate.
The hypothesis is source-indexed and retains the classifier `if`; it is not a
desired global mass bound. -/
theorem exists_normalized_d12_global_of_perbag
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∃ E : ℕ,
      ∀ {p : Corollary53Input} [NeZero p.q] {H₀ Ebag : ℝ},
        Corollary53Admissible 1 1 p → ∀ (hX : 3 ≤ p.X), 0 ≤ Ebag →
        (∀ (branch : Fin (hbOrder delta))
          (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
          (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X))))
            (branch : ℕ))
          (mbag : Sym (Option (Fin
            (sourceDyadicCount ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊)))
            ((branch : ℕ) + 1))
          (component : OuterComponent),
          dynamicLowNormalizationV3 p *
            (if dynamicD12IsActive delta H₀ logIndex zbag mbag then
              componentIntegral p.X p.H 1 p.q
                (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
                p.beta p.eta component
            else 0) ≤ Ebag) →
        dynamicLowNormalizationV3 p *
            (∑ component : OuterComponent,
              dynamicAllD12MassRefinedV3 p delta H₀
                (by linarith [hX]) hdelta component) ≤
          2 * C * Real.log p.X ^ E * Ebag := by
  obtain ⟨C, hC, E, hsq⟩ :=
    exists_d12_weighted_branch_multiplicity_sq_polylog delta hdelta
  refine ⟨C, hC, E, ?_⟩
  intro p inst H₀ Ebag hp hX hEbag hbag
  have hX2 : 2 ≤ p.X := by linarith
  have hnorm : 0 ≤ dynamicLowNormalizationV3 p := by
    unfold dynamicLowNormalizationV3
    positivity
  have hcomponent : ∀ component : OuterComponent,
      dynamicLowNormalizationV3 p *
          dynamicAllD12MassRefinedV3 p delta H₀ hX2 hdelta component ≤
        dynamicLowNormalizationV3 p *
          ∑ branch : Fin (hbOrder delta),
            dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
              (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
                (branch : ℕ) : ℝ) *
              dynamicD12ExtractedBranchMass p delta H₀ branch component := by
    intro component
    exact mul_le_mul_of_nonneg_left
      (dynamicAllD12MassRefined_le_extracted hp hX2 hdelta component)
      hnorm
  have hbranch : ∀ (branch : Fin (hbOrder delta)),
      dynamicLowNormalizationV3 p *
          (∑ component : OuterComponent,
            dynamicD12ExtractedBranchMass p delta H₀ branch component) ≤
        2 * (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
          (branch : ℕ) : ℝ) * Ebag := by
    intro branch
    calc
      dynamicLowNormalizationV3 p *
          (∑ component : OuterComponent,
            dynamicD12ExtractedBranchMass p delta H₀ branch component) =
        ∑ component : OuterComponent,
          dynamicLowNormalizationV3 p *
            dynamicD12ExtractedBranchMass p delta H₀ branch component := by
        rw [Finset.mul_sum]
      _ = ∑ component : OuterComponent,
          ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
            ∑ zbag ∈ dynamicLowZBagSetV3 p.X (branch : ℕ),
              ∑ mbag ∈ dynamicLowMBagSetV3 p.X (hbOrder delta)
                (branch : ℕ),
                dynamicLowNormalizationV3 p *
                  (if dynamicD12IsActive delta H₀ logIndex zbag mbag then
                    componentIntegral p.X p.H 1 p.q
                      (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
                      p.beta p.eta component
                  else 0) := by
        unfold dynamicD12ExtractedBranchMass
        simp only [Finset.mul_sum, Finset.sum_mul]
      _ ≤ ∑ component : OuterComponent,
          ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
            ∑ zbag ∈ dynamicLowZBagSetV3 p.X (branch : ℕ),
              ∑ mbag ∈ dynamicLowMBagSetV3 p.X (hbOrder delta)
                (branch : ℕ), Ebag := by
        apply Finset.sum_le_sum
        intro component hcomponent
        apply Finset.sum_le_sum
        intro logIndex hlog
        apply Finset.sum_le_sum
        intro zbag hzbag
        apply Finset.sum_le_sum
        intro mbag hmbag
        exact hbag branch logIndex zbag mbag component
      _ = 2 * (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
          (branch : ℕ) : ℝ) * Ebag := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hcard : (Fintype.card OuterComponent : ℝ) = 2 := by
          exact_mod_cast card_outerComponent
        rw [hcard]
        unfold dynamicLowComponentMultiplicityV3
        simp [Finset.card_univ]
        ring
  calc
    dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent,
          dynamicAllD12MassRefinedV3 p delta H₀ hX2 hdelta component) =
      ∑ component : OuterComponent,
        dynamicLowNormalizationV3 p *
          dynamicAllD12MassRefinedV3 p delta H₀ hX2 hdelta component := by
      rw [Finset.mul_sum]
    _ ≤ ∑ component : OuterComponent,
        dynamicLowNormalizationV3 p *
          ∑ branch : Fin (hbOrder delta),
            dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
              (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
                (branch : ℕ) : ℝ) *
              dynamicD12ExtractedBranchMass p delta H₀ branch component := by
      exact Finset.sum_le_sum (fun component _ =>
        hcomponent component)
    _ = ∑ branch : Fin (hbOrder delta),
        dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
          (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
            (branch : ℕ) : ℝ) *
          (dynamicLowNormalizationV3 p *
            ∑ component : OuterComponent,
              dynamicD12ExtractedBranchMass p delta H₀ branch component) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro branch _
      ring
    _ ≤ ∑ branch : Fin (hbOrder delta),
        dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
          (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
            (branch : ℕ) : ℝ) *
          (2 * (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
            (branch : ℕ) : ℝ) * Ebag) := by
      apply Finset.sum_le_sum
      intro branch _
      have hw : 0 ≤ dynamicBranchLowWeightRefinedV3
          (K := hbOrder delta) := by
        unfold dynamicBranchLowWeightRefinedV3
        positivity
      have hm : 0 ≤
          (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
            (branch : ℕ) : ℝ) := Nat.cast_nonneg _
      exact mul_le_mul_of_nonneg_left (hbranch branch)
        (mul_nonneg hw hm)
    _ = 2 * Ebag *
        (∑ branch : Fin (hbOrder delta),
          dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
            (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
              (branch : ℕ) : ℝ) ^ 2) := by
      calc
        _ = ∑ branch : Fin (hbOrder delta),
            2 * Ebag *
              (dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
                (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
                  (branch : ℕ) : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro branch _
          ring
        _ = _ := by rw [Finset.mul_sum]
    _ ≤ 2 * Ebag * (C * Real.log p.X ^ E) := by
      gcongr
      exact hsq hX
    _ = 2 * C * Real.log p.X ^ E * Ebag := by ring

end
end MRTDynamicD12GlobalAggregation

#print axioms MRTDynamicD12GlobalAggregation.exists_d12_weighted_branch_multiplicity_sq_polylog
#print axioms MRTDynamicD12GlobalAggregation.exists_normalized_d12_global_of_perbag
