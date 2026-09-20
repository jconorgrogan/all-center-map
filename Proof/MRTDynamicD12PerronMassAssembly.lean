import MRTDynamicD12PerronTransfer
import MRTDynamicD12LiteralMass
import MRTLemma215DynamicTypeIIGlobalCountV3
import MAPFinishDynamicLowTypesRefinedV3
import MAPDynamicHBSourcePacketBoundRefinedV3

/-! Concrete finitary d1/d2 producers.

The first theorem specializes the proved cutoff transfer to one fixed support
dilation.  The second is the exact finite branch/bag assembly: once a genuine
per-bag cell majorant is supplied, all log-indexes, z-bags, m-bags and the two
outer components are summed with the existing multiplicity.  No desired mass
estimate is an input to either theorem. -/
namespace MRTDynamicD12PerronMassAssembly

open scoped BigOperators ArithmeticFunction
open ArithmeticFunction
open MeasureTheory
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25Minkowski
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3 MAPFinishDynamicLowTypesRefinedV3
open MAPFinishDynamicThreeTypeTrace
open MAPDynamicHBSourcePacketBoundRefinedV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion MRTLemma215OpenIntervalCutoffV3
open MRTLemma215DynamicTypeIIGlobalCountV3
open MRTDynamicD12PerronTransfer MRTDynamicD12LiteralMass

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 1200000

def d12SupportDilation (K : ℕ) : ℝ := (2 : ℝ) ^ (2 * K)

theorem d12SupportDilation_gt_one {K : ℕ} (hK : 1 ≤ K) :
    1 < d12SupportDilation K := by
  unfold d12SupportDilation
  have hpow : (2 : ℝ) ^ (2 : ℕ) ≤ (2 : ℝ) ^ (2 * K) :=
    pow_le_pow_right₀ (by norm_num) (by omega : 2 ≤ 2 * K)
  linarith

theorem card_outerComponent : Fintype.card OuterComponent = 2 := by
  decide

/-- One Perron constant, before every source datum and every bag. -/
theorem exists_d12_component_cutoff_transfer (K : ℕ) (hK : 1 ≤ K) :
    ∃ κ : ℝ, 0 < κ ∧
    ∀ {X H beta eta Y P B : ℝ} {q : ℕ} {f : ℕ → ℂ},
      0 ≤ X → 0 ≤ H → 0 < eta → eta ≤ 1 →
      1 ≤ Y → 1 ≤ P → 0 ≤ B →
      SupportedNear Y (d12SupportDilation K) f →
      (∀ n, ‖f n‖ ≤ B) → ∀ component : OuterComponent,
      let a := (componentEndpoints X beta eta component).1
      let b := (componentEndpoints X beta eta component).2
      let U := stationaryWidth beta H
      componentIntegral X H 1 q
          (intervalCutoff (openSourceLeft X) (2 * X) f) beta eta component ≤
        2 * κ ^ 2 *
          ((∫ u in (-P)..P, perronWeight u) ^ 2 *
            (∫ s in (a-P)..(b+P),
              (characterMovingMass
                (fun chi : DirichletCharacter ℂ q => fun t =>
                  ‖halfLineDirichletPolynomial Y (d12SupportDilation K)
                    (characterTwist (fun n => chi n) f) t‖) U s) ^ 2) +
            (b-a) * (2*U*(Fintype.card (DirichletCharacter ℂ q) : ℝ) *
              (B * Real.sqrt Y * Real.log (2+P) / P)) ^ 2) :=
  exists_component_cutoff_transfer (d12SupportDilation K)
    (d12SupportDilation_gt_one hK)

theorem sum_extracted_le_multiplicity_mul
    {p : Corollary53Input} {delta H₀ M : ℝ} {K : ℕ}
    (hM : 0 ≤ M) (branch : Fin K)
    (hpoint : ∀ (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
        (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X))))
          (branch : ℕ))
        (mbag : Sym (Option (Fin (sourceDyadicCount
          ⌊dynamicHBCutoff p.X K⌋₊))) ((branch : ℕ) + 1))
        (component : OuterComponent),
        (if dynamicD12IsActive delta H₀ logIndex zbag mbag then
            componentIntegral p.X p.H 1 p.q
              (dynamicD12FactorizedCoeff (delta := delta) logIndex zbag mbag)
              p.beta p.eta component
          else 0) ≤ M) :
    (∑ component : OuterComponent,
      dynamicD12ExtractedBranchMass p delta H₀ branch component) ≤
        2 * (dynamicLowComponentMultiplicityV3 p.X K (branch : ℕ) : ℝ) * M := by
  classical
  have hcomp :
      (∑ component : OuterComponent,
        dynamicD12ExtractedBranchMass p delta H₀ branch component) =
        ∑ component : OuterComponent,
          ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
            ∑ zbag ∈ dynamicLowZBagSetV3 p.X (branch : ℕ),
              ∑ mbag ∈ dynamicLowMBagSetV3 p.X K (branch : ℕ),
                if dynamicD12IsActive delta H₀ logIndex zbag mbag then
                  componentIntegral p.X p.H 1 p.q
                    (dynamicD12FactorizedCoeff (delta := delta) logIndex zbag mbag)
                    p.beta p.eta component
                else 0 := by
    apply Finset.sum_congr rfl
    intro component _
    rfl
  have hcard : (Fintype.card OuterComponent : ℝ) = 2 := by
    exact_mod_cast card_outerComponent
  have hcount :
      ((Finset.univ : Finset (Fin (sourceDyadicCount (hbFactorCutoff p.X)))).card : ℝ) *
      ((dynamicLowZBagSetV3 p.X (branch : ℕ)).card : ℝ) *
      ((dynamicLowMBagSetV3 p.X K (branch : ℕ)).card : ℝ) =
        (dynamicLowComponentMultiplicityV3 p.X K (branch : ℕ) : ℝ) := by
    unfold dynamicLowComponentMultiplicityV3
    simp [Finset.card_univ]
  have hcount' :
      (Fintype.card (Fin (sourceDyadicCount (hbFactorCutoff p.X))) : ℝ) *
      ((dynamicLowZBagSetV3 p.X (branch : ℕ)).card : ℝ) *
      ((dynamicLowMBagSetV3 p.X K (branch : ℕ)).card : ℝ) =
        (dynamicLowComponentMultiplicityV3 p.X K (branch : ℕ) : ℝ) := by
    simpa only [Finset.card_univ] using hcount
  rw [hcomp]
  have hle :
      (∑ component : OuterComponent,
        ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
          ∑ zbag ∈ dynamicLowZBagSetV3 p.X (branch : ℕ),
            ∑ mbag ∈ dynamicLowMBagSetV3 p.X K (branch : ℕ),
              if dynamicD12IsActive delta H₀ logIndex zbag mbag then
                componentIntegral p.X p.H 1 p.q
                  (dynamicD12FactorizedCoeff (delta := delta) logIndex zbag mbag)
                  p.beta p.eta component
              else 0) ≤
        ∑ component : OuterComponent,
          ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
            ∑ zbag ∈ dynamicLowZBagSetV3 p.X (branch : ℕ),
              ∑ mbag ∈ dynamicLowMBagSetV3 p.X K (branch : ℕ), M := by
    apply Finset.sum_le_sum
    intro component _
    apply Finset.sum_le_sum
    intro logIndex _
    apply Finset.sum_le_sum
    intro zbag hz
    apply Finset.sum_le_sum
    intro mbag hm
    exact hpoint logIndex zbag mbag component
  have hconst :
      (∑ component : OuterComponent,
        ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
          ∑ zbag ∈ dynamicLowZBagSetV3 p.X (branch : ℕ),
        ∑ mbag ∈ dynamicLowMBagSetV3 p.X K (branch : ℕ), M) =
        2 * (dynamicLowComponentMultiplicityV3 p.X K (branch : ℕ) : ℝ) * M := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcard]
    nlinarith [hcount']
  exact hle.trans (le_of_eq hconst)

end
end MRTDynamicD12PerronMassAssembly

#print axioms MRTDynamicD12PerronMassAssembly.exists_d12_component_cutoff_transfer
#print axioms MRTDynamicD12PerronMassAssembly.sum_extracted_le_multiplicity_mul
