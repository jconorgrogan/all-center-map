import MRTDynamicD12CanonicalSourceLedger
import MRTDynamicD12ActiveTailWitnesses
import MRTDynamicD12CutoffPruning

/-! Active canonical D12 source ledger. The classifier's literal `if` is
preserved. Active bags use the one/two-shell witness; bags whose lower product
lies above `2X` use literal support pruning. -/
namespace MRTDynamicD12ActiveCanonicalLedger

open scoped BigOperators ArithmeticFunction
open ArithmeticFunction MeasureTheory
open MAPMRTCorollary53Source MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215ScaleClassifierV3
open MRTDynamicD12LiteralMass MRTDynamicD12MomentSource MRTDynamicD12FactorExtraction
open MRTDynamicD12CanonicalSourceLedger MRTDynamicD12ActiveTailWitnesses
open MRTDynamicD12CutoffPruning MRTDynamicD12ParameterPackage

noncomputable section
set_option maxHeartbeats 1800000
local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem exists_active_canonical_source_ledger
    (delta epsilon : ℝ) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 240) (hepsilon : 0 < epsilon) :
    ∃ D : ℝ, 0 < D ∧
    ∃ kappa1 Cm1 : ℝ, 0 < kappa1 ∧ 0 < Cm1 ∧ ∃ Em1 : ℕ,
    ∃ kappa2 Cm2 : ℝ, 0 < kappa2 ∧ 0 < Cm2 ∧ ∃ Em2 : ℕ,
      ∀ {p : Corollary53Input} [NeZero p.q] {B Cc : ℕ} {reserve : ℝ}
        (hp : Corollary53Admissible 1 1 p) (hX : 3 ≤ p.X)
        (pack : D12ParameterPackage p.X p B Cc reserve)
        (hcut : 2 ≤ ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊)
        {k : ℕ} (component : OuterComponent)
        (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
        (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X))))
          k)
        (mbag : Sym (Option (Fin
          (sourceDyadicCount ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊))) (k + 1))
        (hk : k < hbOrder delta),
        (if dynamicD12IsActive delta
            (Real.rpow p.X (delta + 1 / 8)) logIndex zbag mbag then
          componentIntegral p.X p.H 1 p.q
            (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
            p.beta p.eta component
        else 0) ≤
          max 0 (max
            (rawLedger p pack.P pack.Tmom (D * Real.rpow p.X epsilon)
              (factorLowerProduct (sortedComponentFactorList logIndex zbag mbag))
              delta kappa1 Cm1 Em1 component)
            (rawLedger p pack.P pack.Tmom (D * Real.rpow p.X epsilon)
              (factorLowerProduct (sortedComponentFactorList logIndex zbag mbag))
              delta kappa2 Cm2 Em2 component)) := by
  obtain ⟨D, hD, kappa1, Cm1, hk1, hc1, Em1,
      kappa2, Cm2, hk2, hc2, Em2, hsource⟩ :=
    exists_canonical_source_ledger (hbOrder delta) (hbOrder_one hdelta)
      epsilon hepsilon
  refine ⟨D, hD, kappa1, Cm1, hk1, hc1, Em1, kappa2, Cm2,
    hk2, hc2, Em2, ?_⟩
  intro p inst B Cc reserve hp hX pack hcut k component logIndex zbag mbag hk
  let Y : ℕ := factorLowerProduct (sortedComponentFactorList logIndex zbag mbag)
  let s := largestSmallPrefix
    (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
    (Real.rpow p.X delta)
  have hX2 : 2 ≤ p.X := by linarith
  have hgeom : Real.rpow p.X delta *
      (2 * Real.rpow p.X ((8 : ℝ)⁻¹)) ≤
        2 * Real.rpow p.X (delta + 1 / 8) := by
    have hXp : 0 < p.X := by linarith [pack.hX]
    have heq : Real.rpow p.X delta * Real.rpow p.X ((8 : ℝ)⁻¹) =
        Real.rpow p.X (delta + (8 : ℝ)⁻¹) :=
      (Real.rpow_add hXp _ _).symm
    have heq2 : Real.rpow p.X delta *
        (2 * Real.rpow p.X ((8 : ℝ)⁻¹)) =
        2 * Real.rpow p.X (delta + 1 / 8) := by
      calc
        Real.rpow p.X delta * (2 * Real.rpow p.X ((8 : ℝ)⁻¹)) =
            2 * (Real.rpow p.X delta * Real.rpow p.X ((8 : ℝ)⁻¹)) := by ring
        _ = 2 * Real.rpow p.X (delta + (8 : ℝ)⁻¹) := by rw [heq]
        _ = 2 * Real.rpow p.X (delta + 1 / 8) := by
          rw [show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
    exact heq2.le
  by_cases hprod : 2 * p.X < (Y : ℝ)
  · have hzero := componentIntegral_d12_eq_zero_of_lower_gt_twoX
      (X := p.X) (H := p.H) (beta := p.beta) (eta := p.eta)
      (q := p.q) (delta := delta) (K := hbOrder delta) (k := k)
      (by linarith [pack.hX]) (hbOrder_one hdelta) hk logIndex zbag mbag
      hprod component
    simp [hzero]
  · by_cases ha : dynamicD12IsActive delta
        (Real.rpow p.X (delta + 1 / 8)) logIndex zbag mbag
    · have hwitness := exists_active_d12_tail_witnesses
        (X := p.X) (delta := delta)
        (H₀ := Real.rpow p.X (delta + 1 / 8)) hX2 hdelta
        (by linarith [hdeltaUpper]) hgeom hcut logIndex zbag mbag ha
      have hcanon := hsource (p := p) (B := B) (Cc := Cc)
        (delta := delta) (k := k) hp (by linarith [pack.hX]) hdelta.le
          (by linarith [hdeltaUpper]) hk
        pack component logIndex zbag mbag s rfl
      dsimp [Y, s] at hcanon ⊢
      rcases hwitness with htail | htail
      · obtain ⟨beta, heq, hsmooth, hlen⟩ := htail
        change (if dynamicD12IsActive delta
            (Real.rpow p.X (delta + 1 / 8)) logIndex zbag mbag then _ else _) ≤ _
        rw [if_pos ha]
        exact (hcanon.1 beta heq hsmooth hlen).trans
          ((le_max_left _ _).trans (le_max_right _ _))
      · obtain ⟨beta, gamma, heq, hsmooth, hlen, hgsmooth, hglen⟩ := htail
        change (if dynamicD12IsActive delta
            (Real.rpow p.X (delta + 1 / 8)) logIndex zbag mbag then _ else _) ≤ _
        rw [if_pos ha]
        exact (hcanon.2 beta gamma heq hsmooth hlen hgsmooth hglen).trans
          ((le_max_right _ _).trans (le_max_right _ _))
    · change (if dynamicD12IsActive delta
        (Real.rpow p.X (delta + 1 / 8)) logIndex zbag mbag then _ else _) ≤ _
      rw [if_neg ha]
      exact le_max_left _ _

end
end MRTDynamicD12ActiveCanonicalLedger

#print axioms MRTDynamicD12ActiveCanonicalLedger.exists_active_canonical_source_ledger
