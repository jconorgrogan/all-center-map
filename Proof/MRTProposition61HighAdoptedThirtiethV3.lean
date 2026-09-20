import MRTProposition61HighEnvelopeSplitV3
import MRTProposition61HighActivePacketDataV3
import MAPFinishDynamicLowTypes
import MAPPacketIndexedFarSourceV2

/-!
# Adopted high `/30` welded to the active-certificate `/5` slot

`selectedHighMass` is the active-mask free-T mixed total plus the
sharp-maximum Perron errors. It is the high piece of
`activePacketCertificate_of_expandedBudget`, not the original constructor
field `DynamicV3TermwiseBudget.high_packets` (all packets, truncation `p.X`,
L1 companion errors). `H^{-2}` is applied once via
`dynamicLowNormalizationV3 = d(q)^4 / (q U^2)`.

This module records the expanded-RHS identity and converts the adopted
`/30` into that certificate's high `/5` slot.
-/

namespace MRTProposition61HighAdoptedThirtiethV3

open scoped BigOperators
open Filter
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPMRTProposition51Source
open MAPDynamicHBSourceV3
open MAPDynamicHBScaledPacketSourceRefinedV3
open MAPDynamicHBSourcePacketBoundRefinedV3
open MAPFinishDynamicLowTypes
open MAPPacketIndexedFarSourceV2
open MRTProposition61HighActivePacketDataV3
open MRTProposition61HighEnvelopeSplitV3

noncomputable section

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- High mixed-plus-error contribution of the adopted expanded RHS. -/
def activeCertificateHighSlot (p : Corollary53Input) [NeZero p.q]
    (delta : ℝ) (hX : 2 ≤ p.X) (hdelta : 0 < delta) : ℝ :=
  dynamicLowNormalizationV3 p * selectedHighMass p delta hX hdelta

theorem activeCertificateHighSlot_eq
    (p : Corollary53Input) [NeZero p.q]
    (delta : ℝ) (hX : 2 ≤ p.X) (hdelta : 0 < delta) :
    activeCertificateHighSlot p delta hX hdelta =
      dynamicLowNormalizationV3 p * selectedHighMass p delta hX hdelta :=
  rfl

theorem selectedHighMass_eq_highActivePacketMass
    {p : Corollary53Input} [NeZero p.q] {delta : ℝ}
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) :
    selectedHighMass p delta hX hdelta =
      highActivePacketMass (H₀ := highClassifierH0 p.X delta) p
        (selectedHighTruncation p) hX hdelta :=
  rfl

/-- Adopted expanded core = remainder + low + selected high mixed-plus-error. -/
theorem adopted_expanded_core_splits_high
    {p : Corollary53Input} [NeZero p.q] {delta : ℝ}
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) :
    activeExpandedCore
        (H₀ := highClassifierH0 p.X delta)
        (selectedHighTruncation p) hX hdelta =
      (∑ component : OuterComponent, smallRemainderMass p component) +
        (∑ component : OuterComponent,
          dynamicAllLowMassRefinedV3 p delta (highClassifierH0 p.X delta)
            hX hdelta component) +
        selectedHighMass p delta hX hdelta := by
  unfold activeExpandedCore selectedHighMass highActivePacketMass
    highActiveErrorTotal
  simp_rw [Finset.sum_add_distrib]
  abel

theorem dynamicLowNormalizationV3_eq_divisor_over_width_sq
    (p : Corollary53Input) :
    dynamicLowNormalizationV3 p =
      (divisorCount p.q : ℝ) ^ 4 /
        (p.q * stationaryWidth p.beta p.H ^ 2) :=
  rfl

/-- Exact high contribution inside the adopted certificate's expanded RHS. -/
theorem expandedRHS_active_selected_eq
    {p : Corollary53Input} [NeZero p.q] {delta : ℝ}
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) :
    expandedPacketIndexedSourceRHS p
        (activePacketIndexedData
          (H₀ := highClassifierH0 p.X delta)
          (selectedHighTruncation p) hX hdelta) =
      dynamicLowNormalizationV3 p *
          ((∑ component : OuterComponent, smallRemainderMass p component) +
            (∑ component : OuterComponent,
              dynamicAllLowMassRefinedV3 p delta (highClassifierH0 p.X delta)
                hX hdelta component) +
            selectedHighMass p delta hX hdelta) +
        ordinaryError p.X p.H p.f p.beta p.eta := by
  rw [expandedSourceRHS_active_eq (H₀ := highClassifierH0 p.X delta)
    (selectedHighTruncation p) hX hdelta]
  rw [adopted_expanded_core_splits_high hX hdelta,
    dynamicLowNormalizationV3_eq_divisor_over_width_sq]

theorem expandedRHS_active_high_slot
    {p : Corollary53Input} [NeZero p.q] {delta : ℝ}
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) :
    dynamicLowNormalizationV3 p *
        ((∑ component : OuterComponent, smallRemainderMass p component) +
          (∑ component : OuterComponent,
            dynamicAllLowMassRefinedV3 p delta (highClassifierH0 p.X delta)
              hX hdelta component) +
          selectedHighMass p delta hX hdelta) =
      dynamicLowNormalizationV3 p *
          (∑ component : OuterComponent, smallRemainderMass p component) +
        dynamicLowNormalizationV3 p *
          (∑ component : OuterComponent,
            dynamicAllLowMassRefinedV3 p delta (highClassifierH0 p.X delta)
              hX hdelta component) +
        activeCertificateHighSlot p delta hX hdelta := by
  unfold activeCertificateHighSlot
  ring

/-- Four adopted pieces, each `≤ budget/5`, imply the active expanded RHS
is `≤ budget`. Mixed and sharp-max errors share one `/5` (the high slot).
This does not fill `DynamicV3TermwiseBudget.high_packets`. -/
theorem active_expanded_rhs_le_of_high_fifth
    {p : Corollary53Input} [NeZero p.q] {delta budget : ℝ}
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) (hbudget : 0 ≤ budget)
    (hrem : dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent, smallRemainderMass p component) ≤
      budget / 5)
    (hlow : dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent,
          dynamicAllLowMassRefinedV3 p delta (highClassifierH0 p.X delta)
            hX hdelta component) ≤
      budget / 5)
    (hhigh : activeCertificateHighSlot p delta hX hdelta ≤ budget / 5)
    (hord : ordinaryError p.X p.H p.f p.beta p.eta ≤ budget / 5) :
    expandedPacketIndexedSourceRHS p
        (activePacketIndexedData
          (H₀ := highClassifierH0 p.X delta)
          (selectedHighTruncation p) hX hdelta) ≤
      budget := by
  have hsplit := expandedRHS_active_selected_eq hX hdelta
  have hdist := expandedRHS_active_high_slot hX hdelta
  have hsum :
      dynamicLowNormalizationV3 p *
            (∑ component : OuterComponent, smallRemainderMass p component) +
          dynamicLowNormalizationV3 p *
            (∑ component : OuterComponent,
              dynamicAllLowMassRefinedV3 p delta (highClassifierH0 p.X delta)
                hX hdelta component) +
          activeCertificateHighSlot p delta hX hdelta +
          ordinaryError p.X p.H p.f p.beta p.eta ≤
        budget / 5 + budget / 5 + budget / 5 + budget / 5 :=
    add_le_add (add_le_add (add_le_add hrem hlow) hhigh) hord
  have hfour : budget / 5 + budget / 5 + budget / 5 + budget / 5 ≤ budget := by
    have hfrac : (4 : ℝ) / 5 ≤ 1 := by norm_num
    have : budget / 5 + budget / 5 + budget / 5 + budget / 5 =
        (4 : ℝ) / 5 * budget := by ring
    rw [this]
    nlinarith
  calc
    expandedPacketIndexedSourceRHS p
        (activePacketIndexedData
          (H₀ := highClassifierH0 p.X delta)
          (selectedHighTruncation p) hX hdelta)
        = dynamicLowNormalizationV3 p *
            ((∑ component : OuterComponent, smallRemainderMass p component) +
              (∑ component : OuterComponent,
                dynamicAllLowMassRefinedV3 p delta (highClassifierH0 p.X delta)
                  hX hdelta component) +
              selectedHighMass p delta hX hdelta) +
          ordinaryError p.X p.H p.f p.beta p.eta := hsplit
    _ = dynamicLowNormalizationV3 p *
            (∑ component : OuterComponent, smallRemainderMass p component) +
          dynamicLowNormalizationV3 p *
            (∑ component : OuterComponent,
              dynamicAllLowMassRefinedV3 p delta (highClassifierH0 p.X delta)
                hX hdelta component) +
          activeCertificateHighSlot p delta hX hdelta +
          ordinaryError p.X p.H p.f p.beta p.eta := by
        rw [hdist]
    _ ≤ budget / 5 + budget / 5 + budget / 5 + budget / 5 := hsum
    _ ≤ budget := hfour

/-- Type-II-shaped `/30` for the adopted high field, re-exported under this
namespace so the weld does not depend on the Loop 1 name. -/
theorem exists_adopted_high_budget_thirtieth
    (delta A : ℝ) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 240) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
          ∀ (p : Corollary53Input) [NeZero p.q]
            (hp : Corollary53Admissible 1 1 p) (hpX : p.X = X)
            (reserve : ℝ) (hr0 : 0 ≤ reserve) (hr : reserve ≤ 1 / 1200)
            (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
            (heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B))
            (hqQ : (p.q : ℝ) ≤ (Real.log p.X) ^ B)
            (hbeta : |p.beta| ≤ 1 / ((p.q : ℝ) * (Real.log p.X) ^ B))
            (hfar : 2 * (Real.log p.X) ^ Cc < stationaryWidth p.beta p.H)
            (hXp : 2 ≤ p.X),
            activeCertificateHighSlot p delta hXp hdelta ≤
              p.X * Real.rpow (Real.log p.X) (-A) / 30 := by
  obtain ⟨B₀, hB₀⟩ :=
    exists_refined_high_budget_threshold delta A hdelta hdeltaUpper
  refine ⟨B₀, ?_⟩
  intro B hB
  obtain ⟨Cc₀, hCc₀⟩ := hB₀ B hB
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc
  obtain ⟨X₀, hX₀3, hX₀⟩ := hCc₀ Cc hCc
  refine ⟨X₀, hX₀3, ?_⟩
  intro X hX p _ hp hpX reserve hr0 hr hH heta hqQ hbeta hfar hXp
  simpa [activeCertificateHighSlot] using
    hX₀ X hX p hp hpX reserve hr0 hr hH heta hqQ hbeta hfar hXp

/-- Active-certificate high `/5` slot from the adopted `/30`. Not the old
`T = X` constructor mixed-total slot. -/
theorem exists_active_certificate_high_fifth
    (delta A : ℝ) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 240) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
          ∀ (p : Corollary53Input) [NeZero p.q]
            (hp : Corollary53Admissible 1 1 p) (hpX : p.X = X)
            (reserve : ℝ) (hr0 : 0 ≤ reserve) (hr : reserve ≤ 1 / 1200)
            (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
            (heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B))
            (hqQ : (p.q : ℝ) ≤ (Real.log p.X) ^ B)
            (hbeta : |p.beta| ≤ 1 / ((p.q : ℝ) * (Real.log p.X) ^ B))
            (hfar : 2 * (Real.log p.X) ^ Cc < stationaryWidth p.beta p.H)
            (hXp : 2 ≤ p.X),
            activeCertificateHighSlot p delta hXp hdelta ≤
              p.X * Real.rpow (Real.log p.X) (-A) / 5 := by
  obtain ⟨B₀, hB₀⟩ :=
    exists_active_high_budget_fifth delta A hdelta hdeltaUpper
  refine ⟨B₀, ?_⟩
  intro B hB
  obtain ⟨Cc₀, hCc₀⟩ := hB₀ B hB
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc
  obtain ⟨X₀, hX₀3, hX₀⟩ := hCc₀ Cc hCc
  refine ⟨X₀, hX₀3, ?_⟩
  intro X hX p _ hp hpX reserve hr0 hr hH heta hqQ hbeta hfar hXp
  simpa [activeCertificateHighSlot] using
    hX₀ X hX p hp hpX reserve hr0 hr hH heta hqQ hbeta hfar hXp

/-- Mixed-only half of the same slot; sharp-max errors are nonnegative. -/
theorem exists_active_certificate_mixed_fifth
    (delta A : ℝ) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 240) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
          ∀ (p : Corollary53Input) [NeZero p.q]
            (hp : Corollary53Admissible 1 1 p) (hpX : p.X = X)
            (reserve : ℝ) (hr0 : 0 ≤ reserve) (hr : reserve ≤ 1 / 1200)
            (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
            (heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B))
            (hqQ : (p.q : ℝ) ≤ (Real.log p.X) ^ B)
            (hbeta : |p.beta| ≤ 1 / ((p.q : ℝ) * (Real.log p.X) ^ B))
            (hfar : 2 * (Real.log p.X) ^ Cc < stationaryWidth p.beta p.H)
            (hXp : 2 ≤ p.X),
            dynamicLowNormalizationV3 p *
              activeIndexedMixedTotal
                (H₀ := highClassifierH0 p.X delta)
                (selectedHighTruncation p) hXp hdelta ≤
              p.X * Real.rpow (Real.log p.X) (-A) / 5 := by
  obtain ⟨B₀, hB₀⟩ :=
    eventually_refined_high_mixed_le_thirtieth delta A hdelta hdeltaUpper
  refine ⟨B₀, ?_⟩
  intro B hB
  obtain ⟨Cc₀, hCc₀⟩ := hB₀ B hB
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp (hCc₀ Cc hCc)
  refine ⟨max 3 X₀, le_max_left _ _, ?_⟩
  intro X hX p _ hp hpX reserve hr0 hr hH heta hqQ hbeta hfar hXp
  have h30 :=
    hX₀ X ((le_max_right 3 X₀).trans hX) p hp hpX reserve hr0 hr hH heta
      hqQ hbeta hfar hXp
  have hX0 : 0 ≤ p.X := by linarith
  have hX1 : (1 : ℝ) < p.X := by linarith
  have hlog : 0 < Real.log p.X := Real.log_pos hX1
  have hrpow : 0 ≤ Real.rpow (Real.log p.X) (-A) :=
    Real.rpow_nonneg hlog.le _
  exact h30.trans (thirtieth_scalar_le_fifth hX0 hrpow)

end
end MRTProposition61HighAdoptedThirtiethV3

#print axioms MRTProposition61HighAdoptedThirtiethV3.adopted_expanded_core_splits_high

#print axioms MRTProposition61HighAdoptedThirtiethV3.expandedRHS_active_selected_eq

#print axioms MRTProposition61HighAdoptedThirtiethV3.active_expanded_rhs_le_of_high_fifth

#print axioms MRTProposition61HighAdoptedThirtiethV3.exists_adopted_high_budget_thirtieth

#print axioms MRTProposition61HighAdoptedThirtiethV3.exists_active_certificate_high_fifth

#print axioms MRTProposition61HighAdoptedThirtiethV3.exists_active_certificate_mixed_fifth
