import MAPFinishDynamicLowTypes
import MAPDynamicHBSourcePacketBoundRefinedV3

/-! # Genuine low types with the refined fixed low weight -/

namespace MAPFinishDynamicLowTypesRefinedV3

set_option maxHeartbeats 1000000

open scoped BigOperators
open MAPMRTCorollary25Instantiation MAPMRTCorollary53Source
open MAPHBPerronSourceData
open MRTLemma215DynamicClassificationV3
open MRTLemma215DynamicPacketSourceBoundV3
open MAPDynamicHBSourcePacketBoundRefinedV3
open MAPFinishDynamicLowTypes
open MAPDynamicHBSourceV3
open MRTLemma215HBExpansion

noncomputable section

def dynamicBranchGenuineLowMassRefinedV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) : ℝ :=
  dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
    ∑ kind ∈ genuineLowKinds,
      componentIntegral p.X p.H 1 p.q
        (dynamicRawBranchRemainderCoeffV3 p.X delta H₀ branch kind)
        p.beta p.eta component

def dynamicBranchTypeIIMassRefinedV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) : ℝ :=
  dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
    componentIntegral p.X p.H 1 p.q
      (dynamicRawBranchRemainderCoeffV3 p.X delta H₀ branch .typeII)
      p.beta p.eta component

def dynamicBranchD12MassRefinedV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) : ℝ :=
  dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
    (componentIntegral p.X p.H 1 p.q
        (dynamicRawBranchRemainderCoeffV3 p.X delta H₀ branch .typeD1)
        p.beta p.eta component +
      componentIntegral p.X p.H 1 p.q
        (dynamicRawBranchRemainderCoeffV3 p.X delta H₀ branch .typeD2)
        p.beta p.eta component)

def dynamicAllGenuineLowMassRefinedV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) : ℝ :=
  ∑ branch : Fin (hbOrder delta),
    dynamicBranchGenuineLowMassRefinedV3
      p delta H₀ hX hdelta component branch

def dynamicAllTypeIIMassRefinedV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) : ℝ :=
  ∑ branch : Fin (hbOrder delta),
    dynamicBranchTypeIIMassRefinedV3
      p delta H₀ hX hdelta component branch

def dynamicAllD12MassRefinedV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) : ℝ :=
  ∑ branch : Fin (hbOrder delta),
    dynamicBranchD12MassRefinedV3
      p delta H₀ hX hdelta component branch

theorem dynamicBranchGenuineLowMassRefined_eq_typeII_add_d12
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) :
    dynamicBranchGenuineLowMassRefinedV3
        p delta H₀ hX hdelta component branch =
      dynamicBranchTypeIIMassRefinedV3
          p delta H₀ hX hdelta component branch +
        dynamicBranchD12MassRefinedV3
          p delta H₀ hX hdelta component branch := by
  unfold dynamicBranchGenuineLowMassRefinedV3
    dynamicBranchTypeIIMassRefinedV3 dynamicBranchD12MassRefinedV3
    genuineLowKinds
  simp
  ring

theorem dynamicAllGenuineLowMassRefined_eq_typeII_add_d12
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) :
    dynamicAllGenuineLowMassRefinedV3 p delta H₀ hX hdelta component =
      dynamicAllTypeIIMassRefinedV3 p delta H₀ hX hdelta component +
        dynamicAllD12MassRefinedV3 p delta H₀ hX hdelta component := by
  unfold dynamicAllGenuineLowMassRefinedV3
    dynamicAllTypeIIMassRefinedV3 dynamicAllD12MassRefinedV3
  simp_rw [dynamicBranchGenuineLowMassRefined_eq_typeII_add_d12]
  exact Finset.sum_add_distrib

theorem dynamicBranchLowMassRefined_le_three_genuine
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    {delta H₀ : ℝ} (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) :
    dynamicBranchLowMassRefinedV3 p delta H₀ hX hdelta component branch ≤
      3 * dynamicBranchGenuineLowMassRefinedV3
        p delta H₀ hX hdelta component branch := by
  rcases hp with ⟨hHone, hHX, _, _, heta, hetaOne, _⟩
  unfold dynamicBranchLowMassRefinedV3 dynamicBranchGenuineLowMassRefinedV3
  rw [dynamicBranchCombinedRemainderCoeffV3_eq_genuine_sum]
  have hcomponent := componentIntegral_finset_sum_le genuineLowKinds
    (fun kind => dynamicRawBranchRemainderCoeffV3
      p.X delta H₀ branch kind)
    (X := p.X) (H := p.H) (beta := p.beta) (q₀ := 1) (q₁ := p.q)
    (by linarith [hHone, hHX]) (by linarith [hHone]) heta hetaOne component
  have hcard : (genuineLowKinds.card : ℝ) = 3 := by
    have hcardNat : genuineLowKinds.card = 3 := by decide
    exact_mod_cast hcardNat
  rw [hcard] at hcomponent
  have hweight : 0 ≤ dynamicBranchLowWeightRefinedV3
      (K := hbOrder delta) := by
    unfold dynamicBranchLowWeightRefinedV3
    positivity
  have hmul := mul_le_mul_of_nonneg_left hcomponent
    hweight
  calc
    dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
        componentIntegral p.X p.H 1 p.q
          (fun n => ∑ kind ∈ genuineLowKinds,
            dynamicRawBranchRemainderCoeffV3 p.X delta H₀ branch kind n)
          p.beta p.eta component ≤
      dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
        (3 * ∑ kind ∈ genuineLowKinds,
          componentIntegral p.X p.H 1 p.q
            (dynamicRawBranchRemainderCoeffV3 p.X delta H₀ branch kind)
            p.beta p.eta component) := hmul
    _ = 3 * (dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
        ∑ kind ∈ genuineLowKinds,
          componentIntegral p.X p.H 1 p.q
            (dynamicRawBranchRemainderCoeffV3 p.X delta H₀ branch kind)
            p.beta p.eta component) := by ring

theorem dynamicAllLowMassRefined_le_three_genuine
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    {delta H₀ : ℝ} (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) :
    dynamicAllLowMassRefinedV3 p delta H₀ hX hdelta component ≤
      3 * dynamicAllGenuineLowMassRefinedV3
        p delta H₀ hX hdelta component := by
  unfold dynamicAllLowMassRefinedV3 dynamicAllGenuineLowMassRefinedV3
  calc
    (∑ branch : Fin (hbOrder delta),
      dynamicBranchLowMassRefinedV3
        p delta H₀ hX hdelta component branch) ≤
      ∑ branch : Fin (hbOrder delta),
        3 * dynamicBranchGenuineLowMassRefinedV3
          p delta H₀ hX hdelta component branch := by
        exact Finset.sum_le_sum fun branch hbranch =>
          dynamicBranchLowMassRefined_le_three_genuine
            hp hX hdelta component branch
    _ = 3 * ∑ branch : Fin (hbOrder delta),
        dynamicBranchGenuineLowMassRefinedV3
          p delta H₀ hX hdelta component branch := by rw [Finset.mul_sum]

theorem dynamicV3_refined_low_types_of_typeII_and_d12_budgets
    {p : Corollary53Input} [NeZero p.q]
    (hp : Corollary53Admissible 1 1 p)
    {delta H₀ budget : ℝ} (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (htypeII : dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent,
          dynamicAllTypeIIMassRefinedV3 p delta H₀ hX hdelta component) ≤
      budget / 30)
    (hd12 : dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent,
          dynamicAllD12MassRefinedV3 p delta H₀ hX hdelta component) ≤
      budget / 30) :
    dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent,
          dynamicAllLowMassRefinedV3 p delta H₀ hX hdelta component) ≤
      budget / 5 := by
  have hall : (∑ component : OuterComponent,
      dynamicAllLowMassRefinedV3 p delta H₀ hX hdelta component) ≤
      3 * ∑ component : OuterComponent,
        dynamicAllGenuineLowMassRefinedV3
          p delta H₀ hX hdelta component := by
    calc
      _ ≤ ∑ component : OuterComponent,
          3 * dynamicAllGenuineLowMassRefinedV3
            p delta H₀ hX hdelta component := by
        exact Finset.sum_le_sum fun component hcomponent =>
          dynamicAllLowMassRefined_le_three_genuine hp hX hdelta component
      _ = _ := by rw [Finset.mul_sum]
  have hnorm : 0 ≤ dynamicLowNormalizationV3 p := by
    unfold dynamicLowNormalizationV3
    positivity
  have hmul := mul_le_mul_of_nonneg_left hall hnorm
  have hsum : dynamicLowNormalizationV3 p *
      (∑ component : OuterComponent,
        dynamicAllGenuineLowMassRefinedV3
          p delta H₀ hX hdelta component) ≤ budget / 15 := by
    simp_rw [dynamicAllGenuineLowMassRefined_eq_typeII_add_d12,
      Finset.sum_add_distrib]
    rw [mul_add]
    linarith
  calc
    _ ≤ dynamicLowNormalizationV3 p *
        (3 * ∑ component : OuterComponent,
          dynamicAllGenuineLowMassRefinedV3
            p delta H₀ hX hdelta component) := hmul
    _ = 3 * (dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent,
          dynamicAllGenuineLowMassRefinedV3
            p delta H₀ hX hdelta component)) := by ring
    _ ≤ 3 * (budget / 15) := by gcongr
    _ = budget / 5 := by ring

end
end MAPFinishDynamicLowTypesRefinedV3

#print axioms MAPFinishDynamicLowTypesRefinedV3.dynamicAllLowMassRefined_le_three_genuine
#print axioms MAPFinishDynamicLowTypesRefinedV3.dynamicV3_refined_low_types_of_typeII_and_d12_budgets
