import MAPDynamicHBScaledPacketSourceV3

/-!
# Exact reduction of the dynamic low mass to its three genuine types

The dynamic classifier retains the five-slot legacy `HBRemainderKind`, but its
literal source only populates Type II, Type d1, and Type d2.  This file removes
the two identically-zero slots before any analytic low-type estimate is used.
-/

namespace MAPFinishDynamicLowTypes

set_option maxHeartbeats 1200000

open scoped BigOperators
open MAPMRTCorollary25Instantiation MAPMRTCorollary53Source
open MAPHBPerronSourceData
open HBPerronPacketIndexedSourceV2
open MRTLemma215DynamicClassificationV3
open MRTLemma215DynamicPacketSourceBoundV3
open MAPDynamicHBSourcePacketBoundV3 MAPDynamicHBScaledPacketSourceV3
open MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3

noncomputable section

def genuineLowKinds : Finset HBRemainderKind :=
  {.typeII, .typeD1, .typeD2}

theorem dynamicComponentRemainderV3_unitScale_eq_zero
    {X delta H₀ : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (n : ℕ) :
    dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
        logIndex zbag mbag .unitScale n = 0 := by
  unfold dynamicComponentRemainderV3
  split <;> simp_all

theorem dynamicComponentRemainderV3_smallTerm_eq_zero
    {X delta H₀ : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (n : ℕ) :
    dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
        logIndex zbag mbag .smallTerm n = 0 := by
  unfold dynamicComponentRemainderV3
  split <;> simp_all

theorem dynamicRawBranchRemainderCoeffV3_unitScale_eq_zero
    (X delta H₀ : ℝ) {K : ℕ} (branch : Fin K) :
    dynamicRawBranchRemainderCoeffV3 X delta H₀ branch .unitScale = 0 := by
  funext n
  unfold dynamicRawBranchRemainderCoeffV3
  simp_rw [dynamicComponentRemainderV3_unitScale_eq_zero]
  simp

theorem dynamicRawBranchRemainderCoeffV3_smallTerm_eq_zero
    (X delta H₀ : ℝ) {K : ℕ} (branch : Fin K) :
    dynamicRawBranchRemainderCoeffV3 X delta H₀ branch .smallTerm = 0 := by
  funext n
  unfold dynamicRawBranchRemainderCoeffV3
  simp_rw [dynamicComponentRemainderV3_smallTerm_eq_zero]
  simp

theorem dynamicBranchCombinedRemainderCoeffV3_eq_genuine_sum
    (X delta H₀ : ℝ) {K : ℕ} (branch : Fin K) :
    dynamicBranchCombinedRemainderCoeffV3 X delta H₀ branch =
      fun n => ∑ kind ∈ genuineLowKinds,
        dynamicRawBranchRemainderCoeffV3 X delta H₀ branch kind n := by
  funext n
  unfold dynamicBranchCombinedRemainderCoeffV3 genuineLowKinds
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro kind hkind hnot
  fin_cases kind <;> simp_all
  · exact congrFun
      (dynamicRawBranchRemainderCoeffV3_unitScale_eq_zero
        X delta H₀ branch) n
  · exact congrFun
      (dynamicRawBranchRemainderCoeffV3_smallTerm_eq_zero
        X delta H₀ branch) n

/-- The literal branch mass after deleting the two identically-zero legacy
slots. -/
def dynamicBranchGenuineLowMassV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) : ℝ :=
  dynamicBranchPacketWeightV3 (H₀ := H₀) hX hdelta branch *
    ∑ kind ∈ genuineLowKinds,
      componentIntegral p.X p.H 1 p.q
        (dynamicRawBranchRemainderCoeffV3 p.X delta H₀ branch kind)
        p.beta p.eta component

def dynamicAllGenuineLowMassV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) : ℝ :=
  ∑ branch : Fin (hbOrder delta),
    dynamicBranchGenuineLowMassV3 p delta H₀ hX hdelta component branch

/-- The Type-II part of one dynamic branch, separated before invoking the
premise-free Lemma 2.10 estimates. -/
def dynamicBranchTypeIIMassV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) : ℝ :=
  dynamicBranchPacketWeightV3 (H₀ := H₀) hX hdelta branch *
    componentIntegral p.X p.H 1 p.q
      (dynamicRawBranchRemainderCoeffV3 p.X delta H₀ branch .typeII)
      p.beta p.eta component

/-- The two low Type-d branches.  These, unlike Type II, are exactly where
the shared Ramachandra/Corollary-2.12 fourth moment enters. -/
def dynamicBranchD12MassV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) : ℝ :=
  dynamicBranchPacketWeightV3 (H₀ := H₀) hX hdelta branch *
    (componentIntegral p.X p.H 1 p.q
        (dynamicRawBranchRemainderCoeffV3 p.X delta H₀ branch .typeD1)
        p.beta p.eta component +
      componentIntegral p.X p.H 1 p.q
        (dynamicRawBranchRemainderCoeffV3 p.X delta H₀ branch .typeD2)
        p.beta p.eta component)

def dynamicAllTypeIIMassV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) : ℝ :=
  ∑ branch : Fin (hbOrder delta),
    dynamicBranchTypeIIMassV3 p delta H₀ hX hdelta component branch

def dynamicAllD12MassV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) : ℝ :=
  ∑ branch : Fin (hbOrder delta),
    dynamicBranchD12MassV3 p delta H₀ hX hdelta component branch

theorem dynamicBranchGenuineLowMassV3_eq_typeII_add_d12
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) :
    dynamicBranchGenuineLowMassV3 p delta H₀ hX hdelta component branch =
      dynamicBranchTypeIIMassV3 p delta H₀ hX hdelta component branch +
        dynamicBranchD12MassV3 p delta H₀ hX hdelta component branch := by
  unfold dynamicBranchGenuineLowMassV3 dynamicBranchTypeIIMassV3
    dynamicBranchD12MassV3 genuineLowKinds
  simp
  ring

theorem dynamicAllGenuineLowMassV3_eq_typeII_add_d12
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) :
    dynamicAllGenuineLowMassV3 p delta H₀ hX hdelta component =
      dynamicAllTypeIIMassV3 p delta H₀ hX hdelta component +
        dynamicAllD12MassV3 p delta H₀ hX hdelta component := by
  unfold dynamicAllGenuineLowMassV3 dynamicAllTypeIIMassV3
    dynamicAllD12MassV3
  simp_rw [dynamicBranchGenuineLowMassV3_eq_typeII_add_d12]
  exact Finset.sum_add_distrib

/-- The exact normalization occurring in `DynamicV3TermwiseBudget.low_types`,
repeated here so the low-type source reduction does not import the unrelated
high-packet/Perron budget dependency chain. -/
def dynamicLowNormalizationV3 (p : Corollary53Input) : ℝ :=
  (divisorCount p.q : ℝ) ^ 4 /
    (p.q * stationaryWidth p.beta p.H ^ 2)

theorem dynamicBranchLowMassV3_le_three_genuine
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    {delta H₀ : ℝ} (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) :
    dynamicBranchLowMassV3 p delta H₀ hX hdelta component branch ≤
      3 * dynamicBranchGenuineLowMassV3
        p delta H₀ hX hdelta component branch := by
  rcases hp with ⟨hHone, hHX, _, _, heta, hetaOne, _⟩
  unfold dynamicBranchLowMassV3 dynamicBranchGenuineLowMassV3
  rw [dynamicBranchCombinedRemainderCoeffV3_eq_genuine_sum]
  have hcomponent := componentIntegral_finset_sum_le
    genuineLowKinds
    (fun kind => dynamicRawBranchRemainderCoeffV3
      p.X delta H₀ branch kind)
    (X := p.X) (H := p.H) (beta := p.beta) (q₀ := 1) (q₁ := p.q)
    (by linarith [hHone, hHX]) (by linarith [hHone]) heta hetaOne component
  have hcard : (genuineLowKinds.card : ℝ) = 3 := by
    have hcardNat : genuineLowKinds.card = 3 := by decide
    exact_mod_cast hcardNat
  rw [hcard] at hcomponent
  have hmul := mul_le_mul_of_nonneg_left hcomponent
    (dynamicBranchPacketWeightV3_nonneg (H₀ := H₀) hX hdelta branch)
  calc
    dynamicBranchPacketWeightV3 (H₀ := H₀) hX hdelta branch *
        componentIntegral p.X p.H 1 p.q
          (fun n => ∑ kind ∈ genuineLowKinds,
            dynamicRawBranchRemainderCoeffV3 p.X delta H₀ branch kind n)
          p.beta p.eta component ≤
      dynamicBranchPacketWeightV3 (H₀ := H₀) hX hdelta branch *
        (3 * ∑ kind ∈ genuineLowKinds,
          componentIntegral p.X p.H 1 p.q
            (dynamicRawBranchRemainderCoeffV3 p.X delta H₀ branch kind)
            p.beta p.eta component) := hmul
    _ = 3 * (dynamicBranchPacketWeightV3 (H₀ := H₀) hX hdelta branch *
        ∑ kind ∈ genuineLowKinds,
          componentIntegral p.X p.H 1 p.q
            (dynamicRawBranchRemainderCoeffV3 p.X delta H₀ branch kind)
            p.beta p.eta component) := by ring

theorem dynamicAllLowMassV3_le_three_genuine
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    {delta H₀ : ℝ} (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) :
    dynamicAllLowMassV3 p delta H₀ hX hdelta component ≤
      3 * dynamicAllGenuineLowMassV3 p delta H₀ hX hdelta component := by
  unfold dynamicAllLowMassV3 dynamicAllGenuineLowMassV3
  calc
    (∑ branch : Fin (hbOrder delta),
      dynamicBranchLowMassV3 p delta H₀ hX hdelta component branch) ≤
        ∑ branch : Fin (hbOrder delta),
          3 * dynamicBranchGenuineLowMassV3
            p delta H₀ hX hdelta component branch := by
      exact Finset.sum_le_sum fun branch hbranch =>
        dynamicBranchLowMassV3_le_three_genuine
          hp hX hdelta component branch
    _ = 3 * ∑ branch : Fin (hbOrder delta),
        dynamicBranchGenuineLowMassV3
          p delta H₀ hX hdelta component branch := by
      rw [Finset.mul_sum]

theorem dynamicV3_low_types_of_genuine_three_type_budget
    {p : Corollary53Input} [NeZero p.q]
    (hp : Corollary53Admissible 1 1 p)
    {delta H₀ budget : ℝ} (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hgenuine : dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent,
          dynamicAllGenuineLowMassV3 p delta H₀ hX hdelta component) ≤
      budget / 15) :
    dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent,
          dynamicAllLowMassV3 p delta H₀ hX hdelta component) ≤
      budget / 5 := by
  have hall : (∑ component : OuterComponent,
      dynamicAllLowMassV3 p delta H₀ hX hdelta component) ≤
      3 * ∑ component : OuterComponent,
        dynamicAllGenuineLowMassV3 p delta H₀ hX hdelta component := by
    calc
      (∑ component : OuterComponent,
        dynamicAllLowMassV3 p delta H₀ hX hdelta component) ≤
          ∑ component : OuterComponent,
            3 * dynamicAllGenuineLowMassV3
              p delta H₀ hX hdelta component := by
        exact Finset.sum_le_sum fun component hcomponent =>
          dynamicAllLowMassV3_le_three_genuine hp hX hdelta component
      _ = 3 * ∑ component : OuterComponent,
          dynamicAllGenuineLowMassV3 p delta H₀ hX hdelta component := by
        rw [Finset.mul_sum]
  have hnorm : 0 ≤ dynamicLowNormalizationV3 p := by
    unfold dynamicLowNormalizationV3
    positivity
  have hmul := mul_le_mul_of_nonneg_left hall hnorm
  calc
    dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent,
          dynamicAllLowMassV3 p delta H₀ hX hdelta component) ≤
      dynamicLowNormalizationV3 p *
        (3 * ∑ component : OuterComponent,
          dynamicAllGenuineLowMassV3 p delta H₀ hX hdelta component) := hmul
    _ = 3 * (dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent,
          dynamicAllGenuineLowMassV3 p delta H₀ hX hdelta component)) := by ring
    _ ≤ 3 * (budget / 15) := by linarith
    _ = budget / 5 := by ring

/-- Exact public constructor after separating the unconditional Type-II route
from the shared-AFE Type-d route.  The constants allocate `/30` to each side;
the existing factor-three collection loss then gives the required `/5` low
slot of `DynamicV3TermwiseBudget`. -/
theorem dynamicV3_low_types_of_typeII_and_d12_budgets
    {p : Corollary53Input} [NeZero p.q]
    (hp : Corollary53Admissible 1 1 p)
    {delta H₀ budget : ℝ} (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (htypeII : dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent,
          dynamicAllTypeIIMassV3 p delta H₀ hX hdelta component) ≤
      budget / 30)
    (hd12 : dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent,
          dynamicAllD12MassV3 p delta H₀ hX hdelta component) ≤
      budget / 30) :
    dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent,
          dynamicAllLowMassV3 p delta H₀ hX hdelta component) ≤
      budget / 5 := by
  apply dynamicV3_low_types_of_genuine_three_type_budget hp hX hdelta
  simp_rw [dynamicAllGenuineLowMassV3_eq_typeII_add_d12,
    Finset.sum_add_distrib]
  have hdistrib : dynamicLowNormalizationV3 p *
      ((∑ component : OuterComponent,
          dynamicAllTypeIIMassV3 p delta H₀ hX hdelta component) +
        ∑ component : OuterComponent,
          dynamicAllD12MassV3 p delta H₀ hX hdelta component) =
      dynamicLowNormalizationV3 p *
          (∑ component : OuterComponent,
            dynamicAllTypeIIMassV3 p delta H₀ hX hdelta component) +
        dynamicLowNormalizationV3 p *
          (∑ component : OuterComponent,
            dynamicAllD12MassV3 p delta H₀ hX hdelta component) := by ring
  rw [hdistrib]
  linarith

end
end MAPFinishDynamicLowTypes

#print axioms MAPFinishDynamicLowTypes.dynamicComponentRemainderV3_unitScale_eq_zero
#print axioms MAPFinishDynamicLowTypes.dynamicComponentRemainderV3_smallTerm_eq_zero
#print axioms MAPFinishDynamicLowTypes.dynamicRawBranchRemainderCoeffV3_unitScale_eq_zero
#print axioms MAPFinishDynamicLowTypes.dynamicRawBranchRemainderCoeffV3_smallTerm_eq_zero
#print axioms MAPFinishDynamicLowTypes.dynamicBranchCombinedRemainderCoeffV3_eq_genuine_sum
#print axioms MAPFinishDynamicLowTypes.dynamicBranchLowMassV3_le_three_genuine
#print axioms MAPFinishDynamicLowTypes.dynamicAllLowMassV3_le_three_genuine
#print axioms MAPFinishDynamicLowTypes.dynamicV3_low_types_of_genuine_three_type_budget
#print axioms MAPFinishDynamicLowTypes.dynamicAllGenuineLowMassV3_eq_typeII_add_d12
#print axioms MAPFinishDynamicLowTypes.dynamicV3_low_types_of_typeII_and_d12_budgets
