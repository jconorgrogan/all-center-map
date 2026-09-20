import MAPDynamicHBSourceDecompositionV3
import MRTLemma215DynamicCoefficientBoundsV3
import HBPerronPacketIndexedSourceV2

/-!
# Literal dynamic MRT classifier

This module partitions every exact preliminary component of the
arbitrary-order Heath--Brown source.  Type-II, Type-d1, and Type-d2 remain
separate remainders; Type-dj for `j >= 3` is the high packet source; both
vanishing alternatives are proved zero.  No raw HB index is identified with
a final Type label.
-/

namespace MRTLemma215DynamicClassificationV3

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPHBPerronSourceData HBPerronPacketIndexedSourceV2
open MAPDynamicHBSourceV3 MRTLemma215DynamicPreliminaryV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215ScaleClassifierV3
open MRTLemma215DynamicOutcomeWeldV3

noncomputable section

private theorem sum_univ_finset_finset_univ_comm
    {A B C D : Type*} [Fintype A] [Fintype D]
    [DecidableEq B] [DecidableEq C]
    (SB : Finset B) (SC : Finset C) (F : A → B → C → D → ℂ) :
    (∑ a : A, ∑ b ∈ SB, ∑ c ∈ SC, ∑ d : D, F a b c d) =
      ∑ d : D, ∑ a : A, ∑ b ∈ SB, ∑ c ∈ SC, F a b c d := by
  calc
    (∑ a : A, ∑ b ∈ SB, ∑ c ∈ SC, ∑ d : D, F a b c d) =
        ∑ a : A, ∑ b ∈ SB, ∑ d : D, ∑ c ∈ SC, F a b c d := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = ∑ a : A, ∑ d : D, ∑ b ∈ SB, ∑ c ∈ SC, F a b c d := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ d : D, ∑ a : A, ∑ b ∈ SB, ∑ c ∈ SC, F a b c d := by
      exact Finset.sum_comm

def maskedDynamicComponentV3
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (n : ℕ) : ℂ :=
  if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then
    dynamicPreliminaryComponent (some logIndex) zbag mbag n else 0

/-- Low-type piece of one literal preliminary component. -/
def dynamicComponentRemainderV3
    {X delta H₀ : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (kind : HBRemainderKind) (n : ℕ) : ℂ :=
  match dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag with
  | .typeII => if kind = .typeII then
      maskedDynamicComponentV3 logIndex zbag mbag n else 0
  | .typeD j =>
      if (j : ℕ) = 1 then
        if kind = .typeD1 then
          maskedDynamicComponentV3 logIndex zbag mbag n else 0
      else if (j : ℕ) = 2 then
        if kind = .typeD2 then
          maskedDynamicComponentV3 logIndex zbag mbag n else 0
      else 0
  | .vanishing => 0

/-- High Type-dj (`j >= 3`) piece of one preliminary component. -/
def dynamicComponentHighV3
    {X delta H₀ : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (n : ℕ) : ℂ :=
  match dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag with
  | .typeD j => if 3 ≤ (j : ℕ) then
      maskedDynamicComponentV3 logIndex zbag mbag n else 0
  | _ => 0

/-- Exact one-component classifier weld. -/
theorem maskedDynamicComponentV3_eq_remainders_add_high
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K k : ℕ} (hK : 1 ≤ K)
    (hgeom : Real.rpow X delta *
        (2 * Real.rpow X ((8 : ℝ)⁻¹)) ≤ 2 * H₀)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (hsize : (2 : ℝ) ^
        (dynamicComponentFactorList logIndex zbag mbag).length *
          Real.rpow X delta ≤ X)
    (n : ℕ) :
    maskedDynamicComponentV3 logIndex zbag mbag n =
      (∑ kind : HBRemainderKind,
        dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
          logIndex zbag mbag kind n) +
      dynamicComponentHighV3 (delta := delta) (H₀ := H₀)
        logIndex zbag mbag n := by
  cases houtcome : dynamicComponentOutcome 8 delta H₀
      logIndex zbag mbag with
  | typeII =>
      simp [dynamicComponentRemainderV3, dynamicComponentHighV3, houtcome]
  | vanishing =>
      have hzero :=
        maskedDynamicPreliminaryComponent_eq_zero_of_outcome_vanishing
          hX hdelta hK (by norm_num) hgeom logIndex zbag mbag hsize
          houtcome n
      change maskedDynamicComponentV3 logIndex zbag mbag n = _
      have hzero' : maskedDynamicComponentV3 logIndex zbag mbag n = 0 := by
        simpa [maskedDynamicComponentV3] using hzero
      rw [hzero']
      simp [dynamicComponentRemainderV3, dynamicComponentHighV3, houtcome]
  | typeD j =>
      have hdata := typeD_outcome_data logIndex zbag mbag j houtcome
      have hjone : 1 ≤ (j : ℕ) := hdata.2.2.2
      by_cases hj1 : (j : ℕ) = 1
      · simp [dynamicComponentRemainderV3, dynamicComponentHighV3,
          houtcome, hj1]
      · by_cases hj2 : (j : ℕ) = 2
        · simp [dynamicComponentRemainderV3, dynamicComponentHighV3,
            houtcome, hj1, hj2]
        · have hj3 : 3 ≤ (j : ℕ) := by omega
          simp [dynamicComponentRemainderV3, dynamicComponentHighV3,
            houtcome, hj1, hj2, hj3]

/-- Exact flattened component expansion of one raw dynamic HB branch. -/
theorem dynamicHBBranchCoeff_eq_sum_maskedDynamicComponentsV3
    {X : ℝ} (hX : 1 ≤ X) {K : ℕ} (hK : 1 ≤ K)
    (branch : Fin K) (n : ℕ) :
    dynamicHBBranchCoeff X K branch n =
      ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)),
        ∑ zbag ∈ (Finset.univ : Finset
            (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))).sym
              (branch : ℕ),
          ∑ mbag ∈ (Finset.univ : Finset
              (Option (Fin (sourceDyadicCount
                ⌊dynamicHBCutoff X K⌋₊)))).sym ((branch : ℕ) + 1),
            maskedDynamicComponentV3 logIndex zbag mbag n := by
  rw [dynamicHBBranchCoeff_eq_maskedFactorizedPreliminarySum hX hK]
  unfold maskedDynamicFactorizedPreliminarySum
    dynamicFactorizedPreliminarySum maskedDynamicComponentV3
  by_cases hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊
  · rw [if_pos hn]
    simp_rw [if_pos hn]
    simp_rw [arithmeticFunction_finsetSum_apply]
    apply Finset.sum_congr rfl
    intro logIndex hlog
    apply Finset.sum_congr rfl
    intro zbag hz
    apply Finset.sum_congr rfl
    intro mbag hm
    have hcomponent := dynamicPreliminaryComponent_some_eq_factorConvolution
      hX hK logIndex zbag mbag
    exact congrArg (fun F : ArithmeticFunction ℂ => F n) hcomponent |>.symm
  · rw [if_neg hn]
    simp_rw [if_neg hn]
    simp

/-- Aggregate low remainder of one raw dynamic HB branch. -/
def dynamicRawBranchRemainderCoeffV3
    (X delta H₀ : ℝ) {K : ℕ} (branch : Fin K)
    (kind : HBRemainderKind) (n : ℕ) : ℂ :=
  ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)),
    ∑ zbag ∈ (Finset.univ : Finset
        (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))).sym
          (branch : ℕ),
      ∑ mbag ∈ (Finset.univ : Finset
          (Option (Fin (sourceDyadicCount
            ⌊dynamicHBCutoff X K⌋₊)))).sym ((branch : ℕ) + 1),
        dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
          logIndex zbag mbag kind n

/-- Aggregate high coefficient of one raw dynamic HB branch. -/
def dynamicRawBranchHighCoeffV3
    (X delta H₀ : ℝ) {K : ℕ} (branch : Fin K) (n : ℕ) : ℂ :=
  ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)),
    ∑ zbag ∈ (Finset.univ : Finset
        (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))).sym
          (branch : ℕ),
      ∑ mbag ∈ (Finset.univ : Finset
          (Option (Fin (sourceDyadicCount
            ⌊dynamicHBCutoff X K⌋₊)))).sym ((branch : ℕ) + 1),
        dynamicComponentHighV3 (delta := delta) (H₀ := H₀)
          logIndex zbag mbag n

/-- Every raw branch is exactly the sum of its three genuine low types and
its high Type-dj family.  The unit/small remainder slots are literally zero
for this exact finite decomposition. -/
theorem dynamicHBBranchCoeff_eq_remainders_add_highV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (hK : 1 ≤ K)
    (hgeom : Real.rpow X delta *
        (2 * Real.rpow X ((8 : ℝ)⁻¹)) ≤ 2 * H₀)
    (hsize : ∀ (branch : Fin K)
      (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
      (zbag : Sym (Option
        (Fin (sourceDyadicCount (hbFactorCutoff X)))) (branch : ℕ))
      (mbag : Sym (Option (Fin (sourceDyadicCount
        ⌊dynamicHBCutoff X K⌋₊))) ((branch : ℕ) + 1)),
      (2 : ℝ) ^ (dynamicComponentFactorList logIndex zbag mbag).length *
        Real.rpow X delta ≤ X)
    (branch : Fin K) (n : ℕ) :
    dynamicHBBranchCoeff X K branch n =
      (∑ kind : HBRemainderKind,
        dynamicRawBranchRemainderCoeffV3 X delta H₀ branch kind n) +
      dynamicRawBranchHighCoeffV3 X delta H₀ branch n := by
  rw [dynamicHBBranchCoeff_eq_sum_maskedDynamicComponentsV3
    (by linarith) hK]
  unfold dynamicRawBranchRemainderCoeffV3 dynamicRawBranchHighCoeffV3
  simp_rw [maskedDynamicComponentV3_eq_remainders_add_high
    hX hdelta hK hgeom _ _ _ (hsize branch _ _ _)]
  simp_rw [Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · exact sum_univ_finset_finset_univ_comm _ _ _
  · rfl

end
end MRTLemma215DynamicClassificationV3

#print axioms MRTLemma215DynamicClassificationV3.maskedDynamicComponentV3_eq_remainders_add_high
#print axioms MRTLemma215DynamicClassificationV3.dynamicHBBranchCoeff_eq_sum_maskedDynamicComponentsV3
#print axioms MRTLemma215DynamicClassificationV3.dynamicHBBranchCoeff_eq_remainders_add_highV3
