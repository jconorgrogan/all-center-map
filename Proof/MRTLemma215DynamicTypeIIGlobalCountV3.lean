import MRTLemma215DynamicMultiplicityBoundsV3
import MRTLemma215DynamicTypeIIFiniteEnvelopeV3
import MRTProposition61TypeIIGlobalFilteredAnalyticV3

/-! # Global logarithmic envelope for natural dyadic shell counts -/

namespace MRTLemma215DynamicTypeIIGlobalCountV3

open MRTLemma215DyadicPartition MRTLemma215DynamicMultiplicityBoundsV3

noncomputable section

/-- Any natural cutoff below `X` has at most `3 log X` source dyadic cells.
This packages the monotonicity step needed for prefix and suffix cell counts. -/
theorem sourceDyadicCount_nat_le_three_log
    {N : ℕ} {X : ℝ} (hX : 3 ≤ X) (hNX : (N : ℝ) ≤ X) :
    (sourceDyadicCount N : ℝ) ≤ 3 * Real.log X := by
  by_cases hN : 3 ≤ N
  · have hbase := sourceDyadicCount_floor_le (X := (N : ℝ))
      (by exact_mod_cast hN)
    have hfloor : ⌊(N : ℝ)⌋₊ = N := Nat.floor_natCast N
    rw [hfloor] at hbase
    have hlogN : Real.log (N : ℝ) ≤ Real.log X :=
      Real.log_le_log (by positivity) hNX
    linarith
  · have hsmall : N ≤ 2 := by omega
    have hcount : sourceDyadicCount N ≤ 2 := by
      unfold sourceDyadicCount
      have hself := Nat.log2_le_self (N - 1)
      omega
    have hlog : 1 ≤ Real.log X := by
      calc
        1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log X := Real.log_le_log (Real.exp_pos 1)
          (Real.exp_one_lt_three.le.trans hX)
    have hcountR : (sourceDyadicCount N : ℝ) ≤ 2 := by
      exact_mod_cast hcount
    linarith

/-- Product cutoffs need not lie below `X`: a fixed-degree polynomial
cutoff still has a logarithmic number of cells. -/
theorem sourceDyadicCount_nat_le_three_mul_degree_log
    {N d : ℕ} {X : ℝ} (hX : 3 ≤ X) (hd : 1 ≤ d)
    (hNX : (N : ℝ) ≤ X ^ d) :
    (sourceDyadicCount N : ℝ) ≤ 3 * d * Real.log X := by
  have hpow : X ≤ X ^ d := le_self_pow₀ (by linarith : 1 ≤ X) (by omega)
  have hbase := sourceDyadicCount_nat_le_three_log (hX.trans hpow) hNX
  simpa only [Real.log_pow, mul_assoc] using hbase


open MAPDynamicHBSourceV3 MAPFinishDynamicThreeTypeTrace
open MRTLemma215HBExpansion MRTLemma215DynamicSupportV3
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicHighProvenanceV3 MRTLemma215DynamicTypeIIFiniteEnvelopeV3
open MRTLemma215DynamicTypeIIFactorizationV3

theorem dynamicHBCutoff_le_two_mul {X : ℝ} {K : ℕ}
    (hX : 3 ≤ X) (hK : 1 ≤ K) : dynamicHBCutoff X K ≤ 2 * X := by
  unfold dynamicHBCutoff
  calc
    _ ≤ Real.rpow (2 * X) 1 := Real.rpow_le_rpow_of_exponent_le
      (by linarith) (inv_le_one_of_one_le₀ (by exact_mod_cast hK))
    _ = _ := Real.rpow_one _

theorem sourceDyadicCount_dynamicHBCutoff_le {X : ℝ} {K : ℕ}
    (hX : 3 ≤ X) (hK : 1 ≤ K) :
    (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊ : ℝ) ≤ 6 * Real.log X := by
  have hfloor : (⌊dynamicHBCutoff X K⌋₊ : ℝ) ≤ 2 * X :=
    (Nat.floor_le (Real.rpow_nonneg (by linarith) _)).trans
      (dynamicHBCutoff_le_two_mul hX hK)
  have hb := sourceDyadicCount_nat_le_three_log (by linarith : 3 ≤ 2 * X) hfloor
  have hl : Real.log (2 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num) (by linarith : X ≠ 0)]
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ X)
    linarith
  linarith

theorem log_one_le {X : ℝ} (hX : 3 ≤ X) : 1 ≤ Real.log X := by
  calc
    1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log X := Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.le.trans hX)

theorem dynamicLowZBagSet_card_le_polylog {X : ℝ} {K k : ℕ}
    (hX : 3 ≤ X) (hk : k < K) :
    ((dynamicLowZBagSetV3 X k).card : ℝ) ≤
      ((6 + K : ℕ) : ℝ) ^ K * Real.log X ^ K := by
  have hb : ((dynamicLowZBagSetV3 X k).card : ℝ) ≤
      ((sourceDyadicCount (hbFactorCutoff X) : ℝ) + k) ^ k := by
    exact_mod_cast dynamicLowZBagSet_card_le_pow X k
  have hc := sourceDyadicCount_hbFactorCutoff_le hX
  have hl := log_one_le hX
  have hkR : (k : ℝ) ≤ K := by exact_mod_cast hk.le
  have hbase : (sourceDyadicCount (hbFactorCutoff X) : ℝ) + k ≤
      (6 + K : ℝ) * Real.log X := by nlinarith
  calc
    _ ≤ ((6 + K : ℝ) * Real.log X) ^ k := hb.trans (by gcongr)
    _ ≤ ((6 + K : ℝ) * Real.log X) ^ K :=
      pow_le_pow_right₀ (by nlinarith : 1 ≤ (6 + K : ℝ) * Real.log X) hk.le
    _ = _ := by rw [mul_pow]; norm_cast

theorem dynamicLowMBagSet_card_le_polylog {X : ℝ} {K k : ℕ}
    (hX : 3 ≤ X) (hk : k < K) :
    ((dynamicLowMBagSetV3 X K k).card : ℝ) ≤
      ((6 + K : ℕ) : ℝ) ^ K * Real.log X ^ K := by
  have hK : 1 ≤ K := by omega
  have hb : ((dynamicLowMBagSetV3 X K k).card : ℝ) ≤
      ((sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊ : ℝ) + k + 1) ^ (k + 1) := by
    exact_mod_cast dynamicLowMBagSet_card_le_pow X K k
  have hc := sourceDyadicCount_dynamicHBCutoff_le hX hK
  have hl := log_one_le hX
  have hkR : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk
  have hbase : (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊ : ℝ) + k + 1 ≤
      (6 + K : ℝ) * Real.log X := by nlinarith
  calc
    _ ≤ ((6 + K : ℝ) * Real.log X) ^ (k + 1) := hb.trans (by gcongr)
    _ ≤ ((6 + K : ℝ) * Real.log X) ^ K :=
      pow_le_pow_right₀ (by nlinarith : 1 ≤ (6 + K : ℝ) * Real.log X) hk
    _ = _ := by rw [mul_pow]; norm_cast

theorem dynamicLowComponentMultiplicity_le_polylog {X : ℝ} {K k : ℕ}
    (hX : 3 ≤ X) (hk : k < K) :
    (dynamicLowComponentMultiplicityV3 X K k : ℝ) ≤
      (6 * ((6 + K : ℕ) : ℝ) ^ (2 * K)) * Real.log X ^ (2 * K + 1) := by
  have hz := dynamicLowZBagSet_card_le_polylog hX hk
  have hm := dynamicLowMBagSet_card_le_polylog hX hk
  have hc := sourceDyadicCount_hbFactorCutoff_le hX
  have hl : 0 ≤ Real.log X := (log_one_le hX).trans' (by norm_num)
  unfold dynamicLowComponentMultiplicityV3
  push_cast
  calc
    _ ≤ (6 * Real.log X) *
        (((6 + K : ℕ) : ℝ) ^ K * Real.log X ^ K) *
        (((6 + K : ℕ) : ℝ) ^ K * Real.log X ^ K) := by gcongr
    _ = _ := by push_cast; ring


theorem sourceDyadicScale_le_max (N : ℕ) (j : Fin (sourceDyadicCount N)) :
    2 ^ (j : ℕ) ≤ max 1 N := by
  have hj : (j : ℕ) ≤ (N - 1).log2 := by have := j.isLt; unfold sourceDyadicCount at this; omega
  have hp := Nat.pow_le_pow_right (by omega : 0 < 2) hj
  by_cases hn : 0 < N - 1
  · exact hp.trans ((Nat.log2_self_le hn.ne').trans (by omega))
  · have hz : N - 1 = 0 := by omega
    simp [hz] at hj
    simp [hj]

theorem sourceDyadicScale_le_two_mul {X : ℝ} (hX : 3 ≤ X)
    {N : ℕ} (hN : (N : ℝ) ≤ 2 * X) (j : Fin (sourceDyadicCount N)) :
    ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ 2 * X := by
  have hb : ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ max (1 : ℝ) N := by
    exact_mod_cast sourceDyadicScale_le_max N j
  exact hb.trans (max_le (by linarith) hN)

theorem sortedComponentFactor_length_le_two_mul
    {X : ℝ} {K k : ℕ} (hX : 3 ≤ X) (hK : 1 ≤ K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    {f : NatDyadicFactor} (hf : f ∈ sortedComponentFactorList logIndex zbag mbag) :
    (f.length : ℝ) ≤ 2 * X := by
  have hz : (hbFactorCutoff X : ℝ) ≤ 2 * X := by
    exact Nat.floor_le (by linarith)
  have hm : (⌊dynamicHBCutoff X K⌋₊ : ℝ) ≤ 2 * X :=
    (Nat.floor_le (Real.rpow_nonneg (by linarith) _)).trans
      (dynamicHBCutoff_le_two_mul hX hK)
  have hfOriginal := (sortedComponentFactorList_perm logIndex zbag mbag).mem_iff.mp hf
  unfold dynamicComponentFactorList at hfOriginal
  simp only [List.mem_cons, List.mem_append] at hfOriginal
  rcases hfOriginal with rfl | hzeta | hmoebius
  · exact sourceDyadicScale_le_two_mul hX hz logIndex
  · obtain ⟨j, rfl⟩ := mem_bagFactorList_exists (dynamicZetaFactor X) zbag hzeta
    exact sourceDyadicScale_le_two_mul hX hz j
  · obtain ⟨j, rfl⟩ := mem_bagFactorList_exists (dynamicMoebiusFactor X K) mbag hmoebius
    exact sourceDyadicScale_le_two_mul hX hm j

theorem factorUpperProduct_le_cube_pow {X : ℝ} (hX : 3 ≤ X)
    (factors : List NatDyadicFactor)
    (hf : ∀ f ∈ factors, (f.length : ℝ) ≤ 2 * X) :
    (factorUpperProduct factors : ℝ) ≤ (X ^ 3) ^ factors.length := by
  induction factors with
  | nil => simp
  | cons f fs ih =>
    rw [factorUpperProduct_cons, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat,
      List.length_cons, pow_succ]
    have hfirst := hf f (by simp)
    have htail := ih (fun g hg => hf g (by simp [hg]))
    have hcube : 2 * (f.length : ℝ) ≤ X ^ 3 := by nlinarith [sq_nonneg (X - 3)]
    calc
      _ ≤ X ^ 3 * (X ^ 3) ^ fs.length := mul_le_mul hcube htail (by positivity) (by positivity)
      _ = _ := by ring

theorem actualSplit_sourceDyadicCounts_le
    {X : ℝ} {K : ℕ} (hX : 3 ≤ X) (branch : Fin K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) (branch : ℕ))
    (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) ((branch : ℕ) + 1))
    (s : ℕ) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    (sourceDyadicCount (factorUpperProduct (typeIIPrefixFactorList factors s)) : ℝ) ≤
      18 * K * Real.log X ∧
    (sourceDyadicCount (factorUpperProduct (typeIISuffixFactorList factors s)) : ℝ) ≤
      18 * K * Real.log X := by
  dsimp only
  have hK : 1 ≤ K := by have := branch.isLt; omega
  have hlen := sortedComponentFactorList_length_le logIndex zbag mbag
  have hbranch := branch.isLt
  have hbound : ∀ sub : List NatDyadicFactor,
      (∀ f ∈ sub, f ∈ sortedComponentFactorList logIndex zbag mbag) →
      sub.length ≤ 2 * K →
      (sourceDyadicCount (factorUpperProduct sub) : ℝ) ≤ 18 * K * Real.log X := by
    intro sub hsub hlength
    have hp := factorUpperProduct_le_cube_pow hX sub
      (fun f hf => sortedComponentFactor_length_le_two_mul hX hK logIndex zbag mbag (hsub f hf))
    have hpow : (factorUpperProduct sub : ℝ) ≤ X ^ (6 * K) := by
      calc
        _ ≤ (X ^ 3) ^ sub.length := hp
        _ = X ^ (3 * sub.length) := (pow_mul _ _ _).symm
        _ ≤ X ^ (6 * K) := pow_le_pow_right₀ (by linarith) (by omega)
    have hb := sourceDyadicCount_nat_le_three_mul_degree_log hX (by omega : 1 ≤ 6 * K) hpow
    push_cast at hb
    nlinarith
  constructor
  · apply hbound
    · intro f hf; exact List.mem_of_mem_take hf
    · unfold typeIIPrefixFactorList; simp only [List.length_take]; omega
  · apply hbound
    · intro f hf; exact List.mem_of_mem_drop hf
    · unfold typeIISuffixFactorList; simp only [List.length_drop]; omega


open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourcePacketBoundRefinedV3
open MRTProposition61TypeIIComponentTotalV3
open MRTProposition61TypeIIActiveAggregateBoundV3
open MRTProposition61TypeIIGlobalFilteredAnalyticV3
open MRTLemma215ScaleClassifierV3 MRTLemma215DynamicOutcomeWeldV3

/-- Literal filtered cell sums have only four shell-count losses: the
original Cauchy multiplier and the two finite summations. -/
theorem dynamicFilteredTypeIIAnalyticAggregate_le_of_cell_bound
    {p : Corollary53Input} {delta H₀ T theta C B : ℝ} {K : ℕ}
    (hX : 3 ≤ p.X) (hB : 0 ≤ B) (branch : Fin K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) (branch : ℕ))
    (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff p.X K⌋₊))) ((branch : ℕ) + 1))
    (component : OuterComponent)
    (hcell :
      let factors := sortedComponentFactorList logIndex zbag mbag
      let s := largestSmallPrefix
        (dynamicPreliminaryScaleList (some logIndex) zbag mbag) (Real.rpow p.X delta)
      let left := typeIIPrefixFactorList factors s
      let suffix := typeIISuffixFactorList factors s
      dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag = .typeII →
      suffix ≠ [] →
      ∀ leftCell : Fin (sourceDyadicCount (factorUpperProduct left)),
      ∀ suffixCell ∈ activeTypeIINonzeroSuffixCellsV3 zbag mbag left suffix leftCell,
        activeTypeIICellAnalyticRHSV3 p T theta C logIndex zbag mbag
          left suffix leftCell suffixCell component ≤ B) :
    dynamicFilteredTypeIIAnalyticAggregateV3 p delta H₀ T theta C
      logIndex zbag mbag component ≤ (18 * K) ^ 4 * Real.log p.X ^ 4 * B := by
  classical
  let factors := sortedComponentFactorList logIndex zbag mbag
  let s := largestSmallPrefix
    (dynamicPreliminaryScaleList (some logIndex) zbag mbag) (Real.rpow p.X delta)
  let left := typeIIPrefixFactorList factors s
  let suffix := typeIISuffixFactorList factors s
  let l := sourceDyadicCount (factorUpperProduct left)
  let r := sourceDyadicCount (factorUpperProduct suffix)
  have hcounts := actualSplit_sourceDyadicCounts_le hX branch logIndex zbag mbag s
  change (l : ℝ) ≤ 18 * K * Real.log p.X ∧ (r : ℝ) ≤ 18 * K * Real.log p.X at hcounts
  change dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag = .typeII →
    suffix ≠ [] → ∀ i : Fin l,
      ∀ j ∈ activeTypeIINonzeroSuffixCellsV3 zbag mbag left suffix i,
      activeTypeIICellAnalyticRHSV3 p T theta C logIndex zbag mbag left suffix i j component ≤ B at hcell
  unfold dynamicFilteredTypeIIAnalyticAggregateV3
  change (if dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag = .typeII then
    if suffix = [] then 0 else (l : ℝ) * r *
      ∑ i : Fin l, ∑ j ∈ activeTypeIINonzeroSuffixCellsV3 zbag mbag left suffix i,
        activeTypeIICellAnalyticRHSV3 p T theta C logIndex zbag mbag left suffix i j component
    else 0) ≤ _
  split_ifs with ho hs
  · positivity
  · have hsum : (∑ i : Fin l, ∑ j ∈ activeTypeIINonzeroSuffixCellsV3 zbag mbag left suffix i,
        activeTypeIICellAnalyticRHSV3 p T theta C logIndex zbag mbag left suffix i j component) ≤
        (l : ℝ) * r * B := by
      calc
        _ ≤ ∑ i : Fin l, (r : ℝ) * B := by
          apply Finset.sum_le_sum
          intro i hi
          calc
            _ ≤ ∑ j ∈ activeTypeIINonzeroSuffixCellsV3 zbag mbag left suffix i, B :=
              Finset.sum_le_sum (fun j hj => hcell ho hs i j hj)
            _ = ((activeTypeIINonzeroSuffixCellsV3 zbag mbag left suffix i).card : ℝ) * B := by simp
            _ ≤ (r : ℝ) * B := by
              apply mul_le_mul_of_nonneg_right _ hB
              exact_mod_cast (show (activeTypeIINonzeroSuffixCellsV3 zbag mbag left suffix i).card ≤ r from
                (Finset.card_le_univ _).trans_eq (Fintype.card_fin _))
        _ = _ := by simp [mul_assoc]
    have hl : 0 ≤ Real.log p.X := (log_one_le hX).trans' (by norm_num)
    calc
      _ ≤ (l : ℝ) * r * ((l : ℝ) * r * B) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (18 * K * Real.log p.X) * (18 * K * Real.log p.X) *
          ((18 * K * Real.log p.X) * (18 * K * Real.log p.X) * B) := by gcongr <;> first | exact hcounts.1 | exact hcounts.2
      _ = _ := by ring
  · positivity

/-- The actual global component enumeration costs two multiplicity factors.
All bag and logarithmic-shell counts are discharged by source theorems. -/
theorem dynamicAllTypeIIFilteredAnalyticLedger_le_of_aggregate_bound
    {p : Corollary53Input} {delta H₀ T theta C A : ℝ}
    (hX : 3 ≤ p.X) (hA : 0 ≤ A)
    (haggregate : ∀ (component : OuterComponent) (branch : Fin (hbOrder delta))
      (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
      (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) (branch : ℕ))
      (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊))) ((branch : ℕ) + 1)),
      dynamicFilteredTypeIIAnalyticAggregateV3 p delta H₀ T theta C
        logIndex zbag mbag component ≤ A) :
    dynamicAllTypeIIFilteredAnalyticLedgerV3 p delta H₀ T theta C ≤
      (144 * (hbOrder delta : ℝ) ^ 2 * ((6 + hbOrder delta : ℕ) : ℝ) ^ (4 * hbOrder delta)) *
        Real.log p.X ^ (4 * hbOrder delta + 2) * A := by
  classical
  let K := hbOrder delta
  let M : ℝ := (6 * ((6 + K : ℕ) : ℝ) ^ (2 * K)) * Real.log p.X ^ (2 * K + 1)
  have hl : 0 ≤ Real.log p.X := (log_one_le hX).trans' (by norm_num)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbound : ∀ branch : Fin K,
      (dynamicLowComponentMultiplicityV3 p.X K branch : ℝ) ≤ M :=
    fun branch => dynamicLowComponentMultiplicity_le_polylog hX branch.isLt
  unfold dynamicAllTypeIIFilteredAnalyticLedgerV3
  calc
    _ ≤ ∑ component : OuterComponent, ∑ branch : Fin K,
        (2 * K : ℝ) * M * (M * A) := by
      apply Finset.sum_le_sum
      intro component hc
      apply Finset.sum_le_sum
      intro branch hb
      have hsum : (∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
          ∑ zbag ∈ dynamicLowZBagSetV3 p.X (branch : ℕ),
            ∑ mbag ∈ dynamicLowMBagSetV3 p.X K (branch : ℕ),
              dynamicFilteredTypeIIAnalyticAggregateV3 p delta H₀ T theta C
                logIndex zbag mbag component) ≤ M * A := by
        calc
          _ ≤ ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
              ∑ zbag ∈ dynamicLowZBagSetV3 p.X (branch : ℕ),
                ∑ mbag ∈ dynamicLowMBagSetV3 p.X K (branch : ℕ), A := by
            apply Finset.sum_le_sum; intro i hi
            apply Finset.sum_le_sum; intro z hz
            apply Finset.sum_le_sum; intro m hm
            exact haggregate component branch i z m
          _ = (dynamicLowComponentMultiplicityV3 p.X K branch : ℝ) * A := by
            simp [dynamicLowComponentMultiplicityV3, mul_assoc, mul_comm, mul_left_comm]
          _ ≤ M * A := mul_le_mul_of_nonneg_right (hbound branch) hA
      unfold dynamicBranchLowWeightRefinedV3
      exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hbound branch) (by positivity)) (mul_nonneg hM hA))
    _ = _ := by
      have hcard : Fintype.card OuterComponent = 2 := by decide
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hcard,
        nsmul_eq_mul]
      dsimp [M, K]
      push_cast
      ring


/-- An explicit fixed-order polylogarithmic envelope for the literal global
filtered analytic ledger. The only analytic input is a uniform bound on its
actual active cells; no shell count, bag count or multiplicity is a premise. -/
theorem dynamicAllTypeIIFilteredAnalyticLedger_le_polylog_of_activeCell_bound
    {p : Corollary53Input} {delta H₀ T theta C B : ℝ}
    (hX : 3 ≤ p.X) (hB : 0 ≤ B)
    (hcell : ∀ (component : OuterComponent) (branch : Fin (hbOrder delta))
      (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
      (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) (branch : ℕ))
      (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊))) ((branch : ℕ) + 1)),
      let factors := sortedComponentFactorList logIndex zbag mbag
      let s := largestSmallPrefix
        (dynamicPreliminaryScaleList (some logIndex) zbag mbag) (Real.rpow p.X delta)
      let left := typeIIPrefixFactorList factors s
      let suffix := typeIISuffixFactorList factors s
      dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag = .typeII →
      suffix ≠ [] →
      ∀ leftCell : Fin (sourceDyadicCount (factorUpperProduct left)),
      ∀ suffixCell ∈ activeTypeIINonzeroSuffixCellsV3 zbag mbag left suffix leftCell,
        activeTypeIICellAnalyticRHSV3 p T theta C logIndex zbag mbag
          left suffix leftCell suffixCell component ≤ B) :
    dynamicAllTypeIIFilteredAnalyticLedgerV3 p delta H₀ T theta C ≤
      (144 * (hbOrder delta : ℝ) ^ 2 * ((6 + hbOrder delta : ℕ) : ℝ) ^ (4 * hbOrder delta) *
        (18 * hbOrder delta) ^ 4) * Real.log p.X ^ (4 * hbOrder delta + 6) * B := by
  have h := dynamicAllTypeIIFilteredAnalyticLedger_le_of_aggregate_bound
    (delta := delta) (H₀ := H₀) (T := T) (theta := theta) (C := C)
    hX (show 0 ≤ (18 * (hbOrder delta : ℝ)) ^ 4 * Real.log p.X ^ 4 * B by positivity)
    (fun component branch logIndex zbag mbag =>
      dynamicFilteredTypeIIAnalyticAggregate_le_of_cell_bound hX hB
        branch logIndex zbag mbag component (hcell component branch logIndex zbag mbag))
  convert h using 1 <;> ring

/-- The same literal envelope after multiplying every cell and the global
ledger by a common nonnegative normalization. -/
theorem scaled_dynamicAllTypeIIFilteredAnalyticLedger_le_polylog_of_activeCell_bound
    {p : Corollary53Input} {delta H₀ T theta C B scale : ℝ}
    (hX : 3 ≤ p.X) (hB : 0 ≤ B) (hscale : 0 ≤ scale)
    (hcell : ∀ (component : OuterComponent) (branch : Fin (hbOrder delta))
      (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
      (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) (branch : ℕ))
      (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊))) ((branch : ℕ) + 1)),
      let factors := sortedComponentFactorList logIndex zbag mbag
      let s := largestSmallPrefix
        (dynamicPreliminaryScaleList (some logIndex) zbag mbag) (Real.rpow p.X delta)
      let left := typeIIPrefixFactorList factors s
      let suffix := typeIISuffixFactorList factors s
      dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag = .typeII →
      suffix ≠ [] →
      ∀ leftCell : Fin (sourceDyadicCount (factorUpperProduct left)),
      ∀ suffixCell ∈ activeTypeIINonzeroSuffixCellsV3 zbag mbag left suffix leftCell,
        scale * activeTypeIICellAnalyticRHSV3 p T theta C logIndex zbag mbag
          left suffix leftCell suffixCell component ≤ B) :
    scale * dynamicAllTypeIIFilteredAnalyticLedgerV3 p delta H₀ T theta C ≤
      (144 * (hbOrder delta : ℝ) ^ 2 * ((6 + hbOrder delta : ℕ) : ℝ) ^ (4 * hbOrder delta) *
        (18 * hbOrder delta) ^ 4) * Real.log p.X ^ (4 * hbOrder delta + 6) * B := by
  by_cases hs : scale = 0
  · simp only [hs, zero_mul]
    have hlog : 0 ≤ Real.log p.X := (log_one_le hX).trans' (by norm_num)
    positivity
  · have hspos : 0 < scale := lt_of_le_of_ne hscale (Ne.symm hs)
    have h := dynamicAllTypeIIFilteredAnalyticLedger_le_polylog_of_activeCell_bound
      (delta := delta) (H₀ := H₀) (T := T) (theta := theta) (C := C)
      hX (div_nonneg hB hscale)
      (by
        intro component branch logIndex zbag mbag
        dsimp only
        intro hout hsuffix leftCell suffixCell hactive
        apply (le_div_iff₀ hspos).2
        simpa only [mul_comm] using
          hcell component branch logIndex zbag mbag hout hsuffix leftCell suffixCell hactive)
    have hmul := mul_le_mul_of_nonneg_left h hscale
    convert hmul using 1 <;> field_simp <;> ring

end
end MRTLemma215DynamicTypeIIGlobalCountV3

#print axioms MRTLemma215DynamicTypeIIGlobalCountV3.sourceDyadicCount_nat_le_three_log

#print axioms MRTLemma215DynamicTypeIIGlobalCountV3.sourceDyadicCount_nat_le_three_mul_degree_log

#print axioms MRTLemma215DynamicTypeIIGlobalCountV3.actualSplit_sourceDyadicCounts_le
#print axioms MRTLemma215DynamicTypeIIGlobalCountV3.dynamicLowComponentMultiplicity_le_polylog
#print axioms MRTLemma215DynamicTypeIIGlobalCountV3.dynamicAllTypeIIFilteredAnalyticLedger_le_polylog_of_activeCell_bound

#print axioms MRTLemma215DynamicTypeIIGlobalCountV3.scaled_dynamicAllTypeIIFilteredAnalyticLedger_le_polylog_of_activeCell_bound
