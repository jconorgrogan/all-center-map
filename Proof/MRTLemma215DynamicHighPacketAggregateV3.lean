import MRTLemma215OpenIntervalCutoffV3
import MRTLemma215DynamicHighPacketMixedMeanV3

/-!
# Exact aggregate identity for literal dynamic high packets

Every high Type-`d_j`, `j >= 3`, preliminary component is represented by the
sum of its surviving two-factor packets.  The sharp source mask is retained
exactly through the shifted closed endpoint `floor(X)+1`.
-/

namespace MRTLemma215DynamicHighPacketAggregateV3

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPMRTCorollary25 MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215ScaleClassifierV3
open MRTLemma215DynamicOutcomeWeldV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicClassificationV3
open MRTLemma215DynamicHighPacketsV3 MRTLemma215ComplementDyadicV3
open MRTLemma215DynamicHighPacketCertificateV3
open MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215OpenIntervalCutoffV3

noncomputable section

/-- The literal two-factor coefficient of one surviving V3 packet. -/
def highPacketConvolutionV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    {K : ℕ} (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K) :
    ArithmeticFunction ℂ :=
  highPacketShortCoeffV3 packet * highPacketLongCoeffV3 packet

/-- Sum of every surviving packet attached to one high component. -/
def highComponentPacketSumV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (c : DynamicHighComponentIndexV3 X delta H₀ K) :
    ArithmeticFunction ℂ :=
  ∑ cell : {cell : Fin
        (sourceDyadicCount (factorUpperProduct (highComplementV3 c))) //
      cell ∈ survivingComplementCells
        (highSelectedFactorV3 hX hdelta c).length (highComplementV3 c)},
    highPacketConvolutionV3 (Sigma.mk c cell)

theorem highComplementV3_exists_cons
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (c : DynamicHighComponentIndexV3 X delta H₀ K) :
    ∃ head tail, highComplementV3 c = head :: tail := by
  cases hlist : highComplementV3 c with
  | nil =>
      have hlen := highComplementV3_length_one hX hdelta c
      simp [hlist] at hlen
  | cons head tail => exact ⟨head, tail, rfl⟩

/-- Exact unmasked packet expansion of one high component. -/
theorem dynamicPreliminaryComponent_eq_highComponentPacketSumV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (hK : 1 ≤ K)
    (c : DynamicHighComponentIndexV3 X delta H₀ K) :
    dynamicPreliminaryComponent (some (rawLogIndexV3 c.1))
        (rawZetaBagV3 c.1) (rawMoebiusBagV3 c.1) =
      highComponentPacketSumV3 hX hdelta c := by
  have hgeom := highGeometryV3 hX hdelta c
  let s := highSelectedIndexV3 c
  obtain ⟨hs, hM, hsquare, hfactor⟩ := hgeom
  have hraw := dynamicPreliminaryComponent_eq_sum_survivingPackets
    (show 1 ≤ X by linarith) hK
    (rawLogIndexV3 c.1) (rawZetaBagV3 c.1) (rawMoebiusBagV3 c.1)
    s hs hsquare (highComplementV3_exists_cons hX hdelta c)
  rw [hraw]
  unfold highComponentPacketSumV3
  simp only [highPacketConvolutionV3,
    highPacketShortCoeffV3, highPacketLongCoeffV3,
    highSelectedIndexV3, highSelectedFactorV3, highComplementV3,
    highFactorsV3, s]
  apply Finset.sum_subtype
  intro x
  rfl

/-- Exact masked high component, with no left-endpoint atom. -/
theorem dynamicComponentHighV3_eq_cutoff_packetSum
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (hK : 1 ≤ K)
    (c : DynamicHighComponentIndexV3 X delta H₀ K) :
    dynamicComponentHighV3 (delta := delta) (H₀ := H₀)
        (rawLogIndexV3 c.1) (rawZetaBagV3 c.1) (rawMoebiusBagV3 c.1) =
      intervalCutoff (openSourceLeft X) (2 * X)
        (highComponentPacketSumV3 hX hdelta c) := by
  have houtcome := highTypeIndexV3_outcome c
  have hj := highTypeIndexV3_three c
  unfold dynamicComponentHighV3
  rw [houtcome]
  simp only [hj, if_true]
  rw [maskedDynamicComponentV3_eq_intervalCutoff (by linarith)]
  rw [dynamicPreliminaryComponent_eq_highComponentPacketSumV3
    hX hdelta hK c]

/-- Literal finite set of preliminary components of one raw HB branch. -/
def dynamicBranchRawComponentFinsetV3
    (X : ℝ) (K : ℕ) (branch : Fin K) :=
  (Finset.univ : Finset (Fin (sourceDyadicCount (hbFactorCutoff X)))).product
    ((Finset.univ : Finset
      (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))).sym (branch : ℕ) |>.product
      ((Finset.univ : Finset (Option (Fin (sourceDyadicCount
        ⌊dynamicHBCutoff X K⌋₊)))).sym ((branch : ℕ) + 1)))

def DynamicBranchRawComponentIndexV3
    (X : ℝ) (K : ℕ) (branch : Fin K) :=
  {c // c ∈ dynamicBranchRawComponentFinsetV3 X K branch}

instance (X : ℝ) (K : ℕ) (branch : Fin K) :
    Fintype (DynamicBranchRawComponentIndexV3 X K branch) := by
  unfold DynamicBranchRawComponentIndexV3
  infer_instance

def branchRawToGlobalV3
    {X : ℝ} {K : ℕ} {branch : Fin K}
    (c : DynamicBranchRawComponentIndexV3 X K branch) :
    DynamicRawComponentIndexV3 X K :=
  ⟨branch, c.1.1, c.1.2.1, c.1.2.2⟩

def DynamicBranchComponentIsHighV3
    {X : ℝ} {K : ℕ} {branch : Fin K} (delta H₀ : ℝ)
    (c : DynamicBranchRawComponentIndexV3 X K branch) : Prop :=
  DynamicComponentIsHighV3 delta H₀ (branchRawToGlobalV3 c)

def DynamicBranchHighComponentIndexV3
    (X delta H₀ : ℝ) (K : ℕ) (branch : Fin K) :=
  {c : DynamicBranchRawComponentIndexV3 X K branch //
    DynamicBranchComponentIsHighV3 delta H₀ c}

instance (X delta H₀ : ℝ) (K : ℕ) (branch : Fin K) :
    Fintype (DynamicBranchHighComponentIndexV3 X delta H₀ K branch) := by
  classical
  unfold DynamicBranchHighComponentIndexV3
  infer_instance

def branchHighToGlobalV3
    {X delta H₀ : ℝ} {K : ℕ} {branch : Fin K}
    (c : DynamicBranchHighComponentIndexV3 X delta H₀ K branch) :
    DynamicHighComponentIndexV3 X delta H₀ K :=
  ⟨branchRawToGlobalV3 c.1, c.property⟩

/-- Exact finite reindexing of the three nested dyadic shell sums. -/
theorem dynamicRawBranchHighCoeffV3_apply_eq_branchRawSum
    {X delta H₀ : ℝ} {K : ℕ} (branch : Fin K) (n : ℕ) :
    dynamicRawBranchHighCoeffV3 X delta H₀ branch n =
      ∑ c : DynamicBranchRawComponentIndexV3 X K branch,
        dynamicComponentHighV3 (delta := delta) (H₀ := H₀)
          c.1.1 c.1.2.1 c.1.2.2 n := by
  unfold dynamicRawBranchHighCoeffV3
  calc
    (∑ logIndex,
      ∑ zbag ∈ (Finset.univ : Finset
          (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))).sym (branch : ℕ),
        ∑ mbag ∈ (Finset.univ : Finset (Option (Fin (sourceDyadicCount
          ⌊dynamicHBCutoff X K⌋₊)))).sym ((branch : ℕ) + 1),
          dynamicComponentHighV3 (delta := delta) (H₀ := H₀)
            logIndex zbag mbag n) =
      ∑ c ∈ dynamicBranchRawComponentFinsetV3 X K branch,
        dynamicComponentHighV3 (delta := delta) (H₀ := H₀)
          c.1 c.2.1 c.2.2 n := by
        let A := (Finset.univ : Finset
          (Fin (sourceDyadicCount (hbFactorCutoff X))))
        let B := (Finset.univ : Finset
          (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))).sym
            (branch : ℕ)
        let C := (Finset.univ : Finset (Option (Fin (sourceDyadicCount
          ⌊dynamicHBCutoff X K⌋₊)))).sym ((branch : ℕ) + 1)
        let f : (Fin (sourceDyadicCount (hbFactorCutoff X)) ×
            (Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) (branch : ℕ) ×
            Sym (Option (Fin (sourceDyadicCount
              ⌊dynamicHBCutoff X K⌋₊))) ((branch : ℕ) + 1))) → ℂ := fun c =>
          dynamicComponentHighV3
            (delta := delta) (H₀ := H₀) c.1 c.2.1 c.2.2 n
        have houter := Finset.sum_product A (B.product C) f
        have hinner : ∀ a ∈ A,
            (∑ bc ∈ B.product C, f (a, bc)) =
              ∑ b ∈ B, ∑ c ∈ C, f (a, (b, c)) := by
          intro a ha
          exact Finset.sum_product B C (fun bc => f (a, bc))
        unfold dynamicBranchRawComponentFinsetV3
        change (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f (a, (b, c))) =
          ∑ c ∈ A.product (B.product C), f c
        have hsum : (∑ a ∈ A, ∑ bc ∈ B.product C, f (a, bc)) =
            ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f (a, (b, c)) :=
          Finset.sum_congr rfl hinner
        exact (houter.trans hsum).symm
    _ = ∑ c : DynamicBranchRawComponentIndexV3 X K branch,
        dynamicComponentHighV3 (delta := delta) (H₀ := H₀)
          c.1.1 c.1.2.1 c.1.2.2 n :=
      Finset.sum_subtype (dynamicBranchRawComponentFinsetV3 X K branch)
        (fun x => Iff.rfl) _

theorem dynamicBranchComponentHighV3_eq_zero_of_not_high
    {X delta H₀ : ℝ} {K : ℕ} {branch : Fin K}
    (c : DynamicBranchRawComponentIndexV3 X K branch)
    (hc : ¬ DynamicBranchComponentIsHighV3 delta H₀ c) :
    dynamicComponentHighV3 (delta := delta) (H₀ := H₀)
      c.1.1 c.1.2.1 c.1.2.2 = 0 := by
  funext n
  unfold DynamicBranchComponentIsHighV3 DynamicComponentIsHighV3
    branchRawToGlobalV3 at hc
  cases houtcome : dynamicComponentOutcome 8 delta H₀
      c.1.1 c.1.2.1 c.1.2.2 with
  | typeII => simp [dynamicComponentHighV3, houtcome]
  | vanishing => simp [dynamicComponentHighV3, houtcome]
  | typeD j =>
      by_cases hj : 3 ≤ (j : ℕ)
      · exact (hc ⟨j, houtcome, hj⟩).elim
      · simp [dynamicComponentHighV3, houtcome, hj]

/-- All non-high components disappear exactly. -/
theorem dynamicRawBranchHighCoeffV3_eq_branchHighComponentSum
    {X delta H₀ : ℝ} {K : ℕ} (branch : Fin K) :
    dynamicRawBranchHighCoeffV3 X delta H₀ branch =
      ∑ c : DynamicBranchHighComponentIndexV3 X delta H₀ K branch,
        dynamicComponentHighV3 (delta := delta) (H₀ := H₀)
          c.1.1.1 c.1.1.2.1 c.1.1.2.2 := by
  classical
  funext n
  rw [show (∑ c : DynamicBranchHighComponentIndexV3 X delta H₀ K branch,
      dynamicComponentHighV3 (delta := delta) (H₀ := H₀)
        c.1.1.1 c.1.1.2.1 c.1.1.2.2) n =
      ∑ c : DynamicBranchHighComponentIndexV3 X delta H₀ K branch,
        dynamicComponentHighV3 (delta := delta) (H₀ := H₀)
          c.1.1.1 c.1.1.2.1 c.1.1.2.2 n by
    simpa using arithmeticFunction_finsetSum_apply
      (Finset.univ : Finset
        (DynamicBranchHighComponentIndexV3 X delta H₀ K branch))
      (fun c => dynamicComponentHighV3 (delta := delta) (H₀ := H₀)
        c.1.1.1 c.1.1.2.1 c.1.1.2.2) n]
  change dynamicRawBranchHighCoeffV3 X delta H₀ branch n =
    ∑ c : DynamicBranchHighComponentIndexV3 X delta H₀ K branch,
      dynamicComponentHighV3 (delta := delta) (H₀ := H₀)
        c.1.1.1 c.1.1.2.1 c.1.1.2.2 n
  rw [dynamicRawBranchHighCoeffV3_apply_eq_branchRawSum]
  let f := fun c : DynamicBranchRawComponentIndexV3 X K branch =>
    dynamicComponentHighV3 (delta := delta) (H₀ := H₀)
      c.1.1 c.1.2.1 c.1.2.2 n
  let S := (Finset.univ : Finset
    (DynamicBranchRawComponentIndexV3 X K branch)).filter
      (DynamicBranchComponentIsHighV3 delta H₀)
  have hsub : (∑ c ∈ S, f c) =
      ∑ c : DynamicBranchHighComponentIndexV3 X delta H₀ K branch,
        f c.1 := by
    exact Finset.sum_subtype S (by simp [S]) f
  have hfilter : (∑ c : DynamicBranchRawComponentIndexV3 X K branch, f c) =
      ∑ c ∈ S, f c := by
    unfold S
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c hcMem
    by_cases hc : DynamicBranchComponentIsHighV3 delta H₀ c
    · simp [hc]
    · rw [if_neg hc]
      simpa [f] using congrFun
        (dynamicBranchComponentHighV3_eq_zero_of_not_high c hc) n
  exact hfilter.trans hsub

/-- Source-faithful high aggregate after applying the exact open-left MRT
cutoff to each genuine high component. -/
theorem dynamicRawBranchHighCoeffV3_eq_cutoff_highComponentPacketSums
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (hK : 1 ≤ K) (branch : Fin K) :
    dynamicRawBranchHighCoeffV3 X delta H₀ branch =
      ∑ c : DynamicBranchHighComponentIndexV3 X delta H₀ K branch,
        intervalCutoff (openSourceLeft X) (2 * X)
          (highComponentPacketSumV3 hX hdelta (branchHighToGlobalV3 c)) := by
  rw [dynamicRawBranchHighCoeffV3_eq_branchHighComponentSum]
  apply Finset.sum_congr rfl
  intro c hc
  exact dynamicComponentHighV3_eq_cutoff_packetSum hX hdelta hK
    (branchHighToGlobalV3 c)

end
end MRTLemma215DynamicHighPacketAggregateV3

#print axioms MRTLemma215DynamicHighPacketAggregateV3.dynamicPreliminaryComponent_eq_highComponentPacketSumV3
#print axioms MRTLemma215DynamicHighPacketAggregateV3.dynamicComponentHighV3_eq_cutoff_packetSum
#print axioms MRTLemma215DynamicHighPacketAggregateV3.dynamicRawBranchHighCoeffV3_eq_cutoff_highComponentPacketSums
