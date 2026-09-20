import FordSubsetMoment
import FordIntegerPowerMoment

open scoped BigOperators
noncomputable section

namespace FordSubsetPower

open FordSubsetMoment

def subsetFreq (B : Finset ℕ) (M : ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) {s k : ℕ}
    (x : Fin s → BoundedNat B) : Fin k → ℤ :=
  FordIntegerPower.intPowerMap s k M (mapTuple B M hB x)

lemma subsetFreq_apply (B : Finset ℕ) (M : ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) {s k : ℕ}
    (x : Fin s → BoundedNat B) (j : Fin k) :
    subsetFreq B M hB x j =
      (∑ i : Fin s, (x i).val ^ (j.val + 1) : ℕ) := by
  simp [subsetFreq, FordIntegerPower.intPowerMap,
    FordPowerFibers.powerMap, mapTuple, toFinM_val_add_one]

theorem subsetZeroRep_eq_subsetMoment (B : Finset ℕ) (s k M : ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) :
    FordDifferenceDominance.differencePairCount
        (subsetFreq B M hB (s := s) (k := k)) 0 =
      subsetMoment B s k := by
  classical
  unfold FordDifferenceDominance.differencePairCount subsetMoment
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  have hiff :
      subsetFreq B M hB (s := s) (k := k) x -
          subsetFreq B M hB (s := s) (k := k) y = 0 ↔
        subsetPowerEq B s k (x, y) := by
    rw [sub_eq_zero]
    constructor
    · intro h
      intro j hj
      have hjmem := Finset.mem_Icc.mp hj
      let jj : Fin k := ⟨j - 1, by omega⟩
      have hj' := congrFun h jj
      have hcast := hj'
      simp only [subsetFreq_apply] at hcast
      have hnat :
          (∑ i : Fin s, (x i).val ^ (jj.val + 1)) =
            ∑ i : Fin s, (y i).val ^ (jj.val + 1) := by
        exact_mod_cast hcast
      simpa [jj, Nat.sub_add_cancel hjmem.1] using hnat
    · intro h
      funext j
      have hj := h (j.val + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hcast :
          (subsetFreq B M hB (s := s) (k := k) x j) =
            subsetFreq B M hB (s := s) (k := k) y j := by
        simp only [subsetFreq_apply]
        exact_mod_cast hj
      exact hcast
  simp [hiff]

theorem subsetZeroRep_le_completeMoment (B : Finset ℕ) (s k M : ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) :
    FordDifferenceDominance.differencePairCount
        (subsetFreq B M hB (s := s) (k := k)) 0 ≤
      MAPFordCompleteSystemMoment.completeMoment s k M := by
  rw [subsetZeroRep_eq_subsetMoment B s k M hB]
  exact subsetMoment_le_completeMoment B s k M hB

theorem subsetFreq_difference_mem_box (B : Finset ℕ) (s k M : ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) (hr : 1 ≤ s)
    (x y : Fin s → BoundedNat B) :
    subsetFreq B M hB (s := s) (k := k) x -
        subsetFreq B M hB (s := s) (k := k) y ∈
      FordIntegerPower.differenceBox s k M := by
  simpa [subsetFreq, mapTuple] using
    (FordIntegerPower.difference_mem_box hr
      (mapTuple B M hB x) (mapTuple B M hB y))

end FordSubsetPower

#print axioms FordSubsetPower.subsetZeroRep_eq_subsetMoment
#print axioms FordSubsetPower.subsetZeroRep_le_completeMoment
#print axioms FordSubsetPower.subsetFreq_difference_mem_box
