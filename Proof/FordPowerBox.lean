import FordPowerFibers

open scoped BigOperators
noncomputable section

namespace FordPowerBox

def coordinateBox (r k M : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun j : Fin k => Finset.Icc 1 (r * M ^ (j.val + 1)))

theorem powerMap_mem_Icc {r k M : ℕ} (hr : 1 ≤ r)
    (x : Fin r → Fin M) (j : Fin k) :
    FordPowerFibers.powerMap r k M x j ∈
    Finset.Icc 1 (r * M ^ (j.val + 1)) := by
  simp only [Finset.mem_Icc]
  constructor
  · calc
      1 ≤ r := hr
      _ = ∑ _i : Fin r, 1 := by simp
      _ ≤ ∑ i : Fin r, ((x i).val + 1) ^ (j.val + 1) := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.one_le_iff_ne_zero.mpr (Nat.pow_pos (by omega)).ne'
  · calc
      ∑ i : Fin r, ((x i).val + 1) ^ (j.val + 1) ≤
          ∑ _i : Fin r, M ^ (j.val + 1) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Nat.pow_le_pow_left
        omega
      _ = r * M ^ (j.val + 1) := by simp

theorem powerMap_mem_coordinateBox {r k M : ℕ} (hr : 1 ≤ r)
    (x : Fin r → Fin M) :
    FordPowerFibers.powerMap r k M x ∈ coordinateBox r k M := by
  simp only [coordinateBox, Fintype.mem_piFinset]
  intro j
  exact powerMap_mem_Icc hr x j

theorem coordinateBox_card (r k M : ℕ) :
    (coordinateBox r k M).card =
      ∏ j : Fin k, (r * M ^ (j.val + 1)) := by
  simp [coordinateBox]

end FordPowerBox

#print axioms FordPowerBox.powerMap_mem_Icc
#print axioms FordPowerBox.powerMap_mem_coordinateBox
#print axioms FordPowerBox.coordinateBox_card
