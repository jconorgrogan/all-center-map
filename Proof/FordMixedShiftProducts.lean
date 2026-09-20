import FordMixedKernelBounds
import FordGoodShiftError

noncomputable section
namespace FordMixedShiftProducts

open FordMixedKernelBounds FordGoodShiftError FordDiscretePairCount

/-- Literal sum and product bounds for a list of good natural shifts. -/
theorem good_shift_sum_prod_bounds
    {Q : ℕ} (hQ : 1 ≤ Q) {A : ℝ} (hA : 0 ≤ A)
    (hs : List ℕ)
    (hgood : ∀ g ∈ hs, g ∈ goodShifts Q A) :
    shiftSum (hs.map (fun h : ℕ => (h : ℝ))) ≤
        (hs.length : ℝ) * (Q : ℝ) ∧
      ((Q : ℝ) * A) ^ hs.length ≤
        shiftProd (hs.map (fun h : ℕ => (h : ℝ))) ∧
      shiftProd (hs.map (fun h : ℕ => (h : ℝ))) ≤
        (Q : ℝ) ^ hs.length := by
  induction hs with
  | nil =>
      simp [shiftSum, shiftProd]
  | cons h hs ih =>
      have hmem : h ∈ goodShifts Q A := hgood h (by simp)
      have hpos : h ∈ positiveRange Q :=
        (Finset.mem_filter.mp hmem).1
      have hlow : (Q : ℝ) * A ≤ (h : ℝ) :=
        (Finset.mem_filter.mp hmem).2
      have hlt : h < Q := by
        exact Finset.mem_range.mp (Finset.mem_filter.mp hpos).1
      have hupper : (h : ℝ) ≤ (Q : ℝ) := by
        exact_mod_cast (Nat.le_of_lt hlt)
      have hnonneg : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
      have htail : ∀ g ∈ hs, g ∈ goodShifts Q A := by
        intro g hg
        exact hgood g (by simp [hg])
      have hi := ih htail
      have hqa0 : 0 ≤ (Q : ℝ) * A :=
        mul_nonneg (by exact_mod_cast (Nat.zero_le Q)) hA
      have hprod0 : 0 ≤ shiftProd
          (hs.map (fun k : ℕ => (k : ℝ))) := by
        exact (pow_nonneg hqa0 _).trans hi.2.1
      have hsum :
          (h : ℝ) + shiftSum (hs.map (fun k : ℕ => (k : ℝ))) ≤
            (Q : ℝ) + (hs.length : ℝ) * (Q : ℝ) :=
        add_le_add hupper hi.1
      have hprodlo :
          ((Q : ℝ) * A) ^ (hs.length + 1) ≤
            (h : ℝ) * shiftProd (hs.map (fun k : ℕ => (k : ℝ))) := by
        have hm := mul_le_mul hi.2.1 hlow hqa0 hprod0
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hm
      have hprodup :
          (h : ℝ) * shiftProd (hs.map (fun k : ℕ => (k : ℝ))) ≤
            (Q : ℝ) * (Q : ℝ) ^ hs.length := by
        have hm := mul_le_mul hupper hi.2.2 hprod0
          (by exact_mod_cast (Nat.zero_le Q))
        exact hm
      refine ⟨?_, ?_, ?_⟩
      · simpa [shiftSum, Nat.cast_add, Nat.cast_one, add_mul, add_comm] using hsum
      · simpa [shiftProd, Nat.cast_add] using hprodlo
      · simpa [shiftProd, Nat.cast_add, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hprodup

end FordMixedShiftProducts

#print axioms FordMixedShiftProducts.good_shift_sum_prod_bounds
