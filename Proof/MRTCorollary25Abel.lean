import MRTCorollary25RawPrefixFormula
import GoldfeldLemma11TwoFinite

/-!
# Finite Abel step for MRT Corollary 2.5
-/

namespace MAPMRTCorollary25Abel

open scoped BigOperators

noncomputable section

/-- A nonnegative decreasing weight on a natural interval costs only its first
value times a uniform bound for interval prefixes.  This is the exact discrete
Abel step used in MRT Corollary 2.5. -/
theorem norm_sum_Icc_weighted_le_two_first_mul
    (a : ℕ → ℂ) (w : ℕ → ℝ) {L U : ℕ} {P : ℝ}
    (hL : 1 ≤ L) (hLU : L ≤ U) (hP : 0 ≤ P)
    (hprefix : ∀ N : ℕ, L ≤ N → N ≤ U →
      ‖∑ n ∈ Finset.Icc L N, a n‖ ≤ P)
    (hw0 : ∀ n, L ≤ n → n ≤ U → 0 ≤ w n)
    (hwanti : ∀ n, L ≤ n → n < U → w (n + 1) ≤ w n) :
    ‖∑ n ∈ Finset.Icc L U, (w n : ℂ) * a n‖ ≤
      2 * P * w L := by
  let c : ℕ → ℂ := fun n => if n ∈ Finset.Icc L U then a n else 0
  have hcpartial : ∀ r : ℕ,
      ‖∑ n ∈ Finset.range r, c n‖ ≤ P := by
    intro r
    by_cases hrL : r ≤ L
    · have hempty : (Finset.range r).filter (fun n => n ∈ Finset.Icc L U) = ∅ := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc,
          Finset.notMem_empty, iff_false, not_and_or]
        omega
      simp only [c, ← Finset.sum_filter, hempty, Finset.sum_empty, norm_zero]
      exact hP
    · have hLr : L < r := Nat.lt_of_not_ge hrL
      by_cases hrU : r ≤ U + 1
      · have hset : (Finset.range r).filter (fun n => n ∈ Finset.Icc L U) =
            Finset.Icc L (r - 1) := by
          ext n
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
          omega
        simp only [c, ← Finset.sum_filter, hset]
        exact hprefix (r - 1) (by omega) (by omega)
      · have hUr : U + 1 < r := Nat.lt_of_not_ge hrU
        have hset : (Finset.range r).filter (fun n => n ∈ Finset.Icc L U) =
            Finset.Icc L U := by
          ext n
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
          omega
        simp only [c, ← Finset.sum_filter, hset]
        exact hprefix U hLU le_rfl
  have hK : L - 1 < U := by omega
  have hbound := MAPGoldfeldSiegel.norm_sum_Ioc_mul_le_two_mul_of_antitone
    c w hK hcpartial
    (fun n hn hnu => hw0 n (by omega) hnu)
    (fun n hn hnu => hwanti n (by omega) hnu)
  have hset : Finset.Ioc (L - 1) U = Finset.Icc L U := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset] at hbound
  have hc : ∀ n ∈ Finset.Icc L U, c n = a n := by
    intro n hn
    dsimp only [c]
    rw [if_pos hn]
  have hsum :
      (∑ n ∈ Finset.Icc L U, (w n : ℂ) * c n) =
        ∑ n ∈ Finset.Icc L U, (w n : ℂ) * a n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hc n hn]
  rw [hsum] at hbound
  have hpred : L - 1 + 1 = L := Nat.sub_add_cancel hL
  simpa only [hpred] using hbound

/-- The critical-line weight is nonnegative and decreasing. -/
theorem norm_sum_Icc_invSqrt_le_of_prefix
    (a : ℕ → ℂ) {L U : ℕ} {P : ℝ}
    (hL : 1 ≤ L) (hLU : L ≤ U) (hP : 0 ≤ P)
    (hprefix : ∀ N : ℕ, L ≤ N → N ≤ U →
      ‖∑ n ∈ Finset.Icc L N, a n‖ ≤ P) :
    ‖∑ n ∈ Finset.Icc L U,
        ((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ) * a n‖ ≤
      2 * P / Real.sqrt (L : ℝ) := by
  have hbase := norm_sum_Icc_weighted_le_two_first_mul a
    (fun n => 1 / Real.sqrt (n : ℝ)) hL hLU hP hprefix
    (fun n hn hnu => by positivity)
    (fun n hn hnu => by
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hL.trans hn
      have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
      have hsqrtle : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := by
        apply Real.sqrt_le_sqrt
        norm_num
      exact one_div_le_one_div_of_le hsqrtpos hsqrtle)
  simpa [div_eq_mul_inv, mul_assoc] using hbase

end
end MAPMRTCorollary25Abel

#print axioms MAPMRTCorollary25Abel.norm_sum_Icc_weighted_le_two_first_mul
#print axioms MAPMRTCorollary25Abel.norm_sum_Icc_invSqrt_le_of_prefix
