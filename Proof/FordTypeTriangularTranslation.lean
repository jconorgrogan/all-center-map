import Mathlib
import FordTypeCenteredDifference

namespace MAPFordType
open Polynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 900000

/-- Ford's triangular translation of the row family by an integer `c`. -/
def triangularTranslation (psi : ℕ → Polynomial ℤ) (c : ℤ) (j : ℕ) : Polynomial ℤ :=
  ∑ ell ∈ Finset.range (j + 1),
    C (Nat.choose j ell : ℤ) * psi ell * C (c ^ (j - ell))

lemma triangularTranslation_eq_zero_of_row_zero
    (psi : ℕ → Polynomial ℤ) (c : ℤ) (j : ℕ) (hzero : ∀ ell ≤ j, psi ell = 0) :
    triangularTranslation psi c j = 0 := by
  simp only [triangularTranslation]
  apply Finset.sum_eq_zero
  intro ell hell
  rw [hzero ell (by exact Nat.le_of_lt_succ (Finset.mem_range.mp hell))]
  simp

lemma triangularTranslation_degree_lower
    (k d : ℕ) (T : ℤ) (m : ℕ) (psi : ℕ → Polynomial ℤ)
    (hpsi : FordType k d T m psi) (c : ℤ)
    (j : ℕ) (hj : j ≤ k) (hdlt : d < j) :
    (∑ ell ∈ Finset.range j,
      C (Nat.choose j ell : ℤ) * psi ell * C (c ^ (j - ell))).degree <
        (psi j).degree := by
  have hrowj := (hpsi j hj).2 hdlt
  have hpsi0 : psi j ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hrowj
    omega
  have htarget : (psi j).degree = (j - d : WithBot ℕ) := by
    rw [degree_eq_natDegree hpsi0, hrowj.1]
  have hsum_le :
      (∑ ell ∈ Finset.range j,
        C (Nat.choose j ell : ℤ) * psi ell * C (c ^ (j - ell))).degree ≤
          ((j - d - 1 : ℕ) : WithBot ℕ) := by
    refine (degree_sum_le _ _).trans (Finset.sup_le fun ell hell => ?_)
    have hellj : ell < j := Finset.mem_range.mp hell
    by_cases held : ell ≤ d
    · rw [(hpsi ell (le_trans (Nat.le_of_lt hellj) hj)).1 held]
      simp
    · have hdell : d < ell := Nat.lt_of_not_ge held
      have hrow := (hpsi ell (le_trans (Nat.le_of_lt hellj) hj)).2 hdell
      have hdegpsi : (psi ell).degree ≤ (ell - d : WithBot ℕ) := by
        exact (natDegree_le_iff_degree_le).mp (le_of_eq hrow.1)
      have hfirst :
          (C (Nat.choose j ell : ℤ) * psi ell).degree ≤
            (psi ell).degree + (0 : WithBot ℕ) := by
        calc
          (C (Nat.choose j ell : ℤ) * psi ell).degree ≤
              (C (Nat.choose j ell : ℤ)).degree + (psi ell).degree :=
            degree_mul_le _ _
          _ ≤ (0 : WithBot ℕ) + (psi ell).degree := by
            have hC : (C (Nat.choose j ell : ℤ)).degree ≤ (0 : WithBot ℕ) := degree_C_le
            exact add_le_add_left hC _
          _ = (psi ell).degree + (0 : WithBot ℕ) := by simp [add_comm]
      calc
        (C (Nat.choose j ell : ℤ) * psi ell * C (c ^ (j - ell))).degree ≤
            (C (Nat.choose j ell : ℤ) * psi ell).degree +
              (C (c ^ (j - ell))).degree := degree_mul_le _ _
        _ ≤ ((psi ell).degree + (0 : WithBot ℕ)) + 0 := by
          have hC : (C (c ^ (j - ell))).degree ≤ (0 : WithBot ℕ) := degree_C_le
          exact add_le_add hfirst hC
        _ ≤ (ell - d : WithBot ℕ) := by simpa using hdegpsi
        _ ≤ ((j - d - 1 : ℕ) : WithBot ℕ) := by
          exact_mod_cast (by omega : ell - d ≤ j - d - 1)
  rw [htarget]
  exact hsum_le.trans_lt (by
    exact WithBot.coe_lt_coe.mpr (by omega : j - d - 1 < j - d))

 theorem ford_type_triangular_translation
    (k d : ℕ) (T : ℤ) (m : ℕ) (psi : ℕ → Polynomial ℤ)
    (hpsi : FordType k d T m psi) (c : ℤ) :
    FordType k d T m (triangularTranslation psi c) := by
  intro j hj
  constructor
  · intro hjd
    apply triangularTranslation_eq_zero_of_row_zero psi c j
    intro ell hell
    exact (hpsi ell (le_trans hell hj)).1 (le_trans hell hjd)
  · intro hdlt
    have hrow := (hpsi j hj).2 hdlt
    let lower : Polynomial ℤ :=
      ∑ ell ∈ Finset.range j,
        C (Nat.choose j ell : ℤ) * psi ell * C (c ^ (j - ell))
    have hlower : lower.degree < (psi j).degree := by
      dsimp [lower]
      exact triangularTranslation_degree_lower k d T m psi hpsi c j hj hdlt
    have hsplit : triangularTranslation psi c j = lower + psi j := by
      simp only [triangularTranslation, lower, Finset.sum_range_succ]
      simp
    have hdeg : (triangularTranslation psi c j).degree = (psi j).degree := by
      rw [hsplit, degree_add_eq_right_of_degree_lt hlower]
    have hnat : (triangularTranslation psi c j).natDegree = j - d := by
      rw [natDegree_eq_of_degree_eq hdeg]
      exact hrow.1
    have hlc : (triangularTranslation psi c j).leadingCoeff = (psi j).leadingCoeff := by
      rw [hsplit, leadingCoeff_add_of_degree_lt hlower]
    exact ⟨hnat, hlc.trans hrow.2⟩

end
end MAPFordType

#print axioms MAPFordType.triangularTranslation_eq_zero_of_row_zero
#print axioms MAPFordType.triangularTranslation_degree_lower
#print axioms MAPFordType.ford_type_triangular_translation
