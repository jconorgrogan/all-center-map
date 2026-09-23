import Mathlib
import FordDifferenceLeadingCoeff
namespace MAPFordType
open Polynomial
noncomputable section
set_option maxHeartbeats 900000

def centeredFiniteDifference (p : Polynomial ℤ) (y : ℤ) : Polynomial ℤ :=
  (p.comp (X + C y) - p) - C (p.eval y - p.eval 0)

theorem centered_difference_degree_leadingCoeff
    (p : Polynomial ℤ) (n : ℕ) (y : ℤ)
    (hp : p.natDegree = n + 2) (hy : 0 < y) :
    (centeredFiniteDifference p y).natDegree = n + 1 ∧
      (centeredFiniteDifference p y).leadingCoeff =
        ((n + 2 : ℕ) : ℤ) * p.leadingCoeff * y := by
  have hp0 : p ≠ 0 := by
    intro hpz
    subst p
    simp at hp
  have hlc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  have ht0 : taylor y p ≠ 0 := by
    rw [← leadingCoeff_ne_zero]
    rw [leadingCoeff_taylor]
    exact hlc0
  have htd : (taylor y p).degree = p.degree := by
    rw [degree_eq_natDegree ht0, degree_eq_natDegree hp0, natDegree_taylor]
  let r : Polynomial ℤ := p.comp (X + C y) - p
  have hrdeg : r.degree < p.degree := by
    dsimp [r]
    rw [← taylor_apply y p]
    simpa [htd] using degree_sub_lt htd ht0 (by rw [leadingCoeff_taylor])
  have hrcoeff : r.coeff (n + 1) =
      ((n + 2 : ℕ) : ℤ) * p.leadingCoeff * y := by
    dsimp [r]
    convert coeff_translated_sub p (n + 1) y (by omega)
    push_cast
    ring
  have hfac0 : ((n + 2 : ℕ) : ℤ) * p.leadingCoeff * y ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · omega
      · exact hlc0
    · omega
  have hrcoeff0 : r.coeff (n + 1) ≠ 0 := by rw [hrcoeff]; exact hfac0
  have hr0 : r ≠ 0 := by
    intro hrz
    rw [hrz] at hrcoeff0
    exact hrcoeff0 (by simp)
  have hrdeg' : r.degree < (n + 2 : WithBot ℕ) := by
    calc
      r.degree < p.degree := hrdeg
      _ = (n + 2 : WithBot ℕ) := by
        rw [degree_eq_natDegree hp0, hp]
        norm_num [Nat.cast_add]
  have hrnatlt : r.natDegree < n + 2 :=
    (natDegree_lt_iff_degree_lt hr0).2 hrdeg'
  have hrnatge : n + 1 ≤ r.natDegree := by
    by_contra hn
    have hn' : r.natDegree < n + 1 := Nat.lt_of_not_ge hn
    exact hrcoeff0 (coeff_eq_zero_of_natDegree_lt hn')
  have hrnat : r.natDegree = n + 1 := by omega
  have hcdeg : (centeredFiniteDifference p y).natDegree = n + 1 := by
    dsimp [centeredFiniteDifference]
    rw [natDegree_sub_C, hrnat]
  constructor
  · exact hcdeg
  · rw [← coeff_natDegree]
    rw [hcdeg]
    change (r - C (p.eval y - p.eval 0)).coeff (n + 1) =
      ((n + 2 : ℕ) : ℤ) * p.leadingCoeff * y
    rw [coeff_sub]
    rw [coeff_C_ne_zero (by omega), sub_zero, hrcoeff]

end
end MAPFordType

#print axioms MAPFordType.centered_difference_degree_leadingCoeff
