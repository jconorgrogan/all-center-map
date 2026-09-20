import Mathlib
import FordCenteredDifferenceDegree

namespace MAPFordType
open Polynomial
noncomputable section
set_option maxHeartbeats 900000

/-- Ford's source type: rows up to `k`, with the first `d` rows zero and
    all later rows having the prescribed degree and leading coefficient.
    The exponent `m` is shared by every row. -/
def FordType (k d : ℕ) (T : ℤ) (m : ℕ)
    (psi : ℕ → Polynomial ℤ) : Prop :=
  ∀ j, j ≤ k →
    (j ≤ d → psi j = 0) ∧
    (d < j →
      (psi j).natDegree = j - d ∧
      (psi j).leadingCoeff =
        ((Nat.factorial j / Nat.factorial (j - d) : ℕ) : ℤ) *
          (2 ^ m : ℤ) * T)

lemma centeredFiniteDifference_eq_zero_of_natDegree_le_one
    (p : Polynomial ℤ) (y : ℤ) (hp : p.natDegree ≤ 1) :
    centeredFiniteDifference p y = 0 := by
  have hform : p = C (p.coeff 1) * X + C (p.coeff 0) :=
    eq_X_add_C_of_natDegree_le_one hp
  rw [hform]
  simp [centeredFiniteDifference]
  ring

lemma ford_factorial_ratio_step
    (j d : ℕ) (hdj : d + 1 ≤ j) :
    (j - d) * (Nat.factorial j / Nat.factorial (j - d)) =
      Nat.factorial j / Nat.factorial (j - (d + 1)) := by
  rw [← Nat.descFactorial_eq_div (by omega : d ≤ j),
    ← Nat.descFactorial_eq_div (by omega : d + 1 ≤ j)]
  rw [Nat.descFactorial_succ]

 theorem ford_type_centered_difference
    (k d : ℕ) (T : ℤ) (m : ℕ) (psi : ℕ → Polynomial ℤ)
    (hpsi : FordType k d T m psi) (y : ℤ) (hy : 0 < y) :
    FordType k (d + 1) (y * T) m
      (fun j => centeredFiniteDifference (psi j) y) := by
  intro j hj
  constructor
  · intro hjd1
    by_cases hjd : j ≤ d
    · exact congrArg (fun p : Polynomial ℤ => centeredFiniteDifference p y)
        (hpsi j hj |>.1 hjd) |>.trans (by simp [centeredFiniteDifference])
    · have hdlt : d < j := Nat.lt_of_not_ge hjd
      have hj_eq : j = d + 1 := by omega
      subst j
      have hpdeg : (psi (d + 1)).natDegree = 1 := by
        have h := ((hpsi (d + 1) hj).2 (by omega)).1
        omega
      exact centeredFiniteDifference_eq_zero_of_natDegree_le_one _ y (by omega)
  · intro hd1j
    have hdlt : d < j := by omega
    have hrow := (hpsi j hj).2 hdlt
    have hjd2 : d + 2 ≤ j := by omega
    let n : ℕ := j - d - 2
    have hpn : (psi j).natDegree = n + 2 := by
      dsimp [n]
      omega
    have hcenter := centered_difference_degree_leadingCoeff (psi j) n y hpn hy
    have hdeg :
        (centeredFiniteDifference (psi j) y).natDegree = j - (d + 1) := by
      have := hcenter.1
      dsimp [n] at this
      omega
    have hlc :
        (centeredFiniteDifference (psi j) y).leadingCoeff =
          ((Nat.factorial j / Nat.factorial (j - (d + 1)) : ℕ) : ℤ) *
            (2 ^ m : ℤ) * (y * T) := by
      rw [hcenter.2, hrow.2]
      have hratio := ford_factorial_ratio_step j d (by omega)
      have hratioZ :
          ((j - d : ℕ) : ℤ) *
              ((Nat.factorial j / Nat.factorial (j - d) : ℕ) : ℤ) =
            ((Nat.factorial j / Nat.factorial (j - (d + 1)) : ℕ) : ℤ) := by
        exact_mod_cast hratio
      have hncast : ((n + 2 : ℕ) : ℤ) = ((j - d : ℕ) : ℤ) := by
        dsimp [n]
        omega
      rw [hncast]
      calc
        ((j - d : ℕ) : ℤ) *
              (((Nat.factorial j / Nat.factorial (j - d) : ℕ) : ℤ) *
                (2 ^ m : ℤ) * T) * y =
            (((j - d : ℕ) : ℤ) *
              ((Nat.factorial j / Nat.factorial (j - d) : ℕ) : ℤ)) *
                (2 ^ m : ℤ) * T * y := by ring
        _ = ((Nat.factorial j / Nat.factorial (j - (d + 1)) : ℕ) : ℤ) *
              (2 ^ m : ℤ) * (y * T) := by rw [hratioZ]; ring
    exact ⟨hdeg, hlc⟩

end
end MAPFordType

#print axioms MAPFordType.centeredFiniteDifference_eq_zero_of_natDegree_le_one
#print axioms MAPFordType.ford_factorial_ratio_step
#print axioms MAPFordType.ford_type_centered_difference
