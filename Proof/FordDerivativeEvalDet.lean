import FordEvalDetFactor

open Polynomial
open scoped BigOperators
namespace FordTypeJacobian
noncomputable section

lemma derivative_natDegree_eq
    (f : Polynomial ℤ) (j : ℕ)
    (hdeg : f.natDegree = j + 1) :
    f.derivative.natDegree = j := by
  have hne : f ≠ 0 := by
    intro hz
    simp [hz] at hdeg
  have htop : f.coeff (j + 1) ≠ 0 := by
    rw [← hdeg, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hne
  have hc : f.derivative.coeff j ≠ 0 := by
    rw [Polynomial.coeff_derivative]
    intro hz
    apply htop
    have hj : ((j : ℤ) + 1) ≠ 0 := by omega
    exact (mul_eq_zero.mp hz).resolve_right hj
  have hle : j ≤ f.derivative.natDegree :=
    Polynomial.le_natDegree_of_ne_zero hc
  have hupper : f.derivative.natDegree ≤ j := by
    have := Polynomial.natDegree_derivative_le f
    omega
  exact le_antisymm hupper hle

lemma derivative_leadingCoeff_eq
    (f : Polynomial ℤ) (j : ℕ)
    (hdeg : f.natDegree = j + 1) :
    f.derivative.leadingCoeff =
      ((j : ℤ) + 1) * f.leadingCoeff := by
  have hnat : f.derivative.natDegree = j := derivative_natDegree_eq f j hdeg
  rw [← Polynomial.coeff_natDegree, Polynomial.coeff_derivative, hnat]
  rw [← hdeg, Polynomial.coeff_natDegree]
  ring


theorem det_derivativeEval_factor
    {n : ℕ} (f : Fin n → Polynomial ℤ) (x : Fin n → ℤ)
    (hdeg : ∀ j : Fin n, (f j).natDegree = j.val + 1) :
    (evalMatrix (fun j => (f j).derivative) x).det =
      (∏ j : Fin n, (((j.val : ℤ) + 1) * (f j).leadingCoeff)) *
        (Matrix.vandermonde x).det := by
  rw [det_evalMatrix_factor (fun j => (f j).derivative) x (by
    intro j
    exact derivative_natDegree_eq (f j) j.val (hdeg j))]
  apply congrArg (fun z => z * (Matrix.vandermonde x).det)
  apply Finset.prod_congr rfl
  intro j hj
  exact derivative_leadingCoeff_eq (f j) j.val (hdeg j)

end
end FordTypeJacobian

#print axioms FordTypeJacobian.derivative_natDegree_eq
#print axioms FordTypeJacobian.derivative_leadingCoeff_eq
#print axioms FordTypeJacobian.det_derivativeEval_factor
