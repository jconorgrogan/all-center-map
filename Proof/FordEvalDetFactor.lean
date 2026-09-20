import Mathlib.LinearAlgebra.Vandermonde
import Mathlib

open Polynomial
open scoped BigOperators
namespace FordTypeJacobian
noncomputable section

def evalMatrix {R : Type*} [CommRing R] {n : ℕ}
    (g : Fin n → Polynomial R) (x : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => (g j).eval (x i)

def coeffMatrix {R : Type*} [CommRing R] {n : ℕ}
    (g : Fin n → Polynomial R) : Matrix (Fin n) (Fin n) R :=
  fun t j => (g j).coeff t.val

lemma evalMatrix_eq_vandermonde_mul_coeffMatrix
    {R : Type*} [CommRing R] {n : ℕ}
    (g : Fin n → Polynomial R) (x : Fin n → R)
    (hdeg : ∀ j : Fin n, (g j).natDegree = j.val) :
    evalMatrix g x = Matrix.vandermonde x * coeffMatrix g := by
  ext i j
  simp only [evalMatrix, Matrix.mul_apply, Matrix.vandermonde, coeffMatrix]
  change (g j).eval (x i) = ∑ t : Fin n, x i ^ t.val * (g j).coeff t.val
  rw [Polynomial.eval_eq_sum_range, hdeg j]
  rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => x i ^ t * (g j).coeff t) n]
  calc
    (∑ t ∈ Finset.range (j.val + 1), (g j).coeff t * x i ^ t) =
        ∑ t ∈ Finset.range (j.val + 1), x i ^ t * (g j).coeff t := by
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = ∑ t ∈ Finset.range n, x i ^ t * (g j).coeff t := by
      apply Finset.sum_subset ((Finset.range_subset_range).mpr (by omega))
      intro t ht htn
      have hzero : (g j).coeff t = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [hdeg j]
        have htlt : t < n := Finset.mem_range.mp ht
        have hnotlt : ¬ t < j.val + 1 := by
          simpa [Finset.mem_range] using htn
        omega
      simp [hzero]

lemma coeffMatrix_upper
    {R : Type*} [CommRing R] {n : ℕ}
    (g : Fin n → Polynomial R)
    (hdeg : ∀ j : Fin n, (g j).natDegree = j.val) :
    (coeffMatrix g).BlockTriangular id := by
  intro i j hji
  have hnot : j.val < i.val := by exact_mod_cast hji
  simp only [coeffMatrix]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [hdeg j]
  exact hnot

lemma det_evalMatrix_factor
    {R : Type*} [CommRing R] {n : ℕ}
    (g : Fin n → Polynomial R) (x : Fin n → R)
    (hdeg : ∀ j : Fin n, (g j).natDegree = j.val) :
    (evalMatrix g x).det =
      (∏ j : Fin n, (g j).leadingCoeff) * (Matrix.vandermonde x).det := by
  rw [evalMatrix_eq_vandermonde_mul_coeffMatrix g x hdeg, Matrix.det_mul,
    Matrix.det_of_upperTriangular (coeffMatrix_upper g hdeg)]
  have hdiag : ∀ j : Fin n, (g j).coeff j.val = (g j).leadingCoeff := by
    intro j
    rw [← hdeg j]
    exact Polynomial.coeff_natDegree
  simp only [coeffMatrix]
  calc
    (Matrix.vandermonde x).det * ∏ j : Fin n, (g j).coeff j.val =
        (∏ j : Fin n, (g j).coeff j.val) * (Matrix.vandermonde x).det := by ring
    _ = (∏ j : Fin n, (g j).leadingCoeff) * (Matrix.vandermonde x).det := by
      rw [Finset.prod_congr rfl (fun j _ => hdiag j)]

end
end FordTypeJacobian

#print axioms FordTypeJacobian.evalMatrix_eq_vandermonde_mul_coeffMatrix
#print axioms FordTypeJacobian.coeffMatrix_upper
#print axioms FordTypeJacobian.det_evalMatrix_factor
