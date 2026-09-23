import FordDerivativeEvalDet
import FordP16LiteralResidueBridge
import FordP16Source35Triangular
import FordTypeCenteredDifference

open scoped BigOperators
open MAPFordP16LiteralResidueBridge
open MAPFordP16Source35Triangular
open MAPFordType

namespace FordTypeJacobian
noncomputable section
set_option maxHeartbeats 1200000

lemma psiNatSucc_tail_natDegree
    {k d : ℕ} {T : ℤ} {m : ℕ} (psi : Fin k → Polynomial ℤ)
    (hpsi : FordType k d T m (psiNatSucc psi))
    (hdk : d ≤ k) (j : Fin (k-d)) :
    (psiNatSucc psi (d + j.val + 1)).natDegree = j.val + 1 := by
  have hjk : d + j.val + 1 ≤ k := by omega
  have h := (hpsi (d + j.val + 1) hjk).2 (by omega)
  omega

lemma psiNatSucc_tail_leadingCoeff
    {k d : ℕ} {T : ℤ} {m : ℕ} (psi : Fin k → Polynomial ℤ)
    (hpsi : FordType k d T m (psiNatSucc psi))
    (hdk : d ≤ k) (j : Fin (k-d)) :
    (psiNatSucc psi (d + j.val + 1)).leadingCoeff =
      ((Nat.factorial (d + j.val + 1) /
        Nat.factorial (j.val + 1) : ℕ) : ℤ) * (2 ^ m : ℤ) * T := by
  have hjk : d + j.val + 1 ≤ k := by omega
  have h := (hpsi (d + j.val + 1) hjk).2 (by omega)
  have hsub : d + j.val + 1 - d = j.val + 1 := by omega
  rw [hsub] at h
  exact h.2

theorem sourceJacobian_det_formula
    {k d P : ℕ} {T : ℤ} {m : ℕ}
    (hdk : d ≤ k) (psi : Fin k → Polynomial ℤ)
    (hpsi : FordType k d T m (psiNatSucc psi))
    (x : Fin (k-d) → Fin (P + 1)) :
    (MAPFordCoarseP18Jacobian.sourceJacobian
      (fun j : Fin (k-d) =>
        psiNatSucc psi (d + j.val + 1))
      x).det =
      (∏ j : Fin (k-d),
        (((j.val : ℤ) + 1) *
          (((Nat.factorial (d + j.val + 1) /
            Nat.factorial (j.val + 1) : ℕ) : ℤ) * (2 ^ m : ℤ) * T))) *
        (Matrix.vandermonde (fun i => ((x i).val : ℤ))).det := by
  let f : Fin (k-d) → Polynomial ℤ := fun j =>
    psiNatSucc psi (d + j.val + 1)
  let xInt : Fin (k-d) → ℤ := fun i => ((x i).val : ℤ)
  have hdeg : ∀ j : Fin (k-d), (f j).natDegree = j.val + 1 := by
    intro j
    exact psiNatSucc_tail_natDegree psi hpsi hdk j
  have hdet := det_derivativeEval_factor f xInt hdeg
  have hprod :
      (∏ j : Fin (k-d), (((j.val : ℤ) + 1) *
        (psiNatSucc psi (d + j.val + 1)).leadingCoeff)) =
      (∏ j : Fin (k-d), (((j.val : ℤ) + 1) *
        (((Nat.factorial (d + j.val + 1) /
          Nat.factorial (j.val + 1) : ℕ) : ℤ) * (2 ^ m : ℤ) * T))) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [psiNatSucc_tail_leadingCoeff psi hpsi hdk j]
  rw [hprod] at hdet
  simpa [f, xInt, MAPFordCoarseP18Jacobian.sourceJacobian] using! hdet

end
end FordTypeJacobian

#print axioms FordTypeJacobian.sourceJacobian_det_formula
