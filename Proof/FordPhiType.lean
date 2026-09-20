import FordP16Source35Triangular

open scoped BigOperators
namespace MAPFordPhiType
open MAPFordP16Source35Triangular MAPFordType

lemma phiNatSucc_eq_translation {k : ℕ} (psi : Fin k → Polynomial ℤ)
    (q c : ℤ) (j : ℕ) (hj : j ≤ k) :
    psiNatSucc (phiRow psi q c) j = triangularTranslation (psiNatSucc psi) (q*c) j := by
  by_cases h0 : j = 0
  · subst j
    simp [psiNatSucc, triangularTranslation]
  · have hjk : j-1 < k := by omega
    simp only [psiNatSucc, h0, ↓reduceDIte, psiNat, hjk, phiRow]
    congr 1
    omega

/-- The corrected finite q*c rows retain the full source degree/leading
coefficient type, including its common m parameter. -/
theorem phiRow_has_FordType {k d m : ℕ} {T : ℤ}
    (psi : Fin k → Polynomial ℤ) (q c : ℤ)
    (hpsi : FordType k d T m (psiNatSucc psi)) :
    FordType k d T m (psiNatSucc (phiRow psi q c)) := by
  have h := ford_type_triangular_translation k d T m (psiNatSucc psi) hpsi (q*c)
  intro j hj
  rw [phiNatSucc_eq_translation psi q c j hj]
  exact h j hj

end MAPFordPhiType
#print axioms MAPFordPhiType.phiRow_has_FordType
