import FordTypeCenteredDifference
import FordP16Source35Triangular

open scoped BigOperators ZMod

namespace MAPFordFamilyDoubling
noncomputable section
set_option maxHeartbeats 1000000

open MAPFordType
open MAPFordP16Source35Triangular
open MAPFordP16FiniteFourierBridge
open Polynomial

/-- Doubling every row multiplies its prescribed leading coefficient by `2`. -/
theorem ford_type_double_nat
    {k d : ℕ} {T : ℤ} {m : ℕ} (psi : ℕ → Polynomial ℤ)
    (hType : FordType k d T m psi) :
    FordType k d T (m + 1) (fun j => C (2 : ℤ) * psi j) := by
  intro j hj
  constructor
  · intro hjd
    simp [hType j hj |>.1 hjd]
  · intro hdj
    have hrow := (hType j hj).2 hdj
    constructor
    · rw [natDegree_C_mul (by norm_num : (2 : ℤ) ≠ 0)]
      exact hrow.1
    · rw [leadingCoeff_mul, leadingCoeff_C]
      rw [hrow.2]
      norm_num [pow_succ]
      ring

/-- The finite-row doubling map. -/
def doublePsi {k : ℕ} (psi : Fin k → Polynomial ℤ) : Fin k → Polynomial ℤ :=
  fun j => C (2 : ℤ) * psi j

lemma psiNatSucc_doublePsi
    {k : ℕ} (psi : Fin k → Polynomial ℤ) (n : ℕ) :
    psiNatSucc (doublePsi psi) n = C (2 : ℤ) * psiNatSucc psi n := by
  by_cases hzero : n = 0
  · simp [psiNatSucc, hzero]
  · by_cases hn : n - 1 < k
    · have hrow : psiNat (doublePsi psi) (n - 1) =
          doublePsi psi ⟨n - 1, hn⟩ := psiNat_eq (doublePsi psi) hn
      have hrow' : psiNat psi (n - 1) = psi ⟨n - 1, hn⟩ :=
          psiNat_eq psi hn
      simp [psiNatSucc, hzero, hrow, hrow', doublePsi]
    · simp [psiNatSucc, hzero, psiNat, hn]

/-- Finite-row wrapper of the natural-row type preservation theorem. -/
theorem ford_type_double_fin
    {k d : ℕ} {T : ℤ} {m : ℕ}
    (psi : Fin k → Polynomial ℤ)
    (hType : FordType k d T m (psiNatSucc psi)) :
    FordType k d T (m + 1) (psiNatSucc (doublePsi psi)) := by
  have hnat := ford_type_double_nat (psiNatSucc psi) hType
  intro j hj
  have hrow := hnat j hj
  simpa only [psiNatSucc_doublePsi] using hrow

lemma fordSourceFrequencyAt_double
    {k P : ℕ} (psi : Fin k → Polynomial ℤ)
    (z : Fin k → Fin (P + 1)) (j : Fin k) :
    fordSourceFrequencyAt (doublePsi psi) z j =
      2 * fordSourceFrequencyAt psi z j := by
  simp only [fordSourceFrequencyAt, doublePsi]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [map_mul]

end
end MAPFordFamilyDoubling

#print axioms MAPFordFamilyDoubling.ford_type_double_nat
#print axioms MAPFordFamilyDoubling.ford_type_double_fin
#print axioms MAPFordFamilyDoubling.fordSourceFrequencyAt_double
