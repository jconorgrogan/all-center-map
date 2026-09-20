import FordTypeCenteredDifference
import FordP16FiniteFourierBridge
import FordP16Source35Triangular

open scoped BigOperators
open MAPFordType
open MAPFordP16FiniteFourierBridge
open MAPFordP16Source35Triangular
namespace MAPFordDifferenceFamily
noncomputable section

/-- Apply the centered finite difference rowwise to a finite polynomial family. -/
def differencePsi {k : ℕ} (psi : Fin k → Polynomial ℤ) (h : ℤ) :
    Fin k → Polynomial ℤ :=
  fun j => centeredFiniteDifference (psi j) h

lemma psiNatSucc_differencePsi
    {k : ℕ} (psi : Fin k → Polynomial ℤ) (h : ℤ) :
    psiNatSucc (differencePsi psi h) =
      (fun n => centeredFiniteDifference (psiNatSucc psi n) h) := by
  funext n
  by_cases hn : n = 0
  · simp [hn, psiNatSucc, differencePsi, centeredFiniteDifference]
  · by_cases hnk : n - 1 < k
    · simp [psiNatSucc, differencePsi, hn, hnk, psiNat]
    · simp [psiNatSucc, differencePsi, hn, hnk, psiNat, centeredFiniteDifference]

/-- The centered finite difference preserves Ford's exact row type, with
scale `T` replaced by `h*T`; the wrapper `psiNatSucc` is handled literally. -/
theorem ford_type_differencePsi
    {k d : ℕ} {T : ℤ} {m : ℕ}
    (psi : Fin k → Polynomial ℤ)
    (hpsi : FordType k d T m (psiNatSucc psi))
    (h : ℤ) (hh : 0 < h) :
    FordType k (d + 1) (h * T) m (psiNatSucc (differencePsi psi h)) := by
  rw [psiNatSucc_differencePsi]
  exact ford_type_centered_difference k d T m (psiNatSucc psi) hpsi h hh

lemma centered_difference_eval_sub
    (p : Polynomial ℤ) (h z : ℤ) :
    (centeredFiniteDifference p h).eval z =
      p.eval (z + h) - p.eval z - (p.eval h - p.eval 0) := by
  simp [centeredFiniteDifference]

lemma centered_source_frequency_formula
    {k P : ℕ} (psi : Fin k → Polynomial ℤ) (h : ℤ)
    (z : Fin k → Fin (P + 1)) (j : Fin k) :
    fordSourceFrequencyAt (differencePsi psi h) z j =
      (∑ i : Fin k, (psi j).eval (((z i).val : ℤ) + h)) -
        fordSourceFrequencyAt psi z j -
        (k : ℤ) * ((psi j).eval h - (psi j).eval 0) := by
  simp only [fordSourceFrequencyAt, differencePsi, centered_difference_eval_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Pairwise source-frequency differences of centered rows equal the
uncentered translated differences: the constant centering term cancels. -/
theorem centered_source_frequency_pair_difference
    {k P : ℕ} (psi : Fin k → Polynomial ℤ) (h : ℤ)
    (z w : Fin k → Fin (P + 1)) (j : Fin k) :
    fordSourceFrequencyAt (differencePsi psi h) z j -
        fordSourceFrequencyAt (differencePsi psi h) w j =
      ((∑ i : Fin k, (psi j).eval (((z i).val : ℤ) + h)) -
          fordSourceFrequencyAt psi z j) -
        ((∑ i : Fin k, (psi j).eval (((w i).val : ℤ) + h)) -
          fordSourceFrequencyAt psi w j) := by
  rw [centered_source_frequency_formula, centered_source_frequency_formula]
  ring

lemma natAbs_step_le
    {P : ℕ} {h : ℤ} (hh1 : (1 : ℤ) ≤ h) (hhP : h ≤ (P : ℤ)) :
    h.natAbs ≤ P := by
  have hnonneg : (0 : ℤ) ≤ h := by omega
  have hcast : (h.natAbs : ℤ) ≤ (P : ℤ) := by
    simpa [Int.natAbs_of_nonneg hnonneg] using hhP
  exact_mod_cast hcast

lemma natAbs_scaled_step_le
    {P d : ℕ} {T h : ℤ}
    (hTsize : T.natAbs ≤ P ^ d)
    (hh1 : (1 : ℤ) ≤ h) (hhP : h ≤ (P : ℤ)) :
    (h * T).natAbs ≤ P ^ (d + 1) := by
  rw [Int.natAbs_mul]
  have hhsize : h.natAbs ≤ P := natAbs_step_le hh1 hhP
  calc
    h.natAbs * T.natAbs ≤ P * P ^ d :=
      Nat.mul_le_mul hhsize hTsize
    _ = P ^ (d + 1) := by rw [pow_succ]; ring

lemma scaled_step_ne_zero
    {T h : ℤ} (hT : T ≠ 0) (hh : 0 < h) : h * T ≠ 0 := by
  exact mul_ne_zero (by omega) hT

end
end MAPFordDifferenceFamily

#print axioms MAPFordDifferenceFamily.ford_type_differencePsi
#print axioms MAPFordDifferenceFamily.centered_source_frequency_formula
#print axioms MAPFordDifferenceFamily.centered_source_frequency_pair_difference
#print axioms MAPFordDifferenceFamily.natAbs_scaled_step_le
