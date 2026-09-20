import JutilaP53SharpResidueAggregation

namespace MAPJutilaP53SharpPairSectors
open scoped BigOperators ComplexConjugate
open Complex
open CGLProofDAG
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53KernelExpansion
open MAPJutilaP53KernelSourceForm
open MAPJutilaP53LeftLineEstimate
open MAPJutilaP53ShiftedContourBound
open MAPJutilaP53PrincipalRResidueAggregation
open MAPJutilaP53PrincipalDiagonalResidue
open MAPJutilaP53OffCharacterKernelBound
open MAPJutilaP53PrincipalKernelShift
open MAPJutilaP53PrincipalShiftedContourBound
open MAPJutilaOneSeparatedExponentialPacking

noncomputable section

open MAPJutilaP53PairSectorAggregation

set_option maxHeartbeats 800000 in
/-- Source-faithful pointwise p.53 correlation bound after aggregating every
row-pair sector.  No scale supremum and no rectangle-area loss has yet been
taken. -/
theorem jutilaP53CorrelationEnergy_le_sharpPairSectors
    {q R : ℕ} [NeZero q] (rows : Finset (JutilaP53Row q))
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    (hSq : ∀ r ∈ S, Squarefree r)
    {alpha epsilon M N : ℝ} (hepsilonHi : epsilon ≤ 1 / 8)
    (hM : 1 ≤ M) (hMN : M < N)
    (hcop : ∀ r ∈ S, r.Coprime q)
    (hrows : ∀ row ∈ rows,
      alpha ≤ row.zero.re ∧ row.zero.re ≤ alpha + epsilon)
    (hfiberSep : ∀ chi : DirichletCharacter ℂ q,
      OneSeparated ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)))
    (hfiberCard : ∀ chi : DirichletCharacter ℂ q,
      ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)).card =
      (rows.filter (fun row => row.character = chi)).card)
    (eta : JutilaP53Row q → ℂ)
    (heta : ∀ row ∈ rows, ‖eta row‖ = 1) :
    jutilaP53CorrelationEnergy rows S alpha M N eta ≤
      (∑ i ∈ rows, ∑ j ∈ rows, p53AnalyticPairBudget S alpha M N i j) +
      (rows.card : ℝ) *
        ((12 * (Real.log N - Real.log M) +
            48 * Real.exp 1 * integerExponentialMass) *
          (harmonic R : ℝ)) := by
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have henergy0 : 0 ≤ jutilaP53CorrelationEnergy rows S alpha M N eta := by
    unfold jutilaP53CorrelationEnergy
    exact tsum_nonneg fun n => mul_nonneg
      (jutilaP53CorrelationWeight_nonneg S hMpos hMN n) (sq_nonneg _)
  have hexpand := jutilaP53CorrelationEnergy_eq_doubleSum rows hS hMpos hMN eta
    (fun row hr => (hrows row hr).1) heta
  calc
    jutilaP53CorrelationEnergy rows S alpha M N eta =
        ‖(jutilaP53CorrelationEnergy rows S alpha M N eta : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg henergy0]
    _ = ‖∑ i ∈ rows, ∑ j ∈ rows,
        conj (eta i) * eta j * jutilaP53Kernel S alpha M N i j‖ := by
      rw [hexpand]
    _ ≤ ∑ i ∈ rows, ∑ j ∈ rows,
        ‖conj (eta i) * eta j * jutilaP53Kernel S alpha M N i j‖ := by
      exact (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun i hi => norm_sum_le _ _)
    _ = ∑ i ∈ rows, ∑ j ∈ rows,
        ‖jutilaP53Kernel S alpha M N i j‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp [heta i hi, heta j hj]
    _ ≤ ∑ i ∈ rows, ∑ j ∈ rows,
        (p53AnalyticPairBudget S alpha M N i j +
          if i.character = j.character then
            ‖p53PrincipalRResidue q S
              (jutilaP53PairShift alpha i j) M N‖ else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hc : i.character = j.character
      · simpa [p53AnalyticPairBudget, hc] using
          norm_jutilaP53Kernel_principal_le_leftBudget_add_residue
            hS hSq hepsilonHi hMpos hMN i j
            (hrows i hi).1 (hrows i hi).2
            (hrows j hj).1 (hrows j hj).2 hc
      · simpa [p53AnalyticPairBudget, hc] using
          norm_jutilaP53Kernel_offCharacter_le hS hSq
            (hepsilonHi.trans (by norm_num)) hMpos hMN i j
            (hrows i hi).1 (hrows i hi).2
            (hrows j hj).1 (hrows j hj).2 hc
    _ = (∑ i ∈ rows, ∑ j ∈ rows,
          p53AnalyticPairBudget S alpha M N i j) +
        (∑ i ∈ rows, ∑ j ∈ rows,
          if i.character = j.character then
            ‖p53PrincipalRResidue q S
              (jutilaP53PairShift alpha i j) M N‖ else 0) := by
      simp_rw [Finset.sum_add_distrib]
    _ ≤ (∑ i ∈ rows, ∑ j ∈ rows,
          p53AnalyticPairBudget S alpha M N i j) +
        (rows.card : ℝ) *
          ((12 * (Real.log N - Real.log M) +
              48 * Real.exp 1 * integerExponentialMass) *
            (harmonic R : ℝ)) := by
      exact add_le_add (le_refl _)
        (MAPJutilaP53SharpResidueAggregation.sum_sameCharacter_norm_p53PrincipalRResidue_le_harmonic
          q rows hS hSq hcop hM hMN.le (by linarith) hrows hfiberSep hfiberCard)

end
end MAPJutilaP53SharpPairSectors
#print axioms MAPJutilaP53SharpPairSectors.jutilaP53CorrelationEnergy_le_sharpPairSectors
