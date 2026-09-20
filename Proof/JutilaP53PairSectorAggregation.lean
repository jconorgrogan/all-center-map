import JutilaP53KernelExpansion
import JutilaP53OffCharacterKernelBound
import JutilaP53PrincipalKernelShift
import JutilaP53PrincipalDiagonalResidue

/-!
# Aggregation of the p.53 pair sectors

This file combines the exact pair-kernel expansion with the shifted-contour
bounds.  It preserves the same-character residue as a linear fiber budget and
keeps the two analytic contour sectors as an explicit finite double sum.
-/

namespace MAPJutilaP53PairSectorAggregation

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

/-- The exact contour budget for a row pair, retaining the distinct principal
and nonprincipal analytic factors. -/
def p53AnalyticPairBudget {q : ℕ} (S : Finset ℕ)
    (alpha M N : ℝ) (i j : JutilaP53Row q) : ℝ := by
  classical
  exact (if i.character = j.character then
      p53PrincipalShiftedAnalyticFactor q (jutilaP53PairShift alpha i j)
    else p53ShiftedAnalyticFactor q (jutilaP53PairShift alpha i j)) *
    p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) *
    p53NormalizedEulerMass S

/-- The total absolute mass of the same-character normalized residue sector is
linear in the number of selected rows.  The diagonal logarithmic quotient is
paid once, and one-separated packing pays every other zero in its character
fiber. -/
theorem sum_sameCharacter_norm_p53PrincipalRResidue_le
    (q : ℕ) [NeZero q] (rows : Finset (JutilaP53Row q))
    {S : Finset ℕ} {alpha epsilon M N : ℝ}
    (hSq : ∀ r ∈ S, Squarefree r)
    (hscale : ∀ r ∈ S, ∀ r' ∈ S, ((r.lcm r' : ℕ) : ℝ) ≤ M)
    (hMN : M ≤ N) (heps : 2 * epsilon ≤ 1 / 2)
    (hrows : ∀ row ∈ rows,
      alpha ≤ row.zero.re ∧ row.zero.re ≤ alpha + epsilon)
    (hfiberSep : ∀ chi : DirichletCharacter ℂ q,
      OneSeparated ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)))
    (hfiberCard : ∀ chi : DirichletCharacter ℂ q,
      ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)).card =
      (rows.filter (fun row => row.character = chi)).card) :
    (∑ i ∈ rows, ∑ j ∈ rows,
      if i.character = j.character then
        ‖p53PrincipalRResidue q S (jutilaP53PairShift alpha i j) M N‖
      else 0) ≤
      (rows.card : ℝ) *
        ((12 * (Real.log N - Real.log M) +
            48 * Real.exp 1 * integerExponentialMass) *
          p53NormalizedEulerMass S) := by
  classical
  let K := (12 * (Real.log N - Real.log M) +
      48 * Real.exp 1 * integerExponentialMass) *
    p53NormalizedEulerMass S
  calc
    (∑ i ∈ rows, ∑ j ∈ rows,
        if i.character = j.character then
          ‖p53PrincipalRResidue q S
            (jutilaP53PairShift alpha i j) M N‖ else 0) ≤
        ∑ _i ∈ rows, K := by
      apply Finset.sum_le_sum
      intro i hi
      dsimp only [K]
      let fiber := rows.filter (fun row => row.character = i.character)
      let C : JutilaP53Row q → ℝ := fun j =>
        ‖p53PrincipalRResidue q S (jutilaP53PairShift alpha i j) M N‖
      have hiFiber : i ∈ fiber := by simp [fiber, hi]
      have hsumEq :
          (∑ j ∈ rows, if i.character = j.character then C j else 0) =
            ∑ j ∈ fiber, C j := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext j
          simp [fiber, eq_comm]
        · intro j hj
          rfl
      have hsplit := Finset.sum_erase_add fiber C hiFiber
      have hoff : ∑ j ∈ fiber.erase i, C j ≤
          48 * Real.exp 1 * integerExponentialMass * p53NormalizedEulerMass S := by
        have hbound := sum_p53PrincipalRResidue_offDiagonal_le q rows
          i.character i hSq hscale hMN heps hrows hi rfl
          (hfiberSep i.character) (hfiberCard i.character)
        have herase : fiber.erase i = fiber.filter (fun j => j ≠ i) := by
          ext j
          simp [and_comm]
        rw [herase]
        simpa [fiber, C] using hbound
      have hdiag : C i ≤
          12 * (Real.log N - Real.log M) * p53NormalizedEulerMass S := by
        simpa [C] using norm_p53PrincipalRResidue_pairShift_self_le q i hSq
          hscale hMN (hrows i hi).1 (hrows i hi).2 heps
      rw [hsumEq]
      calc
        (∑ j ∈ fiber, C j) = C i + ∑ j ∈ fiber.erase i, C j := by
          rw [add_comm]
          exact hsplit.symm
        _ ≤ 12 * (Real.log N - Real.log M) * p53NormalizedEulerMass S +
            48 * Real.exp 1 * integerExponentialMass *
              p53NormalizedEulerMass S := add_le_add hdiag hoff
        _ = (12 * (Real.log N - Real.log M) +
                48 * Real.exp 1 * integerExponentialMass) *
              p53NormalizedEulerMass S := by ring
    _ = (rows.card : ℝ) *
        ((12 * (Real.log N - Real.log M) +
            48 * Real.exp 1 * integerExponentialMass) *
          p53NormalizedEulerMass S) := by simp [K]

set_option maxHeartbeats 800000 in
/-- Source-faithful pointwise p.53 correlation bound after aggregating every
row-pair sector.  No scale supremum and no rectangle-area loss has yet been
taken. -/
theorem jutilaP53CorrelationEnergy_le_pairSectors
    {q R : ℕ} [NeZero q] (rows : Finset (JutilaP53Row q))
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    (hSq : ∀ r ∈ S, Squarefree r)
    {alpha epsilon M N : ℝ} (hepsilonHi : epsilon ≤ 1 / 8)
    (hM : 0 < M) (hMN : M < N)
    (hscale : ∀ r ∈ S, ∀ r' ∈ S, ((r.lcm r' : ℕ) : ℝ) ≤ M)
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
          p53NormalizedEulerMass S) := by
  have henergy0 : 0 ≤ jutilaP53CorrelationEnergy rows S alpha M N eta := by
    unfold jutilaP53CorrelationEnergy
    exact tsum_nonneg fun n => mul_nonneg
      (jutilaP53CorrelationWeight_nonneg S hM hMN n) (sq_nonneg _)
  have hexpand := jutilaP53CorrelationEnergy_eq_doubleSum rows hS hM hMN eta
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
            hS hSq hepsilonHi hM hMN i j
            (hrows i hi).1 (hrows i hi).2
            (hrows j hj).1 (hrows j hj).2 hc
      · simpa [p53AnalyticPairBudget, hc] using
          norm_jutilaP53Kernel_offCharacter_le hS hSq
            (hepsilonHi.trans (by norm_num)) hM hMN i j
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
            p53NormalizedEulerMass S) := by
      exact add_le_add (le_refl _)
        (sum_sameCharacter_norm_p53PrincipalRResidue_le q rows hSq
          hscale hMN.le (by linarith) hrows hfiberSep hfiberCard)

end
end MAPJutilaP53PairSectorAggregation

#print axioms MAPJutilaP53PairSectorAggregation.sum_sameCharacter_norm_p53PrincipalRResidue_le
#print axioms MAPJutilaP53PairSectorAggregation.jutilaP53CorrelationEnergy_le_pairSectors
