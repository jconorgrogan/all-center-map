import JutilaP53OffCharacterKernelShift
import JutilaP53ShiftedContourBound
import JutilaP53DivisorKernelAbsoluteMass
import JutilaP53PrincipalRResidueAggregation

/-!
# Complete normalized off-character p.53 kernel envelope

This sums the shifted-contour estimate through the actual finite selected
`r,r'` system and keeps the exact normalized Euler mass visible.
-/

namespace MAPJutilaP53OffCharacterKernelBound

open scoped BigOperators
open Complex
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53KernelExpansion
open MAPJutilaP53KernelSourceForm
open MAPJutilaP53PairRExpansion
open MAPJutilaP53ShiftedContourBound
open MAPJutilaP53DivisorKernelAbsoluteMass
open MAPJutilaP53LeftLineEstimate
open MAPJutilaP53PrincipalRResidueAggregation

noncomputable section

set_option maxHeartbeats 600000 in
/-- Exact off-character row-pair envelope after the full normalized
pseudocharacter sum. -/
theorem norm_jutilaP53Kernel_offCharacter_le
    {q R : ℕ} [NeZero q] {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 R) (hSq : ∀ r ∈ S, Squarefree r)
    {alpha epsilon M N : ℝ} (hepsilonHi : epsilon ≤ 1 / 4)
    (hM : 0 < M) (hMN : M < N)
    (i j : JutilaP53Row q)
    (hiLo : alpha ≤ i.zero.re) (hiHi : i.zero.re ≤ alpha + epsilon)
    (hjLo : alpha ≤ j.zero.re) (hjHi : j.zero.re ≤ alpha + epsilon)
    (hchar : i.character ≠ j.character) :
    ‖jutilaP53Kernel S alpha M N i j‖ ≤
      p53ShiftedAnalyticFactor q (jutilaP53PairShift alpha i j) *
        p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) *
          p53NormalizedEulerMass S := by
  have hsMem := pairShift_re_mem_Icc hiLo hiHi hjLo hjHi
  have hsLo : 0 ≤ (jutilaP53PairShift alpha i j).re := hsMem.1
  have hsHi : (jutilaP53PairShift alpha i j).re ≤ 1 / 2 :=
    hsMem.2.trans (by linarith)
  have hpairNonprincipal : jutilaP53PairCharacter i j ≠ 1 := by
    intro h
    exact hchar ((pairCharacter_eq_one_iff i j).mp h)
  rw [jutilaP53Kernel_eq_sourceB]
  rw [jutilaP53SourceB_eq_pairR_doubleSum hS hM hMN hsLo]
  calc
    _ ≤ ∑ r ∈ S, ∑ r' ∈ S,
        ‖jutilaP53PairRB M N (jutilaP53PairShift alpha i j)
          (jutilaP53PairCharacter i j) r r'‖ := by
      exact (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun r hr => norm_sum_le _ _)
    _ ≤ ∑ r ∈ S, ∑ r' ∈ S,
        (((r * r' : ℕ) : ℝ)⁻¹) *
          p53ShiftedAnalyticFactor q (jutilaP53PairShift alpha i j) *
          (p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) *
            (MAPJutilaLemma3AbsoluteMass.lemmaThreeAbsoluteMass
              r.primeFactors r'.primeFactors : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro r' hr'
      have hpair := norm_pairRB_le_shiftedDivisorMass_nonprincipal
        (jutilaP53PairCharacter i j) hpairNonprincipal hM hMN hsLo hsHi
        (hSq r hr) (hSq r' hr')
      have hmass := p53ShiftedDivisorMass_le_lemmaThreeAbsoluteMass
        (jutilaP53PairCharacter i j) hM (hM.trans hMN) hsLo
        (hSq r hr) (hSq r' hr')
      calc
        _ ≤ (((r * r' : ℕ) : ℝ)⁻¹) *
            p53ShiftedAnalyticFactor q (jutilaP53PairShift alpha i j) *
              p53ShiftedDivisorMass (jutilaP53PairCharacter i j)
                (jutilaP53PairShift alpha i j) M N r r' := hpair
        _ ≤ (((r * r' : ℕ) : ℝ)⁻¹) *
            p53ShiftedAnalyticFactor q (jutilaP53PairShift alpha i j) *
              (p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) *
                (MAPJutilaLemma3AbsoluteMass.lemmaThreeAbsoluteMass
                  r.primeFactors r'.primeFactors : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hmass
          exact mul_nonneg (by positivity)
            (p53ShiftedAnalyticFactor_nonneg q
              (jutilaP53PairShift alpha i j))
    _ = p53ShiftedAnalyticFactor q (jutilaP53PairShift alpha i j) *
        p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) *
          p53NormalizedEulerMass S := by
      unfold p53NormalizedEulerMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r' hr'
      ring

end
end MAPJutilaP53OffCharacterKernelBound

#print axioms MAPJutilaP53OffCharacterKernelBound.norm_jutilaP53Kernel_offCharacter_le
