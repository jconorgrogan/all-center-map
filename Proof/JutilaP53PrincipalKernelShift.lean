import JutilaP53PrincipalShiftedContourBound
import JutilaP53KernelSourceForm

/-!
# Principal same-character row kernel after contour shift
-/

namespace MAPJutilaP53PrincipalKernelShift

open scoped BigOperators
open Complex
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53KernelExpansion
open MAPJutilaP53KernelSourceForm
open MAPJutilaP53PairRExpansion
open MAPJutilaP53ShiftedContourBound
open MAPJutilaP53PrincipalPairShiftedContour
open MAPJutilaP53PrincipalDivisorResidueBound
open MAPJutilaP53PrincipalRResidueAggregation
open MAPJutilaP53PrincipalShiftedContourBound
open MAPJutilaP53LeftLineEstimate

noncomputable section

/-- Exact same-character row-kernel decomposition into the principal left
contour and the crossed residue. -/
theorem jutilaP53Kernel_eq_principalLeftBranch_add_residue
    {q R : ℕ} [NeZero q] {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 R) (hSq : ∀ r ∈ S, Squarefree r)
    {alpha epsilon M N : ℝ} (hepsilonHi : epsilon ≤ 1 / 8)
    (hM : 0 < M) (hMN : M < N)
    (i j : JutilaP53Row q)
    (hiLo : alpha ≤ i.zero.re) (hiHi : i.zero.re ≤ alpha + epsilon)
    (hjLo : alpha ≤ j.zero.re) (hjHi : j.zero.re ≤ alpha + epsilon)
    (hchar : i.character = j.character) :
    jutilaP53Kernel S alpha M N i j =
      (∑ r ∈ S, ∑ r' ∈ S,
        (((r * r' : ℕ) : ℂ)⁻¹) *
          ∑ d ∈ (r.lcm r').divisors,
            p53LeftContourTerm (1 : DirichletCharacter ℂ q)
              (jutilaP53PairShift alpha i j) M N r r' d) +
      p53PrincipalRResidue q S (jutilaP53PairShift alpha i j) M N := by
  have hsMem := pairShift_re_mem_Icc hiLo hiHi hjLo hjHi
  have hsLo : 0 ≤ (jutilaP53PairShift alpha i j).re := hsMem.1
  have hsHi : (jutilaP53PairShift alpha i j).re ≤ 1 / 4 := by
    calc
      _ ≤ 2 * epsilon := hsMem.2
      _ ≤ 1 / 4 := by linarith
  rw [jutilaP53Kernel_eq_sourceB]
  have hpchar : jutilaP53PairCharacter i j = 1 :=
    (pairCharacter_eq_one_iff i j).mpr hchar
  rw [hpchar]
  rw [jutilaP53SourceB_eq_pairR_doubleSum hS hM hMN hsLo]
  calc
    _ = ∑ r ∈ S, ∑ r' ∈ S, (
        (((r * r' : ℕ) : ℂ)⁻¹) *
          (∑ d ∈ (r.lcm r').divisors,
            p53LeftContourTerm (1 : DirichletCharacter ℂ q)
              (jutilaP53PairShift alpha i j) M N r r' d) +
        (((r * r' : ℕ) : ℂ)⁻¹) *
          p53PrincipalDivisorResidue q
            (jutilaP53PairShift alpha i j) M N r r') := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro r' hr'
      exact pairRB_eq_principal_leftHalfContours_add_residue hM hMN
        hsLo hsHi (hSq r hr) (hSq r' hr')
    _ = _ := by
      unfold p53PrincipalRResidue
      simp_rw [Finset.sum_add_distrib]

set_option maxHeartbeats 600000 in
/-- Norm form, still retaining the exact residue for later same-character
fiber cancellation. -/
theorem norm_jutilaP53Kernel_principal_le_leftBudget_add_residue
    {q R : ℕ} [NeZero q] {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 R) (hSq : ∀ r ∈ S, Squarefree r)
    {alpha epsilon M N : ℝ} (hepsilonHi : epsilon ≤ 1 / 8)
    (hM : 0 < M) (hMN : M < N)
    (i j : JutilaP53Row q)
    (hiLo : alpha ≤ i.zero.re) (hiHi : i.zero.re ≤ alpha + epsilon)
    (hjLo : alpha ≤ j.zero.re) (hjHi : j.zero.re ≤ alpha + epsilon)
    (hchar : i.character = j.character) :
    ‖jutilaP53Kernel S alpha M N i j‖ ≤
      p53PrincipalShiftedAnalyticFactor q (jutilaP53PairShift alpha i j) *
        p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) *
          p53NormalizedEulerMass S +
      ‖p53PrincipalRResidue q S
        (jutilaP53PairShift alpha i j) M N‖ := by
  let A : ℂ := ∑ r ∈ S, ∑ r' ∈ S,
    (((r * r' : ℕ) : ℂ)⁻¹) *
      ∑ d ∈ (r.lcm r').divisors,
        p53LeftContourTerm (1 : DirichletCharacter ℂ q)
          (jutilaP53PairShift alpha i j) M N r r' d
  let Z : ℂ := p53PrincipalRResidue q S
    (jutilaP53PairShift alpha i j) M N
  have heq : jutilaP53Kernel S alpha M N i j = A + Z := by
    simpa [A, Z] using jutilaP53Kernel_eq_principalLeftBranch_add_residue
      hS hSq hepsilonHi hM hMN i j hiLo hiHi hjLo hjHi hchar
  have hsMem := pairShift_re_mem_Icc hiLo hiHi hjLo hjHi
  have hsHi : (jutilaP53PairShift alpha i j).re ≤ 1 / 4 :=
    hsMem.2.trans (by linarith)
  have hA : ‖A‖ ≤
      p53PrincipalShiftedAnalyticFactor q (jutilaP53PairShift alpha i j) *
        p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) *
          p53NormalizedEulerMass S := by
    simpa [A] using norm_principalNormalizedLeftBranch_le
      (q := q) (S := S) (s := jutilaP53PairShift alpha i j)
      (M := M) (N := N) hSq hM hMN hsMem.1 hsHi
  rw [heq]
  exact (norm_add_le A Z).trans (by simpa [Z] using add_le_add hA (le_refl ‖Z‖))

end
end MAPJutilaP53PrincipalKernelShift

#print axioms MAPJutilaP53PrincipalKernelShift.jutilaP53Kernel_eq_principalLeftBranch_add_residue
#print axioms MAPJutilaP53PrincipalKernelShift.norm_jutilaP53Kernel_principal_le_leftBudget_add_residue
