import JutilaP53KernelSourceForm
import JutilaP53PairRExpansion
import JutilaP53PairShiftedContour

/-!
# Off-character p.53 kernel on the shifted contour

This file lifts the one-pair contour identity to the literal row kernel.  It
keeps the finite selected squarefree `r`-set and the row character labels
visible, so the principal/same-character sector is not accidentally erased.
-/

namespace MAPJutilaP53OffCharacterKernelShift

open scoped BigOperators
open Complex MeasureTheory
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53KernelExpansion
open MAPJutilaP53KernelSourceForm
open MAPJutilaP53PairRExpansion
open MAPJutilaP53PairEulerFactorization
open MAPJutilaP53DivisorKernelMultiplicative
open MAPJutilaP53TwoScaleContour
open MAPJutilaP53PairShiftedContour

noncomputable section

/-- Exact shifted-line formula for a row pair carrying different character
labels.  The collar width `epsilon≤1/4` is used only to keep
`0≤Re(pairShift)≤1/2`. -/
theorem jutilaP53Kernel_eq_offCharacter_leftHalfContours
    {q R : ℕ} [NeZero q] {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 R) (hSq : ∀ r ∈ S, Squarefree r)
    {alpha epsilon M N : ℝ} (hepsilonHi : epsilon ≤ 1 / 4)
    (hM : 0 < M) (hMN : M < N)
    (i j : JutilaP53Row q)
    (hiLo : alpha ≤ i.zero.re) (hiHi : i.zero.re ≤ alpha + epsilon)
    (hjLo : alpha ≤ j.zero.re) (hjHi : j.zero.re ≤ alpha + epsilon)
    (hchar : i.character ≠ j.character) :
    jutilaP53Kernel S alpha M N i j =
      ∑ r ∈ S, ∑ r' ∈ S,
        (((r * r' : ℕ) : ℂ)⁻¹) *
          ∑ d ∈ (r.lcm r').divisors,
            LSeries.term
                (p53TwistedDivisorKernel (jutilaP53PairCharacter i j) r r')
                (1 + jutilaP53PairShift alpha i j) d *
              ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
                ∫ v : ℝ,
                  p53TwoScaleContourIntegrand
                    (jutilaP53PairCharacter i j)
                    (jutilaP53PairShift alpha i j)
                    (N / (d : ℝ)) (M / (d : ℝ))
                    (((-(1 / 2 : ℝ)) : ℂ) + v * I))) := by
  have hsMem := pairShift_re_mem_Icc hiLo hiHi hjLo hjHi
  have hsLo : 0 ≤ (jutilaP53PairShift alpha i j).re := hsMem.1
  have hsHi : (jutilaP53PairShift alpha i j).re ≤ 1 / 2 := by
    calc
      _ ≤ 2 * epsilon := hsMem.2
      _ ≤ 1 / 2 := by linarith
  have hpairNonprincipal : jutilaP53PairCharacter i j ≠ 1 := by
    intro h
    exact hchar ((pairCharacter_eq_one_iff i j).mp h)
  rw [jutilaP53Kernel_eq_sourceB]
  rw [jutilaP53SourceB_eq_pairR_doubleSum hS hM hMN hsLo]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro r' hr'
  exact pairRB_eq_divisorKernel_leftHalfContours_nonprincipal
    (jutilaP53PairCharacter i j) hpairNonprincipal hM hMN hsLo hsHi
    (hSq r hr) (hSq r' hr')

end

end MAPJutilaP53OffCharacterKernelShift

#print axioms MAPJutilaP53OffCharacterKernelShift.jutilaP53Kernel_eq_offCharacter_leftHalfContours
