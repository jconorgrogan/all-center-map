import JutilaP53PairContourExpansion
import JutilaP53InfiniteShift

/-!
# Exact shifted-contour form of one nonprincipal p.53 pair

This is the arithmetic-to-left-line identity after the finite divisor-kernel
reindex.  The outer sum remains finite, so no additional Fubini theorem is
needed.
-/

namespace MAPJutilaP53PairShiftedContour

open scoped BigOperators
open Complex MeasureTheory
open MAPJutilaP53PairRExpansion
open MAPJutilaP53PairEulerFactorization
open MAPJutilaP53DivisorKernelMultiplicative
open MAPJutilaP53FiniteFubiniReindex
open MAPJutilaP53PairContourExpansion
open MAPJutilaP53TwoScaleContour
open MAPJutilaP53InfiniteShift
open MAPJutilaP53LeftLineEstimate
open RamachandraShiftedGammaPoleContour

noncomputable section

/-- Literal p.53 pair component on the shifted line `Re w=-1/2`. -/
theorem pairRB_eq_divisorKernel_leftHalfContours_nonprincipal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    {s : ℂ} (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 2)
    {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    jutilaP53PairRB M N s chi r r' =
      (((r * r' : ℕ) : ℂ)⁻¹) *
        ∑ d ∈ (r.lcm r').divisors,
          LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d *
            ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
              ∫ v : ℝ,
                p53TwoScaleContourIntegrand chi s
                  (N / (d : ℝ)) (M / (d : ℝ))
                  (((-(1 / 2 : ℝ)) : ℂ) + v * I))) := by
  rw [MAPJutilaP53PairContourExpansion.pairRB_eq_divisorKernel_rightContours
    chi hM hMN hsLo hr hr']
  apply congrArg (((((r * r' : ℕ) : ℂ)⁻¹)) * ·)
  apply Finset.sum_congr rfl
  intro d hd
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
  have hN : 0 < N := hM.trans hMN
  rw [p53TwoScale_right_eq_leftHalf chi hchi s
    (div_pos hN (by exact_mod_cast hdPos))
    (div_pos hM (by exact_mod_cast hdPos)) hsLo hsHi]

/-- The exact finite arithmetic mass left after the universal vertical-line
estimate.  Attaching Jutila's Euler-product bound to this object is the next
purely arithmetic step. -/
def p53ShiftedDivisorMass
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ)
    (M N : ℝ) (r r' : ℕ) : ℝ :=
  ∑ d ∈ (r.lcm r').divisors,
    ‖LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d‖ *
      p53CpowEndpointBound (N / (d : ℝ)) (M / (d : ℝ))
        (-(1 / 2)) (-(1 / 2))

theorem p53ShiftedDivisorMass_nonneg
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    (r r' : ℕ) :
    0 ≤ p53ShiftedDivisorMass chi s M N r r' := by
  unfold p53ShiftedDivisorMass
  apply Finset.sum_nonneg
  intro d hd
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
  exact mul_nonneg (norm_nonneg _)
    (p53CpowEndpointBound_nonneg
      (div_pos (hM.trans hMN) (by exact_mod_cast hdPos))
      (div_pos hM (by exact_mod_cast hdPos)) _ _)

end

end MAPJutilaP53PairShiftedContour

#print axioms MAPJutilaP53PairShiftedContour.pairRB_eq_divisorKernel_leftHalfContours_nonprincipal
