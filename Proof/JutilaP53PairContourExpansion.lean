import JutilaP53FiniteFubiniReindex
import JutilaP53MellinContourWeld

/-!
# One p.53 pseudocharacter pair as a finite sum of movable contours

This is the exact source seam immediately before the contour displacement.
The divisor kernel is finite, so inserting the two-scale Mellin contour costs
no infinite-sum/integral interchange.
-/

namespace MAPJutilaP53PairContourExpansion

open scoped BigOperators
open Complex MeasureTheory
open MAPJutilaP53PairRExpansion
open MAPJutilaP53PairEulerFactorization
open MAPJutilaP53DivisorKernelMultiplicative
open MAPJutilaP53FiniteFubiniReindex
open MAPJutilaP53InnerMellinRightLine
open MAPJutilaP53TwoScaleContour
open MAPJutilaP53MellinContourWeld

noncomputable section

/-- Exact finite outer Euler sum of right-line two-scale contours. -/
theorem pairRB_eq_divisorKernel_rightContours
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    {s : ℂ} (hs : 0 ≤ s.re) {r r' : ℕ}
    (hr : Squarefree r) (hr' : Squarefree r') :
    jutilaP53PairRB M N s chi r r' =
      (((r * r' : ℕ) : ℂ)⁻¹) *
        ∑ d ∈ (r.lcm r').divisors,
          LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d *
            ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
              ∫ v : ℝ,
                p53TwoScaleContourIntegrand chi s
                  (N / (d : ℝ)) (M / (d : ℝ))
                  (((1 : ℝ) : ℂ) + v * I))) := by
  rw [pairRB_eq_divisorKernel_innerTwoScale chi hM hMN hs hr hr']
  apply congrArg (((((r * r' : ℕ) : ℂ)⁻¹)) * ·)
  apply Finset.sum_congr rfl
  intro d hd
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
  have hN : 0 < N := hM.trans hMN
  rw [p53InnerTwoScale_eq_rightContour chi hs
    (div_pos hN (by exact_mod_cast hdPos))
    (div_pos hM (by exact_mod_cast hdPos))]

end

end MAPJutilaP53PairContourExpansion

#print axioms MAPJutilaP53PairContourExpansion.pairRB_eq_divisorKernel_rightContours
