import JutilaP53PrincipalInfiniteShift
import JutilaP53PairContourExpansion
import JutilaP53ShiftedContourBound

/-!
# Exact principal pair contour with residue
-/

namespace MAPJutilaP53PrincipalPairShiftedContour

open scoped BigOperators
open Complex MeasureTheory
open MAPJutilaP53PairRExpansion
open MAPJutilaP53PairEulerFactorization
open MAPJutilaP53DivisorKernelMultiplicative
open MAPJutilaP53PairContourExpansion
open MAPJutilaP53TwoScaleContour
open MAPJutilaP53PrincipalInfiniteShift
open MAPJutilaP53PrincipalDivisorResidueBound
open MAPJutilaP53ShiftedContourBound

noncomputable section

/-- One normalized pseudocharacter pair equals its shifted principal contour
plus the exact crossed residue. -/
theorem pairRB_eq_principal_leftHalfContours_add_residue
    {q : ℕ} [NeZero q]
    {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    {s : ℂ} (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 4)
    {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    jutilaP53PairRB M N s (1 : DirichletCharacter ℂ q) r r' =
      (((r * r' : ℕ) : ℂ)⁻¹) *
        (∑ d ∈ (r.lcm r').divisors,
          p53LeftContourTerm (1 : DirichletCharacter ℂ q) s M N r r' d) +
      (((r * r' : ℕ) : ℂ)⁻¹) *
        p53PrincipalDivisorResidue q s M N r r' := by
  rw [MAPJutilaP53PairContourExpansion.pairRB_eq_divisorKernel_rightContours
    (1 : DirichletCharacter ℂ q) hM hMN hsLo hr hr']
  rw [← mul_add]
  apply congrArg (((((r * r' : ℕ) : ℂ)⁻¹)) * ·)
  unfold p53PrincipalDivisorResidue
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdPos
  have hshift := p53TwoScale_principal_right_eq_leftHalf_add_residue
    q s (div_pos (hM.trans hMN) hdR) (div_pos hM hdR) hsLo hsHi
  have hleftComm :
      (∫ t : ℝ, p53TwoScaleContourIntegrand
        (1 : DirichletCharacter ℂ q) s (N / (d : ℝ)) (M / (d : ℝ))
        (((-(1 / 2 : ℝ)) : ℂ) + t * I)) =
      (∫ t : ℝ, p53TwoScaleContourIntegrand
        (1 : DirichletCharacter ℂ q) s (N / (d : ℝ)) (M / (d : ℝ))
        (((-(1 / 2 : ℝ)) : ℂ) + I * t)) := by
    apply integral_congr_ae
    filter_upwards [] with t
    congr 2
    ring
  rw [hleftComm] at hshift
  unfold p53LeftContourTerm
  rw [hshift]
  push_cast
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  field_simp [hpi]

end
end MAPJutilaP53PrincipalPairShiftedContour

#print axioms MAPJutilaP53PrincipalPairShiftedContour.pairRB_eq_principal_leftHalfContours_add_residue
