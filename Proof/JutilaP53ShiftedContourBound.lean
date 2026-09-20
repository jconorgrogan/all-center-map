import JutilaP53PairShiftedContour

/-!
# Quantitative bound for the shifted p.53 pair contour

The analytic and arithmetic factors are named separately to keep the exact
finite Euler mass visible and to avoid hiding any modulus or scale loss.
-/

namespace MAPJutilaP53ShiftedContourBound

open scoped BigOperators
open Complex MeasureTheory
open MAPJutilaP53PairRExpansion
open MAPJutilaP53PairEulerFactorization
open MAPJutilaP53DivisorKernelMultiplicative
open MAPJutilaP53TwoScaleContour
open MAPJutilaP53LeftLineEstimate
open MAPJutilaP53PairShiftedContour

noncomputable section

def p53UniversalVerticalMass : ℝ :=
  ∫ t : ℝ, (1 + |t|) ^ 6 * Real.exp (-|t|)

def p53ShiftedAnalyticFactor (q : ℕ) (s : ℂ) : ℝ :=
  4800 * (q : ℝ) ^ 2 * (5 + |s.im|) ^ 2 * p53UniversalVerticalMass

def p53LeftContourTerm {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (s : ℂ) (M N : ℝ)
    (r r' d : ℕ) : ℂ :=
  LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d *
    ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, p53TwoScaleContourIntegrand chi s
        (N / (d : ℝ)) (M / (d : ℝ))
        (((-(1 / 2 : ℝ)) : ℂ) + v * I)))

def p53ShiftedDivisorMass {q : ℕ}
    (chi : DirichletCharacter ℂ q) (s : ℂ) (M N : ℝ)
    (r r' : ℕ) : ℝ :=
  ∑ d ∈ (r.lcm r').divisors,
    ‖LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d‖ *
      p53CpowEndpointBound (N / (d : ℝ)) (M / (d : ℝ))
        (-(1 / 2)) (-(1 / 2))

theorem p53ShiftedAnalyticFactor_nonneg (q : ℕ) (s : ℂ) :
    0 ≤ p53ShiftedAnalyticFactor q s := by
  unfold p53ShiftedAnalyticFactor p53UniversalVerticalMass
  have hint : 0 ≤ ∫ t : ℝ, (1 + |t|) ^ 6 * Real.exp (-|t|) :=
    integral_nonneg fun _ => mul_nonneg (pow_nonneg (by positivity) 6)
      (Real.exp_pos _).le
  positivity

theorem norm_p53LeftContourTerm_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {s : ℂ} (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 2)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    {r r' d : ℕ} (hd : d ∈ (r.lcm r').divisors) :
    ‖p53LeftContourTerm chi s M N r r' d‖ ≤
      ‖LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d‖ *
        (p53ShiftedAnalyticFactor q s *
          p53CpowEndpointBound (N / (d : ℝ)) (M / (d : ℝ))
            (-(1 / 2)) (-(1 / 2))) := by
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdPos
  have hint := norm_integral_p53TwoScaleContourIntegrand_leftHalf_le
    chi hchi s
    (div_pos (hM.trans hMN) hdR)
    (div_pos hM hdR) hsLo hsHi
  have hpi : ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (1 / (2 * Real.pi) : ℝ))]
    exact (div_le_one (by positivity)).2 (by nlinarith [Real.pi_gt_three])
  unfold p53LeftContourTerm
  rw [norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
        ‖∫ v : ℝ, p53TwoScaleContourIntegrand chi s
          (N / (d : ℝ)) (M / (d : ℝ))
          (((-(1 / 2 : ℝ)) : ℂ) + v * I)‖ ≤
      1 * ‖∫ v : ℝ, p53TwoScaleContourIntegrand chi s
          (N / (d : ℝ)) (M / (d : ℝ))
          (((-(1 / 2 : ℝ)) : ℂ) + v * I)‖ := by gcongr
    _ ≤ (4800 * (q : ℝ) ^ 2 * (5 + |s.im|) ^ 2 *
          p53CpowEndpointBound (N / (d : ℝ)) (M / (d : ℝ))
            (-(1 / 2)) (-(1 / 2))) * p53UniversalVerticalMass := by
      simpa [p53UniversalVerticalMass] using hint
    _ = p53ShiftedAnalyticFactor q s *
          p53CpowEndpointBound (N / (d : ℝ)) (M / (d : ℝ))
            (-(1 / 2)) (-(1 / 2)) := by
      unfold p53ShiftedAnalyticFactor
      ring

set_option maxHeartbeats 500000 in
 theorem norm_sum_p53LeftContourTerm_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {s : ℂ} (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 2)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N) (r r' : ℕ) :
    ‖∑ d ∈ (r.lcm r').divisors, p53LeftContourTerm chi s M N r r' d‖ ≤
      p53ShiftedAnalyticFactor q s *
        p53ShiftedDivisorMass chi s M N r r' := by
  calc
    _ ≤ ∑ d ∈ (r.lcm r').divisors,
        ‖p53LeftContourTerm chi s M N r r' d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ (r.lcm r').divisors,
        ‖LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d‖ *
          (p53ShiftedAnalyticFactor q s *
            p53CpowEndpointBound (N / (d : ℝ)) (M / (d : ℝ))
              (-(1 / 2)) (-(1 / 2))) := by
      apply Finset.sum_le_sum
      intro d hd
      exact norm_p53LeftContourTerm_le chi hchi hsLo hsHi hM hMN hd
    _ = _ := by
      unfold p53ShiftedDivisorMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

set_option maxHeartbeats 500000 in
 theorem norm_pairRB_le_shiftedDivisorMass_nonprincipal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    {s : ℂ} (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 2)
    {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    ‖jutilaP53PairRB M N s chi r r'‖ ≤
      (((r * r' : ℕ) : ℝ)⁻¹) * p53ShiftedAnalyticFactor q s *
        p53ShiftedDivisorMass chi s M N r r' := by
  rw [pairRB_eq_divisorKernel_leftHalfContours_nonprincipal
    chi hchi hM hMN hsLo hsHi hr hr']
  change ‖(((r * r' : ℕ) : ℂ)⁻¹) *
      ∑ d ∈ (r.lcm r').divisors,
        p53LeftContourTerm chi s M N r r' d‖ ≤ _
  rw [norm_mul]
  have hnormInv : ‖(((r * r' : ℕ) : ℂ)⁻¹)‖ =
      (((r * r' : ℕ) : ℝ)⁻¹) := by simp
  rw [hnormInv]
  calc
    _ ≤ (((r * r' : ℕ) : ℝ)⁻¹) *
        (p53ShiftedAnalyticFactor q s *
          p53ShiftedDivisorMass chi s M N r r') :=
      mul_le_mul_of_nonneg_left
        (norm_sum_p53LeftContourTerm_le chi hchi hsLo hsHi hM hMN r r')
        (by positivity)
    _ = _ := by rw [mul_assoc]

end

end MAPJutilaP53ShiftedContourBound

#print axioms MAPJutilaP53ShiftedContourBound.norm_p53LeftContourTerm_le
#print axioms MAPJutilaP53ShiftedContourBound.norm_sum_p53LeftContourTerm_le
#print axioms MAPJutilaP53ShiftedContourBound.norm_pairRB_le_shiftedDivisorMass_nonprincipal
