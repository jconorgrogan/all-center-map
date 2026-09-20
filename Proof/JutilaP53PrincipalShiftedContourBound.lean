import JutilaP53PrincipalPairShiftedContour
import JutilaP53DivisorKernelAbsoluteMass
import JutilaP53PrincipalRResidueAggregation

/-!
# Quantitative principal shifted-contour branch
-/

namespace MAPJutilaP53PrincipalShiftedContourBound

open scoped BigOperators
open Complex MeasureTheory
open MAPJutilaP53TwoScaleContour
open MAPJutilaP53LeftLineEstimate
open MAPJutilaP53ShiftedContourBound
open MAPJutilaP53PrincipalLeftLineEstimate
open MAPJutilaP53PairEulerFactorization
open MAPJutilaP53DivisorKernelAbsoluteMass
open MAPJutilaP53PrincipalRResidueAggregation

noncomputable section

def p53PrincipalShiftedAnalyticFactor (q : ℕ) (s : ℂ) : ℝ :=
  153600 * (2 : ℝ) ^ q.primeFactors.card * (5 + |s.im|) ^ 6 *
    p53PrincipalUniversalVerticalMass

theorem p53PrincipalShiftedAnalyticFactor_nonneg (q : ℕ) (s : ℂ) :
    0 ≤ p53PrincipalShiftedAnalyticFactor q s := by
  unfold p53PrincipalShiftedAnalyticFactor p53PrincipalUniversalVerticalMass
  have hint : 0 ≤ ∫ t : ℝ, (1 + |t|) ^ 7 * Real.exp (-|t|) :=
    integral_nonneg fun _ => mul_nonneg (pow_nonneg (by positivity) 7)
      (Real.exp_pos _).le
  positivity

theorem norm_p53PrincipalLeftContourTerm_le
    (q : ℕ) [NeZero q] {s : ℂ} (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 4)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    {r r' d : ℕ} (hd : d ∈ (r.lcm r').divisors) :
    ‖p53LeftContourTerm (1 : DirichletCharacter ℂ q) s M N r r' d‖ ≤
      ‖LSeries.term (p53TwistedDivisorKernel
        (1 : DirichletCharacter ℂ q) r r') (1 + s) d‖ *
      (p53PrincipalShiftedAnalyticFactor q s *
        p53CpowEndpointBound (N / (d : ℝ)) (M / (d : ℝ))
          (-(1 / 2)) (-(1 / 2))) := by
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdPos
  have hint := norm_integral_p53PrincipalIntegrand_leftHalf_le q s
    (div_pos (hM.trans hMN) hdR) (div_pos hM hdR) hsLo hsHi
  have hpi : ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (1 / (2 * Real.pi) : ℝ))]
    exact (div_le_one (by positivity)).2 (by nlinarith [Real.pi_gt_three])
  unfold p53LeftContourTerm
  rw [norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
        ‖∫ v : ℝ, p53TwoScaleContourIntegrand
          (1 : DirichletCharacter ℂ q) s (N / (d : ℝ)) (M / (d : ℝ))
          (((-(1 / 2 : ℝ)) : ℂ) + v * I)‖ ≤
      1 * ‖∫ v : ℝ, p53TwoScaleContourIntegrand
          (1 : DirichletCharacter ℂ q) s (N / (d : ℝ)) (M / (d : ℝ))
          (((-(1 / 2 : ℝ)) : ℂ) + v * I)‖ := by gcongr
    _ ≤ (153600 * (2 : ℝ) ^ q.primeFactors.card * (5 + |s.im|) ^ 6 *
        p53CpowEndpointBound (N / (d : ℝ)) (M / (d : ℝ))
          (-(1 / 2)) (-(1 / 2))) * p53PrincipalUniversalVerticalMass := by
      simpa using hint
    _ = p53PrincipalShiftedAnalyticFactor q s *
        p53CpowEndpointBound (N / (d : ℝ)) (M / (d : ℝ))
          (-(1 / 2)) (-(1 / 2)) := by
      unfold p53PrincipalShiftedAnalyticFactor
      ring

set_option maxHeartbeats 500000 in
theorem norm_sum_p53PrincipalLeftContourTerm_le
    (q : ℕ) [NeZero q] {s : ℂ} (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 4)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N) (r r' : ℕ) :
    ‖∑ d ∈ (r.lcm r').divisors,
      p53LeftContourTerm (1 : DirichletCharacter ℂ q) s M N r r' d‖ ≤
      p53PrincipalShiftedAnalyticFactor q s *
        p53ShiftedDivisorMass (1 : DirichletCharacter ℂ q) s M N r r' := by
  calc
    _ ≤ ∑ d ∈ (r.lcm r').divisors,
        ‖p53LeftContourTerm (1 : DirichletCharacter ℂ q) s M N r r' d‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ (r.lcm r').divisors,
        ‖LSeries.term (p53TwistedDivisorKernel
          (1 : DirichletCharacter ℂ q) r r') (1 + s) d‖ *
        (p53PrincipalShiftedAnalyticFactor q s *
          p53CpowEndpointBound (N / (d : ℝ)) (M / (d : ℝ))
            (-(1 / 2)) (-(1 / 2))) := by
      apply Finset.sum_le_sum
      intro d hd
      exact norm_p53PrincipalLeftContourTerm_le q hsLo hsHi hM hMN hd
    _ = _ := by
      unfold p53ShiftedDivisorMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

/-- The full normalized principal left-contour branch after all selected
`r,r'` sums. -/
theorem norm_principalNormalizedLeftBranch_le
    (q : ℕ) [NeZero q] {S : Finset ℕ} {s : ℂ}
    (hSq : ∀ r ∈ S, Squarefree r)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 4) :
    ‖∑ r ∈ S, ∑ r' ∈ S,
      (((r * r' : ℕ) : ℂ)⁻¹) *
        ∑ d ∈ (r.lcm r').divisors,
          p53LeftContourTerm (1 : DirichletCharacter ℂ q) s M N r r' d‖ ≤
      p53PrincipalShiftedAnalyticFactor q s *
        p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) *
          p53NormalizedEulerMass S := by
  calc
    _ ≤ ∑ r ∈ S, ∑ r' ∈ S,
        (((r * r' : ℕ) : ℝ)⁻¹) *
        ‖∑ d ∈ (r.lcm r').divisors,
          p53LeftContourTerm (1 : DirichletCharacter ℂ q) s M N r r' d‖ := by
      calc
        _ ≤ ∑ r ∈ S, ∑ r' ∈ S,
            ‖(((r * r' : ℕ) : ℂ)⁻¹) *
              ∑ d ∈ (r.lcm r').divisors,
                p53LeftContourTerm (1 : DirichletCharacter ℂ q) s M N r r' d‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => norm_sum_le _ _)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro r hr
          apply Finset.sum_congr rfl
          intro r' hr'
          rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ ∑ r ∈ S, ∑ r' ∈ S,
        (((r * r' : ℕ) : ℝ)⁻¹) *
        (p53PrincipalShiftedAnalyticFactor q s *
          (p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) *
            (MAPJutilaLemma3AbsoluteMass.lemmaThreeAbsoluteMass
              r.primeFactors r'.primeFactors : ℝ))) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro r' hr'
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hcont := norm_sum_p53PrincipalLeftContourTerm_le q hsLo hsHi hM hMN r r'
      have hmass := p53ShiftedDivisorMass_le_lemmaThreeAbsoluteMass
        (1 : DirichletCharacter ℂ q) hM (hM.trans hMN) hsLo
        (hSq r hr) (hSq r' hr')
      calc
        _ ≤ p53PrincipalShiftedAnalyticFactor q s *
            p53ShiftedDivisorMass (1 : DirichletCharacter ℂ q) s M N r r' := hcont
        _ ≤ p53PrincipalShiftedAnalyticFactor q s *
            (p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) *
              (MAPJutilaLemma3AbsoluteMass.lemmaThreeAbsoluteMass
                r.primeFactors r'.primeFactors : ℝ)) :=
          mul_le_mul_of_nonneg_left hmass
            (p53PrincipalShiftedAnalyticFactor_nonneg q s)
    _ = _ := by
      unfold p53NormalizedEulerMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r' hr'
      ring

end
end MAPJutilaP53PrincipalShiftedContourBound

#print axioms MAPJutilaP53PrincipalShiftedContourBound.norm_p53PrincipalLeftContourTerm_le
#print axioms MAPJutilaP53PrincipalShiftedContourBound.norm_sum_p53PrincipalLeftContourTerm_le
#print axioms MAPJutilaP53PrincipalShiftedContourBound.norm_principalNormalizedLeftBranch_le
