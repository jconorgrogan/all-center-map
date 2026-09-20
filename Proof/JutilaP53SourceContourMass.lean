import JutilaP53SourcePairContours

/-! Arithmetic assembly of the literal source contour norm. -/
namespace MAPJutilaP53SourceContourMass
open scoped BigOperators
open Complex MeasureTheory
open MAPJutilaP53SourcePairContours MAPJutilaP53SourceDivisorMass
open MAPJutilaP53TwoScaleContour MAPJutilaP53PairEulerFactorization
open MAPJutilaP53Lemma2Bridge MAPJutilaP53DivisorKernelAbsoluteMass
noncomputable section

theorem norm_sourceContourTerm_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} {M N epsilon K : ℝ} {r r' d : ℕ}
    (hM : 0 < M) (hN : 0 < N) (hd : 0 < d)
    (heps : 0 ≤ epsilon) (hs : 0 ≤ s.re) (hK : 0 ≤ K)
    (hI : ‖∫ v : ℝ, p53TwoScaleContourIntegrand chi s
      (N / (d : ℝ)) (M / (d : ℝ))
      (((-1 + epsilon : ℝ) : ℂ) + v * I)‖ ≤
      K * Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2) *
        sourceEndpoint (N / d) (M / d) epsilon) :
    ‖sourceContourTerm chi s M N epsilon r r' d‖ ≤
      (K * Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2) * sourceEndpoint N M epsilon) *
        ‖p53PairDivisorKernel r r' d‖ := by
  have hpi : ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (1 / (2 * Real.pi) : ℝ))]
    exact (div_le_one (by positivity)).2 (by nlinarith [Real.pi_gt_three])
  have hKh : 0 ≤ K * Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2) :=
    mul_nonneg hK (Real.rpow_nonneg (by positivity) _)
  unfold sourceContourTerm
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d‖ *
      (K * Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2) * sourceEndpoint (N / d) (M / d) epsilon) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (mul_le_of_le_one_left (norm_nonneg _) hpi).trans hI
    _ = (K * Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2)) *
      (‖LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d‖ * sourceEndpoint (N / d) (M / d) epsilon) := by ring
    _ ≤ (K * Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2)) *
      (‖p53PairDivisorKernel r r' d‖ * sourceEndpoint N M epsilon) :=
      mul_le_mul_of_nonneg_left (twisted_term_mul_sourceEndpoint_le chi hN hM hd heps hs) hKh
    _ = _ := by ring

theorem norm_sum_sourceContourTerm_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} {M N epsilon K : ℝ} {r r' : ℕ}
    (hM : 0 < M) (hN : 0 < N)
    (heps : 0 ≤ epsilon) (hs : 0 ≤ s.re) (hK : 0 ≤ K)
    (hr : Squarefree r) (hr' : Squarefree r')
    (hI : ∀ d ∈ (r.lcm r').divisors,
      ‖∫ v : ℝ, p53TwoScaleContourIntegrand chi s
        (N / (d : ℝ)) (M / (d : ℝ))
        (((-1 + epsilon : ℝ) : ℂ) + v * I)‖ ≤
      K * Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2) *
        sourceEndpoint (N / d) (M / d) epsilon) :
    ‖∑ d ∈ (r.lcm r').divisors, sourceContourTerm chi s M N epsilon r r' d‖ ≤
      (K * Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2) * sourceEndpoint N M epsilon) *
        (MAPJutilaLemma3AbsoluteMass.lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ) := by
  calc
    _ ≤ ∑ d ∈ (r.lcm r').divisors, ‖sourceContourTerm chi s M N epsilon r r' d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ (r.lcm r').divisors,
        (K * Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2) * sourceEndpoint N M epsilon) *
          ‖p53PairDivisorKernel r r' d‖ := by
      apply Finset.sum_le_sum
      intro d hd
      exact norm_sourceContourTerm_le chi hM hN (Nat.pos_of_mem_divisors hd)
        heps hs hK (hI d hd)
    _ = _ := by
      rw [← Finset.mul_sum, sum_norm_p53PairDivisorKernel_eq_lemmaThreeAbsoluteMass hr hr']

end
end MAPJutilaP53SourceContourMass
#print axioms MAPJutilaP53SourceContourMass.norm_sourceContourTerm_le

#print axioms MAPJutilaP53SourceContourMass.norm_sum_sourceContourTerm_le
