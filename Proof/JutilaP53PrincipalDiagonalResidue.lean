import JutilaP53PrincipalRResidueAggregation

/-!
# The principal p.53 diagonal residue

On the diagonal the pair shift is real.  The removable two-scale quotient is
exactly a logarithmic interval integral, so its norm is bounded by the
logarithmic scale width without dividing by the possibly zero shift.
-/

namespace MAPJutilaP53PrincipalDiagonalResidue

open Complex Real MeasureTheory
open MAPJutilaP53TwoScaleContour
open MAPJutilaP53PrincipalFinitePole
open MAPJutilaP53PrincipalDivisorResidueBound
open MAPJutilaP53PrincipalRResidueAggregation
open MAPJutilaP53KernelSourceForm
open MAPJutilaP53DivisorKernelAbsoluteMass
open MAPJutilaLemma3AbsoluteMass
open MAPBHPPrincipalResidueBound
open MAPGammaCompactStripSharp

noncomputable section

private theorem posReal_cpow_neg_eq_exp
    {U s : ℝ} (hU : 0 < U) :
    (U : ℂ) ^ (-((s : ℝ) : ℂ)) =
      Complex.exp ((-(s : ℝ) : ℂ) * (Real.log U : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hU.ne')]
  rw [← Complex.ofReal_log hU.le]
  congr 1
  ring

/-- Exact logarithmic-interval representation, including the removable
endpoint `s=0`. -/
theorem p53ScaleRemovableQuotient_negReal_eq_neg_integral
    {U V s : ℝ} (hU : 0 < U) (hV : 0 < V) :
    p53ScaleRemovableQuotient U V (-((s : ℝ) : ℂ)) =
      -(∫ t in Real.log U..Real.log V,
        Complex.exp ((-(s : ℝ) : ℂ) * (t : ℂ))) := by
  by_cases hs : s = 0
  · subst s
    simp only [ofReal_zero, neg_zero, zero_mul, Complex.exp_zero]
    simp [p53ScaleRemovableQuotient, intervalIntegral.integral_const,
      Complex.ofReal_log hU.le, Complex.ofReal_log hV.le]
  · have hsC : (-((s : ℝ) : ℂ)) ≠ 0 := by exact neg_ne_zero.mpr (ofReal_ne_zero.mpr hs)
    rw [integral_exp_mul_complex hsC]
    rw [p53ScaleRemovableQuotient, Function.update_of_ne hsC,
      p53ScaleDifference, posReal_cpow_neg_eq_exp hU,
      posReal_cpow_neg_eq_exp hV]
    field_simp [hsC]
    ring

/-- On source scales `1 ≤ U ≤ V`, the diagonal quotient costs only their
logarithmic separation. -/
theorem norm_p53ScaleRemovableQuotient_negReal_le_logGap
    {U V s : ℝ} (hU : 1 ≤ U) (hUV : U ≤ V) (hs : 0 ≤ s) :
    ‖p53ScaleRemovableQuotient U V (-((s : ℝ) : ℂ))‖ ≤
      Real.log V - Real.log U := by
  have hV : 1 ≤ V := hU.trans hUV
  rw [p53ScaleRemovableQuotient_negReal_eq_neg_integral
    (zero_lt_one.trans_le hU) (zero_lt_one.trans_le hV), norm_neg]
  have hlogUV : Real.log U ≤ Real.log V := Real.log_le_log
    (zero_lt_one.trans_le hU) hUV
  calc
    ‖∫ t in Real.log U..Real.log V,
        Complex.exp ((-(s : ℝ) : ℂ) * (t : ℂ))‖ ≤
        1 * |Real.log V - Real.log U| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, ofReal_re, ofReal_im, neg_re, neg_im,
        mul_zero, sub_zero]
      have htmem : t ∈ Set.Ioc (Real.log U) (Real.log V) := by
        simpa [Set.uIoc_of_le hlogUV] using ht
      have ht0 : 0 ≤ t := (Real.log_nonneg hU).trans htmem.1.le
      have hnonpos : -s * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hs) ht0
      simpa using Real.exp_le_one_iff.mpr hnonpos
    _ = Real.log V - Real.log U := by
      rw [one_mul, abs_of_nonneg (sub_nonneg.mpr hlogUV)]

/-- The source ordering is the reverse one: the first smoothing scale is the
larger scale. -/
theorem norm_p53ScaleRemovableQuotient_negReal_le_logGap_rev
    {U V s : ℝ} (hV : 1 ≤ V) (hVU : V ≤ U) (hs : 0 ≤ s) :
    ‖p53ScaleRemovableQuotient U V (-((s : ℝ) : ℂ))‖ ≤
      Real.log U - Real.log V := by
  have hU : 1 ≤ U := hV.trans hVU
  rw [p53ScaleRemovableQuotient_negReal_eq_neg_integral
    (zero_lt_one.trans_le hU) (zero_lt_one.trans_le hV), norm_neg]
  have hlogVU : Real.log V ≤ Real.log U := Real.log_le_log
    (zero_lt_one.trans_le hV) hVU
  calc
    ‖∫ t in Real.log U..Real.log V,
        Complex.exp ((-(s : ℝ) : ℂ) * (t : ℂ))‖ ≤
        1 * |Real.log V - Real.log U| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, ofReal_re, ofReal_im, neg_re, neg_im,
        mul_zero, sub_zero]
      rw [Set.uIoc_comm] at ht
      have htmem : t ∈ Set.Ioc (Real.log V) (Real.log U) := by
        simpa [Set.uIoc_of_le hlogVU] using ht
      have ht0 : 0 ≤ t := (Real.log_nonneg hV).trans htmem.1.le
      have hnonpos : -s * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hs) ht0
      simpa using Real.exp_le_one_iff.mpr hnonpos
    _ = Real.log U - Real.log V := by
      rw [one_mul, abs_of_nonpos (sub_nonpos.mpr hlogVU)]
      ring

/-- Explicit diagonal principal residue bound. -/
theorem norm_p53PrincipalResidue_diagonal_le_logGap
    (q : ℕ) [NeZero q] {s U V : ℝ}
    (hU : 1 ≤ U) (hUV : U ≤ V) (hsLo : 0 ≤ s) (hsHi : s ≤ 1 / 2) :
    ‖p53PrincipalResidue q (s : ℂ) U V‖ ≤
      12 * (Real.log V - Real.log U) := by
  have hQ := norm_p53ScaleRemovableQuotient_negReal_le_logGap hU hUV hsLo
  have hGamma := norm_Gamma_positive_strip_le_exp_pi_half
    (a := 1 - s) (t := 0) (by linarith) (by linarith)
  have hGammaArg :
      Complex.Gamma (1 - (s : ℂ)) =
        Complex.Gamma (GammaCompactStripScratch.stripPoint (1 - s) 0) := by
    congr 1
    apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint]
  rw [← hGammaArg] at hGamma
  have hreg := norm_regularized_principal_one_le_one q
  unfold p53PrincipalResidue
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (12 * (1 + |(0 : ℝ)|) * Real.exp (-(Real.pi / 2) * |(0 : ℝ)|)) *
        (Real.log V - Real.log U) * 1 := by
      exact mul_le_mul
        (mul_le_mul hGamma hQ (norm_nonneg _) (by positivity)) hreg
        (norm_nonneg _) (mul_nonneg (by positivity) (sub_nonneg.mpr
          (Real.log_le_log (zero_lt_one.trans_le hU) hUV)))
    _ = _ := by norm_num

theorem norm_p53PrincipalResidue_diagonal_le_logGap_rev
    (q : ℕ) [NeZero q] {s U V : ℝ}
    (hV : 1 ≤ V) (hVU : V ≤ U) (hsLo : 0 ≤ s) (hsHi : s ≤ 1 / 2) :
    ‖p53PrincipalResidue q (s : ℂ) U V‖ ≤
      12 * (Real.log U - Real.log V) := by
  have hQ := norm_p53ScaleRemovableQuotient_negReal_le_logGap_rev hV hVU hsLo
  have hGamma := norm_Gamma_positive_strip_le_exp_pi_half
    (a := 1 - s) (t := 0) (by linarith) (by linarith)
  have hGammaArg :
      Complex.Gamma (1 - (s : ℂ)) =
        Complex.Gamma (GammaCompactStripScratch.stripPoint (1 - s) 0) := by
    congr 1
    apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint]
  rw [← hGammaArg] at hGamma
  have hreg := norm_regularized_principal_one_le_one q
  unfold p53PrincipalResidue
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (12 * (1 + |(0 : ℝ)|) * Real.exp (-(Real.pi / 2) * |(0 : ℝ)|)) *
        (Real.log U - Real.log V) * 1 := by
      exact mul_le_mul
        (mul_le_mul hGamma hQ (norm_nonneg _) (by positivity)) hreg
        (norm_nonneg _) (mul_nonneg (by positivity) (sub_nonneg.mpr
          (Real.log_le_log (zero_lt_one.trans_le hV) hVU)))
    _ = _ := by norm_num

/-- The exact divisor-expanded diagonal residue retains only the Lemma-3
absolute Euler mass and the logarithmic scale gap. -/
theorem norm_p53PrincipalDivisorResidue_diagonal_le_logGap
    (q : ℕ) [NeZero q] {s M N : ℝ} {r r' : ℕ}
    (hr : Squarefree r) (hr' : Squarefree r')
    (hscale : ((r.lcm r' : ℕ) : ℝ) ≤ M) (hMN : M ≤ N)
    (hsLo : 0 ≤ s) (hsHi : s ≤ 1 / 2) :
    ‖p53PrincipalDivisorResidue q (s : ℂ) M N r r'‖ ≤
      12 * (Real.log N - Real.log M) *
        (lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ) := by
  have hrPos : 0 < r := Nat.pos_of_ne_zero (Squarefree.ne_zero hr)
  have hrPos' : 0 < r' := Nat.pos_of_ne_zero (Squarefree.ne_zero hr')
  have hlcmPos : 0 < r.lcm r' := Nat.lcm_pos hrPos hrPos'
  have hM : 0 < M := (Nat.cast_pos.mpr hlcmPos).trans_le hscale
  have hN : 0 < N := hM.trans_le hMN
  unfold p53PrincipalDivisorResidue
  calc
    _ ≤ ∑ d ∈ (r.lcm r').divisors,
        ‖LSeries.term
            (MAPJutilaP53PairEulerFactorization.p53TwistedDivisorKernel
              (1 : DirichletCharacter ℂ q) r r')
            (1 + (s : ℂ)) d *
          p53PrincipalResidue q (s : ℂ) (N / (d : ℝ)) (M / (d : ℝ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ (r.lcm r').divisors,
        ‖MAPJutilaP53Lemma2Bridge.p53PairDivisorKernel r r' d‖ *
          (12 * (Real.log N - Real.log M)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdPos := Nat.pos_of_mem_divisors hd
      have hdDvd : d ∣ r.lcm r' := (Nat.mem_divisors.mp hd).1
      have hdLe : d ≤ r.lcm r' := Nat.le_of_dvd hlcmPos hdDvd
      have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hdPos
      have hdLeR : (d : ℝ) ≤ (r.lcm r' : ℕ) := by exact_mod_cast hdLe
      have hdM : (d : ℝ) ≤ M := hdLeR.trans hscale
      have hdN : (d : ℝ) ≤ N := hdM.trans hMN
      have hdivOrder : M / (d : ℝ) ≤ N / (d : ℝ) :=
        div_le_div_of_nonneg_right hMN hdR.le
      have hgap : Real.log (N / (d : ℝ)) - Real.log (M / (d : ℝ)) =
          Real.log N - Real.log M := by
        rw [Real.log_div hN.ne' hdR.ne', Real.log_div hM.ne' hdR.ne']
        ring
      rw [norm_mul]
      apply mul_le_mul
      · exact norm_twisted_kernel_term_le_kernel q hdPos (by simpa using hsLo)
      · rw [← hgap]
        exact norm_p53PrincipalResidue_diagonal_le_logGap_rev q
          ((one_le_div₀ hdR).2 hdM) hdivOrder hsLo hsHi
      · exact norm_nonneg _
      · exact norm_nonneg _
    _ = 12 * (Real.log N - Real.log M) *
        ∑ d ∈ (r.lcm r').divisors,
          ‖MAPJutilaP53Lemma2Bridge.p53PairDivisorKernel r r' d‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by
      rw [sum_norm_p53PairDivisorKernel_eq_lemmaThreeAbsoluteMass hr hr']

theorem norm_p53PrincipalRResidue_diagonal_le_logGap
    (q : ℕ) [NeZero q] {S : Finset ℕ} {s M N : ℝ}
    (hSq : ∀ r ∈ S, Squarefree r)
    (hscale : ∀ r ∈ S, ∀ r' ∈ S,
      ((r.lcm r' : ℕ) : ℝ) ≤ M)
    (hMN : M ≤ N) (hsLo : 0 ≤ s) (hsHi : s ≤ 1 / 2) :
    ‖p53PrincipalRResidue q S (s : ℂ) M N‖ ≤
      12 * (Real.log N - Real.log M) * p53NormalizedEulerMass S := by
  unfold p53PrincipalRResidue
  calc
    _ ≤ ∑ r ∈ S, ∑ r' ∈ S,
        ‖(((r * r' : ℕ) : ℂ)⁻¹) *
          p53PrincipalDivisorResidue q (s : ℂ) M N r r'‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => norm_sum_le _ _)
    _ ≤ ∑ r ∈ S, ∑ r' ∈ S,
        (((r * r' : ℕ) : ℝ)⁻¹) *
          (12 * (Real.log N - Real.log M) *
            (lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hrMem
      apply Finset.sum_le_sum
      intro r' hrMem'
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        (norm_p53PrincipalDivisorResidue_diagonal_le_logGap q
          (hSq r hrMem) (hSq r' hrMem') (hscale r hrMem r' hrMem')
          hMN hsLo hsHi) (by positivity)
    _ = 12 * (Real.log N - Real.log M) * p53NormalizedEulerMass S := by
      unfold p53NormalizedEulerMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r' hr'
      ring

@[simp] theorem pairShift_self
    {q : ℕ} (alpha : ℝ) (i : MAPJutilaP53AggregateCorrelationLeaf.JutilaP53Row q) :
    jutilaP53PairShift alpha i i =
      ((2 * (i.zero.re - alpha) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [jutilaP53PairShift]
    ring
  · simp [jutilaP53PairShift]

/-- Exact diagonal row specialization used in the same-character fiber split. -/
theorem norm_p53PrincipalRResidue_pairShift_self_le
    (q : ℕ) [NeZero q] {S : Finset ℕ} {alpha epsilon M N : ℝ}
    (i : MAPJutilaP53AggregateCorrelationLeaf.JutilaP53Row q)
    (hSq : ∀ r ∈ S, Squarefree r)
    (hscale : ∀ r ∈ S, ∀ r' ∈ S,
      ((r.lcm r' : ℕ) : ℝ) ≤ M)
    (hMN : M ≤ N) (hiLo : alpha ≤ i.zero.re)
    (hiHi : i.zero.re ≤ alpha + epsilon) (heps : 2 * epsilon ≤ 1 / 2) :
    ‖p53PrincipalRResidue q S (jutilaP53PairShift alpha i i) M N‖ ≤
      12 * (Real.log N - Real.log M) * p53NormalizedEulerMass S := by
  rw [pairShift_self]
  apply norm_p53PrincipalRResidue_diagonal_le_logGap q hSq hscale hMN
  · linarith
  · linarith

end
end MAPJutilaP53PrincipalDiagonalResidue

#print axioms MAPJutilaP53PrincipalDiagonalResidue.p53ScaleRemovableQuotient_negReal_eq_neg_integral
#print axioms MAPJutilaP53PrincipalDiagonalResidue.norm_p53ScaleRemovableQuotient_negReal_le_logGap
#print axioms MAPJutilaP53PrincipalDiagonalResidue.norm_p53PrincipalResidue_diagonal_le_logGap
#print axioms MAPJutilaP53PrincipalDiagonalResidue.norm_p53ScaleRemovableQuotient_negReal_le_logGap_rev
#print axioms MAPJutilaP53PrincipalDiagonalResidue.norm_p53PrincipalResidue_diagonal_le_logGap_rev
#print axioms MAPJutilaP53PrincipalDiagonalResidue.norm_p53PrincipalDivisorResidue_diagonal_le_logGap
#print axioms MAPJutilaP53PrincipalDiagonalResidue.norm_p53PrincipalRResidue_diagonal_le_logGap
#print axioms MAPJutilaP53PrincipalDiagonalResidue.norm_p53PrincipalRResidue_pairShift_self_le
