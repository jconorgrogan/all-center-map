import GuthMaynardJIterationSigmaIIFourier
import GuthMaynardSectionFourTrace

open scoped BigOperators ComplexConjugate
open GuthMaynardSectionFourTrace
open GuthMaynardJIteration

noncomputable section
namespace GuthMaynardGMPointwiseKernel

/-- The coefficient independent, unsmoothed dyadic phase sum. -/
def gmDyadicKernel (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N), GuthMaynardSectionFourTrace.sourcePhase n t

/-- The real phase when the integer variable is relaxed to a positive real. -/
def gmRealPhase (t x : ℝ) : ℝ := t / (2 * Real.pi) * Real.log x

def gmRealPhaseDeriv (t x : ℝ) : ℝ := t / (2 * Real.pi * x)

def gmRealPhaseSecond (t x : ℝ) : ℝ := -t / (2 * Real.pi * x ^ 2)

theorem hasDerivAt_gmRealPhase {t x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (gmRealPhase t) (gmRealPhaseDeriv t x) x := by
  unfold gmRealPhase gmRealPhaseDeriv
  convert (Real.hasDerivAt_log hx).const_mul (t / (2 * Real.pi)) using 1
  field_simp [Real.pi_ne_zero, hx]

theorem hasDerivAt_gmRealPhaseDeriv {t x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (gmRealPhaseDeriv t) (gmRealPhaseSecond t x) x := by
  unfold gmRealPhaseDeriv gmRealPhaseSecond
  convert (hasDerivAt_inv hx).const_mul (t / (2 * Real.pi)) using 1
  field_simp [Real.pi_ne_zero, hx]
  ring

theorem gmRealPhaseDeriv_abs_le_on_dyadic
    {N : ℕ} (hN : 1 ≤ N) {t x : ℝ} (hx : x ∈ Set.Icc (N : ℝ) (2 * N)) :
    |gmRealPhaseDeriv t x| ≤ |t| / (2 * Real.pi * (N : ℝ)) := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hx0 : 0 < x := lt_of_lt_of_le hN0 hx.1
  unfold gmRealPhaseDeriv
  simp only [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi * x)]
  apply div_le_div_of_nonneg_left (abs_nonneg t)
    (by positivity) (by gcongr; exact hx.1)

theorem gmRealPhaseSecond_abs_le_on_dyadic
    {N : ℕ} (hN : 1 ≤ N) {t x : ℝ} (hx : x ∈ Set.Icc (N : ℝ) (2 * N)) :
    |gmRealPhaseSecond t x| ≤ |t| / (2 * Real.pi * (N : ℝ) ^ 2) := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hx0 : 0 < x := lt_of_lt_of_le hN0 hx.1
  unfold gmRealPhaseSecond
  simp only [abs_div, abs_neg,
    abs_of_pos (by positivity : 0 < 2 * Real.pi * x ^ 2)]
  have hsquares : (N : ℝ) ^ 2 ≤ x ^ 2 := by
    nlinarith [hN0, hx.1]
  apply div_le_div_of_nonneg_left (abs_nonneg t)
    (by positivity : 0 < 2 * Real.pi * (N : ℝ) ^ 2) (by
      gcongr)

theorem gmRealPhaseSecond_abs_ge_on_dyadic
    {N : ℕ} (hN : 1 ≤ N) {t x : ℝ} (hx : x ∈ Set.Icc (N : ℝ) (2 * N)) :
    |t| / (8 * Real.pi * (N : ℝ) ^ 2) ≤ |gmRealPhaseSecond t x| := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hx0 : 0 < x := lt_of_lt_of_le hN0 hx.1
  have hxSq : x ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by
    nlinarith [hx.2, hx.1]
  unfold gmRealPhaseSecond
  simp only [abs_div, abs_neg,
    abs_of_pos (by positivity : 0 < 2 * Real.pi * x ^ 2)]
  have hden : 2 * Real.pi * x ^ 2 ≤ 8 * Real.pi * (N : ℝ) ^ 2 := by
    nlinarith [Real.pi_pos, hxSq]
  apply div_le_div_of_nonneg_left (abs_nonneg t)
    (by positivity : 0 < 2 * Real.pi * x ^ 2) hden

/-- Unconditional absolute bound; this is the complete low-time branch of the
pointwise target. -/
theorem norm_gmDyadicKernel_le_card
    {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    ‖gmDyadicKernel N t‖ ≤ (N : ℝ) := by
  unfold gmDyadicKernel
  calc
    ‖∑ n ∈ Finset.Ioc N (2 * N),
        GuthMaynardSectionFourTrace.sourcePhase n t‖ ≤
        ∑ n ∈ Finset.Ioc N (2 * N),
          ‖GuthMaynardSectionFourTrace.sourcePhase n t‖ := norm_sum_le _ _
    _ = ((Finset.Ioc N (2 * N)).card : ℝ) := by
      have hnorm : ∀ n : ℕ,
          ‖GuthMaynardSectionFourTrace.sourcePhase n t‖ = 1 := by
        intro n
        unfold GuthMaynardSectionFourTrace.sourcePhase
        have h := Complex.norm_exp_ofReal_mul_I (t * Real.log (n : ℝ))
        convert h using 1
        push_cast
        ring_nf
      simp_rw [hnorm]
      simp
    _ = (N : ℝ) := by
      rw [Nat.card_Ioc]
      norm_cast
      omega

theorem norm_gmDyadicKernel_le_shape_of_abs_le_one
    {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : |t| ≤ 1) :
    ‖gmDyadicKernel N t‖ ≤
      4 * ((N : ℝ) / (1 + |t|) + Real.sqrt |t| + Real.sqrt (N : ℝ)) := by
  have hraw := norm_gmDyadicKernel_le_card hN t
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hden : 0 < 1 + |t| := by positivity
  have hfrac : (N : ℝ) / 2 ≤ (N : ℝ) / (1 + |t|) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hden).2
    nlinarith [abs_nonneg t, ht]
  have hsqrt : 0 ≤ Real.sqrt |t| := Real.sqrt_nonneg _
  have hsqrtN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  calc
    ‖gmDyadicKernel N t‖ ≤ (N : ℝ) := hraw
    _ ≤ 4 * ((N : ℝ) / (1 + |t|) + Real.sqrt |t| + Real.sqrt (N : ℝ)) := by
      nlinarith

/-- Exact missing discrete input for the genuinely oscillatory branch.  The
derivative formulae above expose the phase and scales that a finite
first/second derivative van der Corput proof must consume. -/
def gmDiscreteVdC2HardRange : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 1 < |t| →
    ‖gmDyadicKernel N t‖ ≤
      4 * ((N : ℝ) / (1 + |t|) + Real.sqrt |t| + Real.sqrt (N : ℝ))

theorem gmDyadicKernelPointwiseBound_of_discreteVdC2
    (hVdC : gmDiscreteVdC2HardRange) :
    ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ,
      ‖gmDyadicKernel N t‖ ≤
        4 * ((N : ℝ) / (1 + |t|) + Real.sqrt |t| + Real.sqrt (N : ℝ)) := by
  intro N hN t
  by_cases ht : |t| ≤ 1
  · exact norm_gmDyadicKernel_le_shape_of_abs_le_one hN ht
  · exact hVdC N hN t (lt_of_not_ge ht)

end GuthMaynardGMPointwiseKernel

#print axioms GuthMaynardGMPointwiseKernel.hasDerivAt_gmRealPhase
#print axioms GuthMaynardGMPointwiseKernel.hasDerivAt_gmRealPhaseDeriv
#print axioms GuthMaynardGMPointwiseKernel.gmRealPhaseDeriv_abs_le_on_dyadic
#print axioms GuthMaynardGMPointwiseKernel.gmRealPhaseSecond_abs_le_on_dyadic
#print axioms GuthMaynardGMPointwiseKernel.gmRealPhaseSecond_abs_ge_on_dyadic
#print axioms GuthMaynardGMPointwiseKernel.norm_gmDyadicKernel_le_card
#print axioms GuthMaynardGMPointwiseKernel.norm_gmDyadicKernel_le_shape_of_abs_le_one
#print axioms GuthMaynardGMPointwiseKernel.gmDyadicKernelPointwiseBound_of_discreteVdC2
