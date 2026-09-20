import GuthMaynardS2ReflectionBridge

/-! # Scale-local reflection of the literal Fourier pair moment
The pointwise gap mask is retained. The reflection denominator is bounded
using its actual lower gap U, not the ambient diameter T. Both Fourier tails,
the Mellin exterior, and the opposite-sign error remain explicit.
-/

namespace GuthMaynardS2DyadicReflection

open scoped BigOperators
open MeasureTheory
open GuthMaynardS2ReflectionBridge GuthMaynardSectorFactorization
open GuthMaynardLemma62NegativeNonstationary GuthMaynardLemma62AbsoluteMellinTail
open GuthMaynardSectionThreeCutoffDerivativeBudget
open GuthMaynardHeathBrownMajorant GuthMaynardHeathBrownInterface

noncomputable section

def sourceMellinPrefixIntegral (J : ℕ) (R t : ℝ) : ℝ :=
  ∫ r : ℝ in Set.Ioc (-R) R,
    ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
        ((1 : ℂ) + r * Complex.I)‖ *
      ‖GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
        (2 ^ J) (t - r)‖

def sourceReflectionScale (U R : ℝ) (J : ℕ) : ℝ :=
  (1 / (2 * Real.pi)) * ((J + 1) * (20 * Real.sqrt (8 * Real.pi) /
    Real.sqrt (U - R)))

def sourceReflectionError (N : ℕ) (U V R : ℝ) (J k ell : ℕ) : ℝ :=
  ((1 / (2 * Real.pi)) * Real.log (2 * ((2 ^ J : ℕ) : ℝ)) * ((2 ^ J : ℕ) : ℝ)) *
    (2 * (((2 * Real.pi) ^ k * sectionThreeMellinSeminorm k) *
      (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)))) +
  ((2 ^ J : ℕ) : ℝ) * (negativeSectorConstant / U) +
  2 * ((lemma43DerivativeConstant ell * (1 + V) ^ ell *
      (N : ℝ) ^ (-(ell : ℝ))) *
    (((2 ^ J : ℕ) : ℝ) ^ (1 - (ell : ℝ)) / ((ell : ℝ) - 1)))

def sourceFourierGapPairMoment (N : ℕ) (W : Finset ℝ) (U V : ℝ) : ℝ :=
  ∑ t ∈ W, ∑ u ∈ W,
    if U ≤ |t - u| ∧ |t - u| ≤ V then ‖sourceNonzeroFourier N (t - u)‖ ^ 2 else 0

theorem sourceMellinPrefixIntegral_nonneg (J : ℕ) (R t : ℝ) :
    0 ≤ sourceMellinPrefixIntegral J R t :=
  integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem sourceReflectionScale_nonneg (U R : ℝ) (J : ℕ) :
    0 ≤ sourceReflectionScale U R J := by
  unfold sourceReflectionScale
  positivity

theorem sourceReflectionError_nonneg (N : ℕ) {U V R : ℝ}
    (hU : 0 < U) (hV : 0 ≤ V) (hR : 0 < R)
    (J k ell : ℕ) (hk : 2 ≤ k) (hell : 2 ≤ ell) :
    0 ≤ sourceReflectionError N U V R J k ell := by
  have hM : (1 : ℝ) ≤ ((2 ^ J : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_pow J 2 (by norm_num)
  have hlog : 0 ≤ Real.log (2 * ((2 ^ J : ℕ) : ℝ)) :=
    Real.log_nonneg (by linarith)
  have hkR : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hellR : (1 : ℝ) < ell := by exact_mod_cast (show 1 < ell by omega)
  have hder := lemma43DerivativeConstant_nonneg ell
  have hsem := sectionThreeMellinSeminorm_nonneg k
  have hneg := negativeSectorConstant_nonneg
  unfold sourceReflectionError
  positivity

theorem sourceReflectionBudget_eq (N : ℕ) {t : ℝ} (ht : 0 < t)
    (R : ℝ) (J k ell : ℕ) :
    sourceReflectionBudget N t R J k ell =
      sourceReflectionScale t R J * sourceMellinPrefixIntegral J R t +
        sourceReflectionError N t t R J k ell := by
  unfold sourceReflectionBudget sourceReflectionScale sourceMellinPrefixIntegral sourceReflectionError
  rw [integral_const_mul, abs_of_pos ht]
  ring

theorem sourceReflectionScale_antitone {U t R : ℝ}
    (hRU : R < U) (hUt : U ≤ t) (J : ℕ) :
    sourceReflectionScale t R J ≤ sourceReflectionScale U R J := by
  unfold sourceReflectionScale
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_left (by positivity)
    (Real.sqrt_pos.mpr (sub_pos.mpr hRU))
  exact Real.sqrt_le_sqrt (sub_le_sub_right hUt R)

theorem sourceReflectionError_mono (N : ℕ) {U t V R : ℝ}
    (hU : 0 < U) (hUt : U ≤ t) (htV : t ≤ V)
    (J k ell : ℕ) (hell : 2 ≤ ell) :
    sourceReflectionError N t t R J k ell ≤ sourceReflectionError N U V R J k ell := by
  have ht : 0 < t := hU.trans_le hUt
  have hV : 0 ≤ V := ht.le.trans htV
  have hellR : (1 : ℝ) < ell := by exact_mod_cast (show 1 < ell by omega)
  have hneg := div_le_div_of_nonneg_left negativeSectorConstant_nonneg hU hUt
  have hder := lemma43DerivativeConstant_nonneg ell
  unfold sourceReflectionError
  gcongr

/-- Reflection at the actual dyadic gap scale, retaining the pointwise mask. -/
theorem norm_sourceNonzeroFourier_le_gap_reflection
    {N : ℕ} (hN : 0 < N) {U V R t : ℝ}
    (hR : 0 < R) (hRU : R < U) (hUt : U ≤ |t|) (htV : |t| ≤ V)
    (J k ell : ℕ) (hk : 2 ≤ k) (hell : 2 ≤ ell) :
    ‖sourceNonzeroFourier N t‖ ≤
      sourceReflectionScale U R J * sourceMellinPrefixIntegral J R |t| +
        sourceReflectionError N U V R J k ell := by
  have hU := hR.trans hRU
  calc
    _ ≤ sourceReflectionBudget N |t| R J k ell :=
      norm_sourceNonzeroFourier_le_reflection_abs hN t hR
        (hRU.trans_le hUt) J k ell hk hell
    _ = _ := sourceReflectionBudget_eq N (hU.trans_le hUt) R J k ell
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (sourceReflectionScale_antitone hRU hUt J)
        (sourceMellinPrefixIntegral_nonneg J R |t|))
      (sourceReflectionError_mono N hU hUt htV J k ell hell)

private theorem sum_abs_difference_sq_le_twice (W : Finset ℝ) (f : ℝ → ℝ) :
    (∑ t ∈ W, ∑ u ∈ W, f |t - u| ^ 2) ≤
      2 * ∑ t ∈ W, ∑ u ∈ W, f (t - u) ^ 2 := by
  have hp : ∀ t u : ℝ, f |t - u| ^ 2 ≤ f (t - u) ^ 2 + f (u - t) ^ 2 := by
    intro t u
    by_cases h : 0 ≤ t - u
    · rw [abs_of_nonneg h]
      exact le_add_of_nonneg_right (sq_nonneg _)
    · rw [abs_of_neg (lt_of_not_ge h), neg_sub]
      exact le_add_of_nonneg_left (sq_nonneg _)
  calc
    _ ≤ ∑ t ∈ W, ∑ u ∈ W, (f (t - u) ^ 2 + f (u - t) ^ 2) :=
      Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun u _ => hp t u
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun t u => f (u - t) ^ 2)]
      ring

/-- Exact masked pair bound before the certified powered prefix is inserted. -/
theorem sourceFourierGapPairMoment_le_reflection
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) {U V R : ℝ}
    (hR : 0 < R) (hRU : R < U) (hUV : U ≤ V)
    (J k ell : ℕ) (hk : 2 ≤ k) (hell : 2 ≤ ell) :
    sourceFourierGapPairMoment N W U V ≤
      4 * sourceReflectionScale U R J ^ 2 *
        (∑ t ∈ W, ∑ u ∈ W, sourceMellinPrefixIntegral J R (t - u) ^ 2) +
      2 * (W.card : ℝ) ^ 2 * sourceReflectionError N U V R J k ell ^ 2 := by
  let K := sourceReflectionScale U R J
  let E := sourceReflectionError N U V R J k ell
  have hK : 0 ≤ K := sourceReflectionScale_nonneg U R J
  have hE : 0 ≤ E := sourceReflectionError_nonneg N
    (hR.trans hRU) ((hR.trans hRU).le.trans hUV) hR J k ell hk hell
  have hp : ∀ t u : ℝ,
      (if U ≤ |t - u| ∧ |t - u| ≤ V then ‖sourceNonzeroFourier N (t - u)‖ ^ 2 else 0) ≤
        2 * K ^ 2 * sourceMellinPrefixIntegral J R |t - u| ^ 2 + 2 * E ^ 2 := by
    intro t u
    by_cases h : U ≤ |t - u| ∧ |t - u| ≤ V
    · rw [if_pos h]
      have hb := norm_sourceNonzeroFourier_le_gap_reflection hN hR hRU h.1 h.2 J k ell hk hell
      have hb' := pow_le_pow_left₀ (norm_nonneg _) hb 2
      change _ ≤ (K * sourceMellinPrefixIntegral J R |t - u| + E) ^ 2 at hb'
      nlinarith [sq_nonneg (K * sourceMellinPrefixIntegral J R |t - u| - E)]
    · rw [if_neg h]
      positivity
  have hsum : sourceFourierGapPairMoment N W U V ≤
      2 * K ^ 2 * (∑ t ∈ W, ∑ u ∈ W, sourceMellinPrefixIntegral J R |t - u| ^ 2) +
        2 * (W.card : ℝ) ^ 2 * E ^ 2 := by
    calc
      _ ≤ ∑ t ∈ W, ∑ u ∈ W,
          (2 * K ^ 2 * sourceMellinPrefixIntegral J R |t - u| ^ 2 + 2 * E ^ 2) :=
        Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun u _ => hp t u
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        ring
  have habs := sum_abs_difference_sq_le_twice W (sourceMellinPrefixIntegral J R)
  have hm := mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ 2 * K ^ 2)
  change _ ≤ 4 * K ^ 2 * _ + 2 * (W.card : ℝ) ^ 2 * E ^ 2
  nlinarith

def sourceGapPoweredBudget (C eta T : ℝ) (N : ℕ) (W : Finset ℝ)
    (U V R : ℝ) (J k ell : ℕ) : ℝ :=
  4 * sourceReflectionScale U R J ^ 2 *
    ((∫ r : ℝ in Set.Ioc (-R) R,
        ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
          ((1 : ℂ) + r * Complex.I)‖) ^ 2 *
      (((J + 1 : ℕ) : ℝ) * ((W.card : ℝ) ^ 2 +
        ∑ j ∈ Finset.range J,
          C * Real.rpow T eta * (W.card : ℝ) *
            Real.sqrt (heathBrownShape T ((2 ^ j) ^ 2) W)))) +
    2 * (W.card : ℝ) ^ 2 * sourceReflectionError N U V R J k ell ^ 2

/-- Certified local Section-6 estimate on the literal pointwise gap mask.
No reflection, mean-value, or sector-bound premise remains. -/
theorem sourceFourierGapPairMoment_powered_bound {eta : ℝ} (heta : 0 < eta) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (N : ℕ) (W : Finset ℝ) (U V R : ℝ) (J k ell : ℕ),
        T₀ ≤ T → 0 < N → 0 < R → R < U → U ≤ V →
        ((2 ^ J : ℕ) : ℝ) ≤ T → 2 ≤ k → 2 ≤ ell →
        CGLProofDAG.OneSeparated W → ContainedInIntervalOfLength W T →
        sourceFourierGapPairMoment N W U V ≤
          sourceGapPoweredBudget C eta T N W U V R J k ell := by
  obtain ⟨C, T₀, hC, hT₀, hprefix⟩ := reflectedPrefix_pair_integral_sq_le_powered heta
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T N W U V R J k ell hT hN hR hRU hUV hJT hk hell hsep hinterval
  apply (sourceFourierGapPairMoment_le_reflection hN W hR hRU hUV J k ell hk hell).trans
  unfold sourceGapPoweredBudget
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact hprefix T J R W hT hJT hsep hinterval

end
end GuthMaynardS2DyadicReflection

#print axioms GuthMaynardS2DyadicReflection.sourceFourierGapPairMoment_le_reflection

#print axioms GuthMaynardS2DyadicReflection.sourceFourierGapPairMoment_powered_bound
