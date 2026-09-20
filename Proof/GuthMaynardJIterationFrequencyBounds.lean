import GuthMaynardJIterationSigmaIIPoissonSupport
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-! Exact analytic low/high frequency bounds in TeX 1556--1581. -/

def quarticDecayEnvelope (xi : ℝ) : ℝ :=
  1 / (1 + |xi|) ^ 4

theorem integrable_quarticDecayEnvelope :
    Integrable quarticDecayEnvelope := by
  have h := (integrable_one_add_norm (E := ℝ) (μ := volume)
    (r := (4 : ℝ)) (by norm_num))
  apply h.congr
  filter_upwards with xi
  unfold quarticDecayEnvelope
  rw [Real.norm_eq_abs, Real.rpow_neg (by positivity)]
  simp [one_div]

def quarticDecayMass : ℝ :=
  ∫ xi : ℝ, quarticDecayEnvelope xi

theorem highFrequency_norm_sq_le_decayEnvelope
    (ghat : ℝ → ℂ) (q : ℕ) {K B xi : ℝ}
    (hK : 0 ≤ K) (hB : 0 < B) (hxi : B < |xi|)
    (hdecay : ‖ghat xi‖ ≤ K / (1 + |xi|) ^ (q + 2)) :
    ‖ghat xi‖ ^ 2 ≤
      (K / B ^ q) ^ 2 * quarticDecayEnvelope xi := by
  let d : ℝ := |xi|
  have hd : 0 ≤ d := abs_nonneg xi
  have hBd : B ≤ 1 + d := by dsimp only [d]; linarith
  have hpow : B ^ q ≤ (1 + d) ^ q :=
    pow_le_pow_left₀ hB.le hBd q
  have hdenB : 0 < B ^ q := pow_pos hB q
  have hdenD : 0 < (1 + d) ^ q := pow_pos (by linarith) q
  have hdecay' : K / (1 + d) ^ (q + 2) ≤
      (K / B ^ q) * (1 / (1 + d) ^ 2) := by
    rw [pow_add]
    calc
      K / ((1 + d) ^ q * (1 + d) ^ 2) =
          (K / (1 + d) ^ q) * (1 / (1 + d) ^ 2) := by field_simp
      _ ≤ (K / B ^ q) * (1 / (1 + d) ^ 2) := by
        gcongr
  have hright0 : 0 ≤ (K / B ^ q) * (1 / (1 + d) ^ 2) := by positivity
  have hnorm : ‖ghat xi‖ ≤
      (K / B ^ q) * (1 / (1 + d) ^ 2) := hdecay.trans hdecay'
  calc
    ‖ghat xi‖ ^ 2 ≤
        ((K / B ^ q) * (1 / (1 + d) ^ 2)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hright0).2 hnorm
    _ = (K / B ^ q) ^ 2 * quarticDecayEnvelope xi := by
      unfold quarticDecayEnvelope
      dsimp only [d]
      field_simp

/-- Explicit rapid-decay estimate for source region III.  The decay seminorm
and high cutoff remain parameters; specializing `B=T^6` and taking large `q`
pays any desired negative power of `T`. -/
theorem integral_highFrequencyRegion_norm_sq_le
    (ghat : ℝ → ℂ) (q : ℕ) {K B : ℝ}
    (hK : 0 ≤ K) (hB : 0 < B)
    (hdecay : ∀ xi ∈ highFrequencyRegion B,
      ‖ghat xi‖ ≤ K / (1 + |xi|) ^ (q + 2))
    (hghat : IntegrableOn (fun xi => ‖ghat xi‖ ^ 2)
      (highFrequencyRegion B)) :
    (∫ xi in highFrequencyRegion B, ‖ghat xi‖ ^ 2) ≤
      (K / B ^ q) ^ 2 * quarticDecayMass := by
  let A : ℝ := (K / B ^ q) ^ 2
  have hA : 0 ≤ A := sq_nonneg _
  have hmajorInt : IntegrableOn
      (fun xi => A * quarticDecayEnvelope xi) (highFrequencyRegion B) :=
    (integrable_quarticDecayEnvelope.const_mul A).integrableOn
  calc
    (∫ xi in highFrequencyRegion B, ‖ghat xi‖ ^ 2) ≤
        ∫ xi in highFrequencyRegion B, A * quarticDecayEnvelope xi := by
      apply setIntegral_mono_on hghat hmajorInt
        (measurableSet_highFrequencyRegion B)
      intro xi hxi
      exact highFrequency_norm_sq_le_decayEnvelope ghat q hK hB hxi
        (hdecay xi hxi)
    _ ≤ ∫ xi : ℝ, A * quarticDecayEnvelope xi := by
      apply setIntegral_le_integral
      · exact integrable_quarticDecayEnvelope.const_mul A
      · apply Filter.Eventually.of_forall
        intro xi
        exact mul_nonneg hA (by unfold quarticDecayEnvelope; positivity)
    _ = (K / B ^ q) ^ 2 * quarticDecayMass := by
      rw [integral_const_mul]
      rfl

theorem sourceHighFrequencyIntegral_le_time_neg100
    (ghat : ℝ → ℂ) (q : ℕ) {K T C : ℝ}
    (hK : 0 ≤ K) (hT : 0 < T)
    (hdecay : ∀ xi ∈ highFrequencyRegion (sourceHighFrequencyCutoff T),
      ‖ghat xi‖ ≤ K / (1 + |xi|) ^ (q + 2))
    (hghat : IntegrableOn (fun xi => ‖ghat xi‖ ^ 2)
      (highFrequencyRegion (sourceHighFrequencyCutoff T)))
    (hbudget :
      (K / (sourceHighFrequencyCutoff T) ^ q) ^ 2 *
        quarticDecayMass * T ^ 100 ≤ C) :
    (∫ xi in highFrequencyRegion (sourceHighFrequencyCutoff T),
      ‖ghat xi‖ ^ 2) ≤ C / T ^ 100 := by
  have hcut : 0 < sourceHighFrequencyCutoff T := by
    unfold sourceHighFrequencyCutoff
    positivity
  refine (integral_highFrequencyRegion_norm_sq_le ghat q hK hcut
    hdecay hghat).trans ?_
  exact (le_div_iff₀ (pow_pos hT 100)).2 hbudget

def sourceLowOuterSum {ι : Type*} (outer : Finset ι)
    (block : ι → ℂ) : ℂ :=
  ∑ i ∈ outer, block i

/-- The literal two-layer finite Cauchy/triangle estimate behind TeX
1571--1573.  It exposes separately the outer pair count, the `m2` count,
the dilation ratio, the `M3` Poisson factor, and `sup |fhat|`. -/
theorem norm_sq_sourceLowOuterSum_le
    {ι : Type*} (outer : Finset ι) (m2Range : Finset ℤ)
    (M3 R S L N2 : ℝ) (arg : ι → ℤ → ℝ)
    (coeff : ι → ℤ → ℂ) (fhat : ℝ → ℂ)
    (hL : (outer.card : ℝ) ≤ L)
    (hN2 : (m2Range.card : ℝ) ≤ N2)
    (hR : ∀ i ∈ outer, ∀ m2 ∈ m2Range, ‖coeff i m2‖ ≤ R)
    (hS : ∀ i ∈ outer, ∀ m2 ∈ m2Range, ‖fhat (arg i m2)‖ ≤ S)
    (hM3 : 0 ≤ M3) (hR0 : 0 ≤ R) (hS0 : 0 ≤ S) :
    ‖sourceLowOuterSum outer (fun i =>
        (M3 : ℂ) * ∑ m2 ∈ m2Range, coeff i m2 * fhat (arg i m2))‖ ^ 2 ≤
      L ^ 2 * M3 ^ 2 * N2 ^ 2 * R ^ 2 * S ^ 2 := by
  have hinner : ∀ i ∈ outer,
      ‖∑ m2 ∈ m2Range, coeff i m2 * fhat (arg i m2)‖ ≤ N2 * R * S := by
    intro i hi
    calc
      ‖∑ m2 ∈ m2Range, coeff i m2 * fhat (arg i m2)‖ ≤
          ∑ m2 ∈ m2Range, ‖coeff i m2 * fhat (arg i m2)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _m2 ∈ m2Range, R * S := by
        apply Finset.sum_le_sum
        intro m2 hm2
        rw [norm_mul]
        exact mul_le_mul (hR i hi m2 hm2) (hS i hi m2 hm2)
          (norm_nonneg _) hR0
      _ = (m2Range.card : ℝ) * (R * S) := by simp
      _ ≤ N2 * R * S := by nlinarith [mul_nonneg hR0 hS0]
  have hblock : ∀ i ∈ outer,
      ‖(M3 : ℂ) * ∑ m2 ∈ m2Range,
        coeff i m2 * fhat (arg i m2)‖ ≤ M3 * N2 * R * S := by
    intro i hi
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM3]
    calc
      M3 * ‖∑ m2 ∈ m2Range, coeff i m2 * fhat (arg i m2)‖ ≤
          M3 * (N2 * R * S) := mul_le_mul_of_nonneg_left (hinner i hi) hM3
      _ = _ := by ring
  unfold sourceLowOuterSum
  calc
    ‖∑ i ∈ outer,
        (M3 : ℂ) * ∑ m2 ∈ m2Range, coeff i m2 * fhat (arg i m2)‖ ^ 2 ≤
      (outer.card : ℝ) ^ 2 * (M3 * N2 * R * S) ^ 2 :=
        norm_finset_sum_sq_le_card_sq_mul outer _ hblock
    _ ≤ L ^ 2 * (M3 * N2 * R * S) ^ 2 := by
      gcongr
    _ = L ^ 2 * M3 ^ 2 * N2 ^ 2 * R ^ 2 * S ^ 2 := by ring

/-- The exact low-region integral obtained by combining the source's
two-layer finite bound with the already certified interval-volume estimate.
No cardinality, dilation, or Fourier-supremum factor is hidden. -/
theorem sourceLowFrequencyIntegral_from_finite_outer
    {ι : Type*} (outer : Finset ι) (m2Range : Finset ℤ)
    (ghat fhat : ℝ → ℂ) (T eta M1 M3 R S L N2 : ℝ)
    (arg : ℝ → ι → ℤ → ℝ) (coeff : ι → ℤ → ℂ)
    (hghat_eq : ∀ xi ∈ lowFrequencyRegion
      (sourceLowFrequencyCutoff T eta M1 M3),
      ghat xi = sourceLowOuterSum outer (fun i =>
        (M3 : ℂ) * ∑ m2 ∈ m2Range,
          coeff i m2 * fhat (arg xi i m2)))
    (hL : (outer.card : ℝ) ≤ L)
    (hN2 : (m2Range.card : ℝ) ≤ N2)
    (hR : ∀ i ∈ outer, ∀ m2 ∈ m2Range, ‖coeff i m2‖ ≤ R)
    (hS : ∀ xi ∈ lowFrequencyRegion
      (sourceLowFrequencyCutoff T eta M1 M3),
      ∀ i ∈ outer, ∀ m2 ∈ m2Range, ‖fhat (arg xi i m2)‖ ≤ S)
    (hM3 : 0 ≤ M3) (hR0 : 0 ≤ R) (hS0 : 0 ≤ S)
    (hcut0 : 0 ≤ sourceLowFrequencyCutoff T eta M1 M3)
    (hint : IntegrableOn (fun xi => ‖ghat xi‖ ^ 2)
      (lowFrequencyRegion (sourceLowFrequencyCutoff T eta M1 M3))) :
    (∫ xi in lowFrequencyRegion (sourceLowFrequencyCutoff T eta M1 M3),
      ‖ghat xi‖ ^ 2) ≤
      2 * sourceLowFrequencyCutoff T eta M1 M3 *
        (L ^ 2 * M3 ^ 2 * N2 ^ 2 * R ^ 2 * S ^ 2) := by
  apply sourceLowFrequencyIntegral_le ghat hcut0 hint
  intro xi hxi
  rw [hghat_eq xi hxi]
  exact norm_sq_sourceLowOuterSum_le outer m2Range M3 R S L N2
    (arg xi) coeff fhat hL hN2 hR (hS xi hxi) hM3 hR0 hS0

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.integrable_quarticDecayEnvelope
#print axioms GuthMaynardJIteration.highFrequency_norm_sq_le_decayEnvelope
#print axioms GuthMaynardJIteration.integral_highFrequencyRegion_norm_sq_le
#print axioms GuthMaynardJIteration.sourceHighFrequencyIntegral_le_time_neg100
#print axioms GuthMaynardJIteration.norm_sq_sourceLowOuterSum_le
#print axioms GuthMaynardJIteration.sourceLowFrequencyIntegral_from_finite_outer
