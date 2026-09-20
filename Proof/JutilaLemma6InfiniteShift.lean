import JutilaLemma6VerticalIntegrability
import JutilaLemma6HorizontalDecay
import JutilaLemma6SelectedRightLine

/-! Infinite-height passage and the literal Lemma 6 error-integral identity. -/
namespace MAPJutilaLemma6InfiniteShift
open Complex Real MeasureTheory Set Filter Topology
open MAPJutilaLemma6FiniteContour MAPJutilaLemma6ErrorBound MAPJutilaLemma6VerticalIntegrability
open MAPJutilaLemma6HorizontalDecay MAPJutilaLemma6SelectedRightLine MAPJutilaMEntire
open MAPJutilaLemma1OuterSum
noncomputable section

theorem detector_right_eq_errorIntegral
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1) (xi : ℕ → ℂ)
    {D S : Finset ℕ} {z2 R : ℕ}
    (hDcard : D.card ≤ z2) (hDpos : ∀ d ∈ D, 0 < d)
    (hxi : ∀ d ∈ D, ‖xi d‖ ≤ 1) (hS : S ⊆ Finset.Icc 1 R)
    (hSq : ∀ r ∈ S, Squarefree r) (hcop : ∀ r ∈ S, r.Coprime q)
    {beta omega t X : ℝ} (homega : 0 < omega)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta ≤ 1 - omega) (hX : 1 ≤ X)
    (hrho : DirichletCharacter.LFunction chi (lemmaSixZeroPoint beta t) = 0) :
    (∫ u : ℝ, jutilaDetectorExtension chi (lemmaSixZeroPoint beta t)
      xi D S X ((1 : ℂ) + u * I)) =
    ∫ u : ℝ, lemmaSixMellinErrorIntegrand chi xi D S beta t X u := by
  let F := jutilaDetectorExtension chi (lemmaSixZeroPoint beta t) xi D S X
  let Rv : ℝ → ℂ := fun B => ∫ u : ℝ in -B..B, F ((1 : ℂ) + u * I)
  let Lv : ℝ → ℂ := fun B => ∫ u : ℝ in -B..B, F (((-beta : ℝ) : ℂ) + u * I)
  let Hm : ℝ → ℂ := fun B => ∫ x : ℝ in -beta..1, F ((x : ℂ) - B * I)
  let Hp : ℝ → ℂ := fun B => ∫ x : ℝ in -beta..1, F ((x : ℂ) + B * I)
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hrightInt := integrable_detector_rightOne chi hchi (lemmaSixZeroPoint beta t) xi hDpos S hXpos
    (by simp [lemmaSixZeroPoint]; linarith) (by simp [lemmaSixZeroPoint]; linarith) hrho
  have hleftInt := integrable_detector_left chi hprim hchi xi hDcard hDpos hxi hS hSq hcop
    homega hbetaLo hbetaHi hXpos hrho
  have hR : Tendsto Rv atTop (𝓝 (∫ u : ℝ, F ((1 : ℂ) + u * I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hrightInt Filter.tendsto_neg_atTop_atBot tendsto_id
  have hL : Tendsto Lv atTop (𝓝 (∫ u : ℝ, F (((-beta : ℝ) : ℂ) + u * I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hleftInt Filter.tendsto_neg_atTop_atBot tendsto_id
  have hm : Tendsto Hm atTop (𝓝 0) := by
    simpa [Hm, F, lemmaSixZeroPoint, sub_eq_add_neg, neg_mul] using
      tendsto_detector_horizontal_zero chi hchi hrho xi hDpos S hX
        (by simp [lemmaSixZeroPoint]; linarith : 0 ≤ (lemmaSixZeroPoint beta t).re)
        (by simp [lemmaSixZeroPoint]; linarith : (lemmaSixZeroPoint beta t).re ≤ 1)
        (ε := -1) (by norm_num)
  have hp : Tendsto Hp atTop (𝓝 0) := by
    simpa [Hp, F, lemmaSixZeroPoint] using
      tendsto_detector_horizontal_zero chi hchi hrho xi hDpos S hX
        (by simp [lemmaSixZeroPoint]; linarith : 0 ≤ (lemmaSixZeroPoint beta t).re)
        (by simp [lemmaSixZeroPoint]; linarith : (lemmaSixZeroPoint beta t).re ≤ 1)
        (ε := 1) (by norm_num)
  have heq : ∀ᶠ B : ℝ in atTop, Rv B = Lv B + I * (Hm B - Hp B) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    have hf := finiteRectangle_jutilaDetector_shift chi hchi (lemmaSixZeroPoint beta t)
      xi hDpos S hXpos (a := -beta) (c := 1) (B := B) (by linarith) (by linarith) hB
    change Hm B - Hp B + I * Rv B - I * Lv B = 0 at hf
    have hh := congrArg (fun z : ℂ => (-I) * z) hf
    simp [mul_add, mul_sub, ← mul_assoc, Complex.I_mul_I] at hh
    linear_combination hh
  have hcombo : Tendsto (fun B => Lv B + I * (Hm B - Hp B)) atTop
      (𝓝 ((∫ u : ℝ, F (((-beta : ℝ) : ℂ) + u * I)) + I * (0 - 0))) :=
    hL.add (tendsto_const_nhds.mul (hm.sub hp))
  have hR' := hcombo.congr' (Filter.EventuallyEq.symm heq)
  have hv : (∫ u : ℝ, F ((1 : ℂ) + u * I)) =
      ∫ u : ℝ, F (((-beta : ℝ) : ℂ) + u * I) := by
    simpa using tendsto_nhds_unique hR hR'
  calc
    _ = ∫ u : ℝ, F (((-beta : ℝ) : ℂ) + u * I) := hv
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      simpa only [F, lemmaSixLeftPoint, Complex.ofReal_neg] using
        jutilaDetectorExtension_left_eq_errorIntegrand chi xi D S (u := u) (by linarith) hrho

/-- Literal selected-series form of Jutila's equation (2.11), with the
infinite contour shift completely discharged. -/
theorem selectedSmoothedSeries_eq_errorIntegral
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1) (xi : ℕ → ℂ)
    {D S : Finset ℕ} {z2 R : ℕ}
    (hDcard : D.card ≤ z2) (hDpos : ∀ d ∈ D, 0 < d)
    (hxi : ∀ d ∈ D, ‖xi d‖ ≤ 1) (hS : S ⊆ Finset.Icc 1 R)
    (hSq : ∀ r ∈ S, Squarefree r) (hcop : ∀ r ∈ S, r.Coprime q)
    {beta omega t X : ℝ} (homega : 0 < omega)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta ≤ 1 - omega) (hX : 1 ≤ X)
    (hrho : DirichletCharacter.LFunction chi (lemmaSixZeroPoint beta t) = 0) :
    (∑' n : ℕ, LSeries.term (jutilaEquation22SelectedCoeff chi xi D S)
      (lemmaSixZeroPoint beta t) n * (Real.exp (-((n : ℝ) / X)) : ℂ)) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ, lemmaSixMellinErrorIntegrand chi xi D S beta t X u) := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  rw [jutilaSelectedSmoothedSeries_eq_gamma_rightLine chi xi
    (fun d hd => (hDpos d hd).ne') hS hSq hcop (c := 1) (by norm_num) hXpos
    (lemmaSixZeroPoint beta t) (by simp [lemmaSixZeroPoint]; linarith)]
  have hpoint : (∫ v : ℝ,
      DirichletCharacter.LFunction chi (lemmaSixZeroPoint beta t + ((1 : ℂ) + v * I)) *
        jutilaMWeightedSumComplex chi xi D S (lemmaSixZeroPoint beta t + ((1 : ℂ) + v * I)) *
        Complex.Gamma ((1 : ℂ) + v * I) * (X : ℂ)^((1 : ℂ) + v * I)) =
      ∫ v : ℝ, jutilaDetectorExtension chi (lemmaSixZeroPoint beta t) xi D S X ((1 : ℂ) + v * I) := by
    apply integral_congr_ae
    filter_upwards with v
    rw [jutilaDetectorExtension_eq_raw chi xi D S X hrho (by
      intro h; have := congrArg Complex.re h; simp at this)]
    ring
  simp only [Complex.ofReal_one]
  rw [hpoint, detector_right_eq_errorIntegral chi hprim hchi xi hDcard hDpos hxi hS hSq hcop
    homega hbetaLo hbetaHi hX hrho]

end
end MAPJutilaLemma6InfiniteShift
#print axioms MAPJutilaLemma6InfiniteShift.detector_right_eq_errorIntegral

#print axioms MAPJutilaLemma6InfiniteShift.selectedSmoothedSeries_eq_errorIntegral
