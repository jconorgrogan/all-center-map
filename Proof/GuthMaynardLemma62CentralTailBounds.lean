import GuthMaynardLemma62AbsoluteMellinTail

/-!
# Central and exterior bounds in Guth--Maynard Lemma 6.2

This file combines the exact reflected formula with the stationary-phase
estimate on the central Mellin window and an absolute crude kernel bound on
the exterior.  The dyadic length is kept literal, so the logarithmic number
of reflection blocks is visible.
-/

namespace GuthMaynardLemma62CentralTailBounds

open Real Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap BigOperators
open GuthMaynardSectionThreeCutoff
open GuthMaynardLemma62FarTail
open GuthMaynardLemma62MellinInversion
open GuthMaynardLemma62ReflectionSubstitution
open GuthMaynardLemma62AbsoluteMellinTail
open GuthMaynardReflectionKernelVdC
open MAPMRTCorollary53Source

noncomputable section

def reflectedInner (tau N M : ℝ) : ℂ :=
  ∫ v : ℝ in N..(2 * N * M),
    additivePhase (reflectionPhase tau v) * reflectionAmplitude v

def positiveReflectedOuter (t N M r : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I) *
      reflectionScalePhase (t - r) 1) *
    reflectedInner (t - r) N M

/-- The phase scale may be arbitrary in the coefficient formula; its norm is
one and therefore disappears from every analytic estimate. -/
def positiveReflectedOuterAtScale (t N M c r : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I) *
      reflectionScalePhase (t - r) c) *
    reflectedInner (t - r) N M

theorem reflectedInner_intervalIntegrable
    {tau N M : ℝ} (hN : 0 < N) (hM : 0 < M) :
    IntervalIntegrable
      (fun v : ℝ =>
        additivePhase (reflectionPhase tau v) * reflectionAmplitude v)
      volume N (2 * N * M) :=
  reflectionKernel_intervalIntegrable hN (by positivity)

/-- Absolute bound for the reflection kernel, uniform in `tau`. -/
theorem norm_reflectedInner_le_log
    {tau N M : ℝ} (hN : 0 < N) (hM : 1 ≤ M) :
    ‖reflectedInner tau N M‖ ≤ Real.log (2 * M) := by
  have hEnd : N ≤ 2 * N * M := by
    nlinarith [mul_pos hN (show 0 < M by linarith)]
  have hInvInt : IntervalIntegrable (fun v : ℝ => v⁻¹) volume N (2 * N * M) := by
    apply ContinuousOn.intervalIntegrable
    intro v hv
    rw [Set.uIcc_of_le hEnd] at hv
    exact (continuousAt_inv₀ (ne_of_gt (hN.trans_le hv.1))).continuousWithinAt
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hEnd
    (f := fun v : ℝ =>
      additivePhase (reflectionPhase tau v) * reflectionAmplitude v)
    (g := fun v : ℝ => v⁻¹)
    (by
      filter_upwards with v hv
      have hvPos : 0 < v := hN.trans hv.1
      rw [norm_mul, norm_reflectionAmplitude hvPos]
      unfold additivePhase
      rw [Complex.norm_exp]
      simp)
    hInvInt
  unfold reflectedInner
  calc
    ‖∫ v : ℝ in N..2 * N * M,
        additivePhase (reflectionPhase tau v) * reflectionAmplitude v‖ ≤
      ∫ v : ℝ in N..2 * N * M, v⁻¹ := hnorm
    _ = Real.log (2 * N * M / N) := by
      rw [integral_inv]
      rw [Set.uIcc_of_le hEnd]
      intro hz
      exact (not_le_of_gt hN) hz.1
    _ = Real.log (2 * M) := by
      congr 1
      field_simp [hN.ne']

/-- On an exact dyadic reflection range, stationary phase gives the literal
`tau⁻¹/²` saving with the block count exposed. -/
theorem norm_reflectedInner_dyadic_le
    {tau N : ℝ} (htau : 0 < tau) (hN : 0 < N) (J : ℕ) :
    ‖reflectedInner tau N ((2 : ℝ) ^ J)‖ ≤
      (J + 1) * (20 * Real.sqrt (8 * Real.pi) / Real.sqrt tau) := by
  unfold reflectedInner
  convert norm_reflectionKernelDyadicUnion_le htau hN (J + 1) using 1
  unfold dyadicPoint
  rw [pow_succ]
  · ring
  · simp [Nat.cast_add]

theorem norm_positiveReflectedOuterAtScale_le_log
    {t N M c r : ℝ} (hN : 0 < N) (hM : 1 ≤ M) :
    ‖positiveReflectedOuterAtScale t N M c r‖ ≤
      (1 / (2 * Real.pi)) * Real.log (2 * M) *
        ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ := by
  unfold positiveReflectedOuterAtScale
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi)),
    norm_reflectionScalePhase]
  have hinner := norm_reflectedInner_le_log (tau := t - r) hN hM
  calc
    1 / (2 * Real.pi) *
        ‖mellin sectionThreeCutoff (1 + ↑r * I)‖ * 1 *
        ‖reflectedInner (t - r) N M‖ =
      (1 / (2 * Real.pi) *
        ‖mellin sectionThreeCutoff (1 + ↑r * I)‖) *
        ‖reflectedInner (t - r) N M‖ := by ring
    _ ≤ (1 / (2 * Real.pi) *
        ‖mellin sectionThreeCutoff (1 + ↑r * I)‖) *
        Real.log (2 * M) := by
      exact mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = _ := by ring

/-- Central Mellin-window pointwise bound. -/
theorem norm_positiveReflectedOuterAtScale_central_le
    {t N R c r : ℝ} (hN : 0 < N) (_hR : 0 < R) (htR : R < t)
    (hr : r ∈ Set.Ioc (-R) R) (J : ℕ) :
    ‖positiveReflectedOuterAtScale t N ((2 : ℝ) ^ J) c r‖ ≤
      ((1 / (2 * Real.pi)) *
        ((J + 1) * (20 * Real.sqrt (8 * Real.pi) /
          Real.sqrt (t - R)))) *
        ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ := by
  have htau : 0 < t - r := by linarith [hr.2]
  have htRPos : 0 < t - R := by linarith
  have hsqrt : Real.sqrt (t - R) ≤ Real.sqrt (t - r) := by
    exact Real.sqrt_le_sqrt (by linarith [hr.2])
  have hdiv :
      20 * Real.sqrt (8 * Real.pi) / Real.sqrt (t - r) ≤
        20 * Real.sqrt (8 * Real.pi) / Real.sqrt (t - R) := by
    exact div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 htRPos) hsqrt
  have hinner := norm_reflectedInner_dyadic_le htau hN J
  unfold positiveReflectedOuterAtScale
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi)),
    norm_reflectionScalePhase]
  have hJ : (0 : ℝ) ≤ J + 1 := by positivity
  calc
    1 / (2 * Real.pi) *
        ‖mellin sectionThreeCutoff (1 + ↑r * I)‖ * 1 *
        ‖reflectedInner (t - r) N (2 ^ J)‖ ≤
      (1 / (2 * Real.pi) *
        ‖mellin sectionThreeCutoff (1 + ↑r * I)‖) *
        ((J + 1) *
          (20 * Real.sqrt (8 * Real.pi) / Real.sqrt (t - r))) := by
            calc
              1 / (2 * Real.pi) *
                  ‖mellin sectionThreeCutoff (1 + ↑r * I)‖ * 1 *
                  ‖reflectedInner (t - r) N (2 ^ J)‖ =
                (1 / (2 * Real.pi) *
                  ‖mellin sectionThreeCutoff (1 + ↑r * I)‖) *
                  ‖reflectedInner (t - r) N (2 ^ J)‖ := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ 1 / (2 * Real.pi) *
        ‖mellin sectionThreeCutoff (1 + ↑r * I)‖ *
        ((J + 1) *
          (20 * Real.sqrt (8 * Real.pi) / Real.sqrt (t - R))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hdiv hJ) (by positivity)
    _ = _ := by ring

theorem integrable_positiveReflectedOuterAtScale_source
    {t N m M : ℝ} (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    Integrable (positiveReflectedOuterAtScale t N M (m * N)) := by
  have h := integrable_positiveReflectedMellin (t := t) hN hm hmM
  apply h.congr
  filter_upwards with r
  unfold positiveReflectedOuterAtScale reflectedInner
  ring

/-- The exact reflected formula split into the central Mellin window and its
exterior.  The half-open convention makes the two sets literally disjoint and
their union literally all of `ℝ`. -/
theorem sectionThreeFourierCoefficient_eq_central_add_exterior
    {t N m M R : ℝ} (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hR : 0 < R) :
    sectionThreeFourierCoefficient t (m * N) =
      (∫ r : ℝ in Set.Ioc (-R) R,
        positiveReflectedOuterAtScale t N M (m * N) r) +
      (∫ r : ℝ in (Set.Iic (-R) ∪ Set.Ioi R),
        positiveReflectedOuterAtScale t N M (m * N) r) := by
  rw [sectionThreeFourierCoefficient_eq_positiveReflectedMellin hN hm hmM]
  change (∫ r : ℝ, positiveReflectedOuterAtScale t N M (m * N) r) = _
  have hInt := integrable_positiveReflectedOuterAtScale_source
    (t := t) hN hm hmM
  have hDisjoint : Disjoint (Set.Ioc (-R) R)
      (Set.Iic (-R) ∪ Set.Ioi R) := by
    rw [Set.disjoint_union_right]
    constructor <;> exact Set.disjoint_left.2 (by
      intro x hx hy
      simp only [Set.mem_Ioc, Set.mem_Iic, Set.mem_Ioi] at hx hy
      linarith)
  have hUnion : Set.Ioc (-R) R ∪ (Set.Iic (-R) ∪ Set.Ioi R) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Iic, Set.mem_Ioi,
      Set.mem_univ, iff_true]
    by_cases hx : x ≤ -R
    · exact Or.inr (Or.inl hx)
    · have hx' : -R < x := lt_of_not_ge hx
      by_cases hxR : x ≤ R
      · exact Or.inl ⟨hx', hxR⟩
      · exact Or.inr (Or.inr (lt_of_not_ge hxR))
  rw [← MeasureTheory.setIntegral_univ, ← hUnion]
  exact MeasureTheory.setIntegral_union hDisjoint
    (measurableSet_Iic.union measurableSet_Ioi)
    hInt.integrableOn hInt.integrableOn

/-- Exterior reflected contribution, now controlled by the *absolute* Mellin
tail rather than the insufficient norm of its integral. -/
theorem norm_positiveReflected_exterior_le
    {t N m M R : ℝ} {k : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hR : 0 < R) (hk : 2 ≤ k) :
    ‖∫ r : ℝ in (Set.Iic (-R) ∪ Set.Ioi R),
        positiveReflectedOuterAtScale t N M (m * N) r‖ ≤
      (1 / (2 * Real.pi)) * Real.log (2 * M) *
        (2 * (((2 * Real.pi) ^ k * sectionThreeMellinSeminorm k) *
          (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)))) := by
  have hM : 1 ≤ M := hm.trans hmM
  let B : ℝ := (1 / (2 * Real.pi)) * Real.log (2 * M)
  have hB : 0 ≤ B := by
    unfold B
    have hlog : 0 ≤ Real.log (2 * M) := Real.log_nonneg (by nlinarith)
    positivity
  have hMellin := sectionThreeCutoff_verticalIntegrable.norm
  have hmajor : Integrable (fun r : ℝ =>
      B * ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖) :=
    hMellin.const_mul B
  have hnorm :
      ‖∫ r : ℝ in (Set.Iic (-R) ∪ Set.Ioi R),
          positiveReflectedOuterAtScale t N M (m * N) r‖ ≤
        ∫ r : ℝ in (Set.Iic (-R) ∪ Set.Ioi R),
          B * ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmajor.integrableOn
    filter_upwards with r
    simpa [B] using
      (norm_positiveReflectedOuterAtScale_le_log
        (t := t) (c := m * N) (r := r) hN hM)
  calc
    ‖∫ r : ℝ in (Set.Iic (-R) ∪ Set.Ioi R),
        positiveReflectedOuterAtScale t N M (m * N) r‖ ≤
      ∫ r : ℝ in (Set.Iic (-R) ∪ Set.Ioi R),
        B * ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ := hnorm
    _ = B * (∫ r : ℝ in (Set.Iic (-R) ∪ Set.Ioi R),
        ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖) := by
          rw [MeasureTheory.integral_const_mul]
    _ ≤ B * (2 * (((2 * Real.pi) ^ k * sectionThreeMellinSeminorm k) *
          (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)))) :=
      mul_le_mul_of_nonneg_left
        (integral_exterior_norm_sectionThreeMellin_le hk hR) hB
    _ = _ := rfl

/-- Per-frequency approximate functional equation with an explicit,
arbitrary-order exterior error. -/
theorem norm_sectionThreeFourierCoefficient_sub_central_le
    {t N m M R : ℝ} {k : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hR : 0 < R) (hk : 2 ≤ k) :
    ‖sectionThreeFourierCoefficient t (m * N) -
        ∫ r : ℝ in Set.Ioc (-R) R,
          positiveReflectedOuterAtScale t N M (m * N) r‖ ≤
      (1 / (2 * Real.pi)) * Real.log (2 * M) *
        (2 * (((2 * Real.pi) ^ k * sectionThreeMellinSeminorm k) *
          (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)))) := by
  rw [sectionThreeFourierCoefficient_eq_central_add_exterior
    hN hm hmM hR]
  rw [add_sub_cancel_left]
  exact norm_positiveReflected_exterior_le hN hm hmM hR hk

end

end GuthMaynardLemma62CentralTailBounds

#print axioms GuthMaynardLemma62CentralTailBounds.norm_reflectedInner_le_log
#print axioms GuthMaynardLemma62CentralTailBounds.norm_reflectedInner_dyadic_le
#print axioms GuthMaynardLemma62CentralTailBounds.norm_positiveReflectedOuterAtScale_central_le
