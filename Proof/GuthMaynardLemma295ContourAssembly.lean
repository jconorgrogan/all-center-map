import GuthMaynardLemma295DeepLeftSplit
import GuthMaynardLemma295DeepLeftExteriorEnvelope
import GuthMaynardLemma295ExactMHorizontal
import GuthMaynardLemma295VerticalIntegrability
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Cancellation of the common vertical edge in the two Lemma 29.5 rectangles. -/
namespace GuthMaynardLemma295ContourAssembly

open Complex Real Set MeasureTheory Filter Topology
open FinitePoleRectangle
open GuthMaynardLemma295DualTail
open GuthMaynardLemma295FiniteContour
open GuthMaynardLemma295ReflectedFiniteContour
open GuthMaynardLemma295DeepLeftSplit
open GuthMaynardLemma295DeepLeftCompactIntegral
open GuthMaynardLemma295DeepLeftExteriorEnvelope

open GuthMaynardLemma295VerticalIntegrability

noncomputable section

open GuthMaynardLemma295MellinLineTwo
open GuthMaynardLemma295LineTwoFubini
open GuthMaynardLemma295CutoffAnalytic

theorem intervalIntegral_raw_deepLeft_split
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K n : ℕ) (u v : ℝ) :
    (∫ t in u..v, lemma295RawIntegrand N g
      ((deepLeftSigma n : ℂ) + t * I)) =
    (∫ t in u..v, lemma295ReflectedFiniteIntegrand N g K
      ((deepLeftSigma n : ℂ) + t * I)) +
    (∫ t in u..v, lemma295DeepLeftTailIntegrand N g K n t) := by
  have hs : deepLeftSigma n < 1 := by
    unfold deepLeftSigma
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hf := (continuous_reflectedFinite_vertical hN g K hs).intervalIntegrable (μ := volume) u v
  have ht := (continuous_lemma295DeepLeftTailIntegrand hN g K n).intervalIntegrable (μ := volume) u v
  rw [← intervalIntegral.integral_add hf ht]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne g] with t ht
  exact fun _ => lemma295RawIntegrand_deepLeft_eq_finite_add_tail N g K n ht

/-- A finite identity in which the common deep-left finite polynomial cancels.
Only the literal dual tail remains on that vertical line. -/
theorem finite_twoRectangle_identity
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K n : ℕ)
    {B : ℝ} (hB : |g| + 1 < B) :
    I * (∫ t in (-B)..B, lemma295RawIntegrand N g ((2 : ℂ) + t * I)) =
      (2 * Real.pi * I) * lemma295PoleResidue N g +
      I * (∫ t in (-B)..B, lemma295ReflectedFiniteIntegrand N g K
        (((1/2 : ℝ) : ℂ) + t * I)) +
      I * (∫ t in (-B)..B, lemma295DeepLeftTailIntegrand N g K n t) +
      (∫ x in deepLeftSigma n..2,
        lemma295RawIntegrand N g ((x : ℂ) + B * I)) -
      (∫ x in deepLeftSigma n..2,
        lemma295RawIntegrand N g ((x : ℂ) + (-B) * I)) +
      (∫ x in deepLeftSigma n..(1/2),
        lemma295ReflectedFiniteIntegrand N g K ((x : ℂ) + (-B) * I)) -
      (∫ x in deepLeftSigma n..(1/2),
        lemma295ReflectedFiniteIntegrand N g K ((x : ℂ) + B * I)) := by
  have hs : deepLeftSigma n ≤ (1/2 : ℝ) := by
    unfold deepLeftSigma
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hr := finiteRectangle_lemma295_shift hN g
    (a := deepLeftSigma n) (c := 2) (u := -B) (v := B)
    (rad := 1/4) (by norm_num) (by linarith) (by norm_num)
    (by linarith [neg_abs_le g]) (by linarith [le_abs_self g])
  have hf := rectangleBoundaryIntegral_reflectedFinite_eq_zero hN g K
    (u := -B) (v := B) hs (by norm_num : (1/2 : ℝ) < 1)
  unfold rectangleBoundaryIntegral at hr hf
  rw [intervalIntegral_raw_deepLeft_split hN g K n (-B) B] at hr
  simp only [Complex.ofReal_neg] at hr hf ⊢
  linear_combination hr - hf

/-- Full-line contour identity with the literal discarded dual tail. -/
theorem fullLine_twoRectangle_identity
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K n : ℕ) :
    (∫ t : ℝ, lemma295RawIntegrand N g ((2 : ℂ) + t * I)) =
      (2 * Real.pi : ℂ) * lemma295PoleResidue N g +
      (∫ t : ℝ, lemma295ReflectedFiniteIntegrand N g K
        (((1/2 : ℝ) : ℂ) + t * I)) +
      (∫ t : ℝ, lemma295DeepLeftTailIntegrand N g K n t) := by
  let raw : ℝ → ℂ := fun t => lemma295RawIntegrand N g ((2 : ℂ) + t * I)
  let critical : ℝ → ℂ := fun t => lemma295ReflectedFiniteIntegrand N g K
    (((1/2 : ℝ) : ℂ) + t * I)
  let tail := lemma295DeepLeftTailIntegrand N g K n
  have hrInt : Integrable raw := integrable_lineTwoZetaIntegrand hN g
  have hcInt : Integrable critical := integrable_reflectedFinite_critical hN g K
  have htInt : Integrable tail := integrable_lemma295DeepLeftTailIntegrand hN g K n
  have hrLim := intervalIntegral_tendsto_integral hrInt
    tendsto_neg_atTop_atBot tendsto_id
  have hcLim := intervalIntegral_tendsto_integral hcInt
    tendsto_neg_atTop_atBot tendsto_id
  have htLim := intervalIntegral_tendsto_integral htInt
    tendsto_neg_atTop_atBot tendsto_id
  have hru := GuthMaynardLemma295RawHorizontalIntegral.tendsto_lemma295Raw_horizontalIntegral_zero hN g n
  have hrl := GuthMaynardLemma295RawHorizontalIntegral.tendsto_lemma295Raw_lowerHorizontalIntegral_zero hN g n
  have hfu := GuthMaynardLemma295HorizontalIntegral.tendsto_lemma295ReflectedFinite_horizontalIntegral_zero hN g K n
  have hfl := GuthMaynardLemma295HorizontalIntegral.tendsto_lemma295ReflectedFinite_lowerHorizontalIntegral_zero hN g K n
  have hconst : Tendsto (fun _ : ℝ => (2 * Real.pi * I) * lemma295PoleResidue N g)
      atTop (𝓝 ((2 * Real.pi * I) * lemma295PoleResidue N g)) := tendsto_const_nhds
  have hright := (((((hconst.add (hcLim.const_mul I)).add
    (htLim.const_mul I)).add hru).sub hrl).add hfl).sub hfu
  have hevent : (fun B : ℝ => I * ∫ t in (-B)..B, raw t) =ᶠ[atTop]
      (fun B : ℝ =>
        (2 * Real.pi * I) * lemma295PoleResidue N g +
        I * (∫ t in (-B)..B, critical t) + I * (∫ t in (-B)..B, tail t) +
        (∫ x in deepLeftSigma n..2, lemma295RawIntegrand N g ((x : ℂ) + B * I)) -
        (∫ x in deepLeftSigma n..2, lemma295RawIntegrand N g ((x : ℂ) + (-B) * I)) +
        (∫ x in deepLeftSigma n..(1/2), lemma295ReflectedFiniteIntegrand N g K ((x : ℂ) + (-B) * I)) -
        (∫ x in deepLeftSigma n..(1/2), lemma295ReflectedFiniteIntegrand N g K ((x : ℂ) + B * I))) := by
    filter_upwards [eventually_gt_atTop (|g| + 1)] with B hB
    exact finite_twoRectangle_identity hN g K n hB
  have hlimEq := tendsto_nhds_unique (hrLim.const_mul I) (hright.congr' hevent.symm)
  simp only [add_zero, sub_zero] at hlimEq
  apply mul_left_cancel₀ I_ne_zero
  dsimp [raw, critical, tail] at hlimEq
  linear_combination hlimEq


/-- The normalized source sum equals the residue, the retained critical
integral, and the literal deep-left remainder. -/
theorem sourceHPlusSum_eq_residue_add_critical_add_tail
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K n : ℕ) :
    GuthMaynardJutilaReflection2941.sourceHPlusSum N g =
      lemma295PoleResidue N g +
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, lemma295ReflectedFiniteIntegrand N g K
          (((1/2 : ℝ) : ℂ) - t * I)) +
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, lemma295DeepLeftTailIntegrand N g K n t) := by
  have hc : (((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * Real.pi : ℂ)) = 1 := by
    push_cast
    field_simp [Real.pi_ne_zero]
  have hreverse :
      (∫ t : ℝ, lemma295ReflectedFiniteIntegrand N g K
        (((1/2 : ℝ) : ℂ) - t * I)) =
      (∫ t : ℝ, lemma295ReflectedFiniteIntegrand N g K
        (((1/2 : ℝ) : ℂ) + t * I)) := by
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using
      (integral_neg_eq_self (fun t : ℝ => lemma295ReflectedFiniteIntegrand N g K
        (((1/2 : ℝ) : ℂ) + t * I)) volume)
  rw [hreverse, sourceHPlusSum_eq_lineTwo_zeta_integral hN g]
  change (((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ, lemma295RawIntegrand N g ((2 : ℂ) + t * I)) = _
  rw [fullLine_twoRectangle_identity hN g K n, mul_add, mul_add, ← mul_assoc, hc, one_mul]


theorem norm_sourceHPlusSum_le_residue_add_critical_add_tail
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K n : ℕ) :
    ‖GuthMaynardJutilaReflection2941.sourceHPlusSum N g‖ ≤
      ‖lemma295PoleResidue N g‖ +
      (1 / (2 * Real.pi)) *
        ‖∫ t : ℝ, lemma295ReflectedFiniteIntegrand N g K
          (((1/2 : ℝ) : ℂ) - t * I)‖ +
      (1 / (2 * Real.pi)) *
        ‖∫ t : ℝ, lemma295DeepLeftTailIntegrand N g K n t‖ := by
  rw [sourceHPlusSum_eq_residue_add_critical_add_tail hN g K n]
  have hc : ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    _ ≤ ‖lemma295PoleResidue N g +
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, lemma295ReflectedFiniteIntegrand N g K
          (((1/2 : ℝ) : ℂ) - t * I))‖ +
      ‖(((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, lemma295DeepLeftTailIntegrand N g K n t)‖ := norm_add_le _ _
    _ ≤ (‖lemma295PoleResidue N g‖ +
      ‖(((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, lemma295ReflectedFiniteIntegrand N g K
          (((1/2 : ℝ) : ℂ) - t * I))‖) +
      ‖(((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, lemma295DeepLeftTailIntegrand N g K n t)‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by rw [norm_mul, norm_mul, hc]


end
end GuthMaynardLemma295ContourAssembly

#print axioms GuthMaynardLemma295ContourAssembly.intervalIntegral_raw_deepLeft_split
#print axioms GuthMaynardLemma295ContourAssembly.finite_twoRectangle_identity

#print axioms GuthMaynardLemma295ContourAssembly.fullLine_twoRectangle_identity

#print axioms GuthMaynardLemma295ContourAssembly.sourceHPlusSum_eq_residue_add_critical_add_tail

#print axioms GuthMaynardLemma295ContourAssembly.norm_sourceHPlusSum_le_residue_add_critical_add_tail
