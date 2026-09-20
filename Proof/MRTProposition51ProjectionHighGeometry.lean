import MRTProposition51FirstAnalytic

/-!
# MRT Proposition 5.1: the rescaled-window geometry in the high projection

This module formalizes the change of variables and finite window covering used
on MRT p.46, lines 2343--2365.  In particular, it does not package the claimed
high-frequency estimate as an input.  It proves that every centered window
`|x-λn| ≤ H`, uniformly for `1/2 ≤ λ ≤ 2`, has square integral controlled by
the literal one-sided `ordinarySlidingMass` occurring in Proposition 5.1.
-/

namespace MAPMRTProposition51ProjectionHighGeometry

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51FirstAnalytic

noncomputable section

/-- The nonnegative coefficient window printed on MRT p.46 after (77), with
the harmless `O(H)` made concrete as the closed centered window of radius `H`.
The coefficient support is exactly the support used by `ordinarySlidingMass`.
-/
def scaledCenteredWindowSum
    (X H lambda : ℝ) (f : ℕ → ℂ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    if |x - lambda * n| ≤ H then ‖f n‖ else 0

theorem scaledCenteredWindowSum_nonneg
    (X H lambda : ℝ) (f : ℕ → ℂ) (x : ℝ) :
    0 ≤ scaledCenteredWindowSum X H lambda f x := by
  unfold scaledCenteredWindowSum
  positivity

/-- Four adjacent one-sided `H`-windows cover the centered radius-`2H`
window.  This is the precise finite covering hidden in "rescaling x by λ and
using the triangle inequality" on MRT p.46. -/
theorem scaledCenteredWindowSum_mul_le_four_windows
    {X H lambda y : ℝ} {f : ℕ → ℂ}
    (hH : 0 ≤ H) (hlower : 1 / 2 ≤ lambda) :
    scaledCenteredWindowSum X H lambda f (lambda * y) ≤
      ordinaryWindowSum X H f (y - 2 * H) +
      ordinaryWindowSum X H f (y - H) +
      ordinaryWindowSum X H f y +
      ordinaryWindowSum X H f (y + H) := by
  unfold scaledCenteredWindowSum ordinaryWindowSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hc : |lambda * y - lambda * (n : ℝ)| ≤ H
  · rw [if_pos hc]
    have hlpos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlower
    have habs : lambda * |y - (n : ℝ)| ≤ H := by
      rw [← abs_of_pos hlpos, ← abs_mul]
      convert hc using 1 <;> ring
    have hdist : |y - (n : ℝ)| ≤ 2 * H := by
      have hmul := mul_le_mul_of_nonneg_left hlower (abs_nonneg (y - (n : ℝ)))
      nlinarith
    rw [abs_le] at hdist
    have hleft : y - 2 * H ≤ (n : ℝ) := by linarith [hdist.1]
    have hright : (n : ℝ) ≤ y + 2 * H := by linarith [hdist.2]
    by_cases h₁ : (n : ℝ) ≤ y - H
    · have hm : y - 2 * H ≤ (n : ℝ) ∧
          (n : ℝ) ≤ (y - 2 * H) + H := by
        constructor <;> linarith
      rw [if_pos hm]
      split_ifs <;> nlinarith [norm_nonneg (f n)]
    · by_cases h₂ : (n : ℝ) ≤ y
      · have hm : y - H ≤ (n : ℝ) ∧ (n : ℝ) ≤ (y - H) + H := by
          constructor <;> linarith
        rw [if_pos hm]
        split_ifs <;> nlinarith [norm_nonneg (f n)]
      · by_cases h₃ : (n : ℝ) ≤ y + H
        · have hm : y ≤ (n : ℝ) ∧ (n : ℝ) ≤ y + H := by
            constructor <;> linarith
          rw [if_pos hm]
          split_ifs <;> nlinarith [norm_nonneg (f n)]
        · have hm : y + H ≤ (n : ℝ) ∧
              (n : ℝ) ≤ (y + H) + H := by
            constructor <;> linarith
          rw [if_pos hm]
          split_ifs <;> nlinarith [norm_nonneg (f n)]
  · rw [if_neg hc]
    positivity

/-- Squaring the four-window cover costs at most `4`. -/
theorem scaledCenteredWindowSum_mul_sq_le_four_windows
    {X H lambda y : ℝ} {f : ℕ → ℂ}
    (hH : 0 ≤ H) (hlower : 1 / 2 ≤ lambda) :
    scaledCenteredWindowSum X H lambda f (lambda * y) ^ 2 ≤
      4 * (ordinaryWindowSum X H f (y - 2 * H) ^ 2 +
        ordinaryWindowSum X H f (y - H) ^ 2 +
        ordinaryWindowSum X H f y ^ 2 +
        ordinaryWindowSum X H f (y + H) ^ 2) := by
  have hcover := scaledCenteredWindowSum_mul_le_four_windows
    (X := X) (f := f) (y := y) hH hlower
  have h0 := scaledCenteredWindowSum_nonneg X H lambda f (lambda * y)
  have ha := ordinaryWindowSum_nonneg X H f (y - 2 * H)
  have hb := ordinaryWindowSum_nonneg X H f (y - H)
  have hc := ordinaryWindowSum_nonneg X H f y
  have hd := ordinaryWindowSum_nonneg X H f (y + H)
  nlinarith [
    sq_nonneg (ordinaryWindowSum X H f (y - 2 * H) -
      ordinaryWindowSum X H f (y - H)),
    sq_nonneg (ordinaryWindowSum X H f (y - 2 * H) -
      ordinaryWindowSum X H f y),
    sq_nonneg (ordinaryWindowSum X H f (y - 2 * H) -
      ordinaryWindowSum X H f (y + H)),
    sq_nonneg (ordinaryWindowSum X H f (y - H) -
      ordinaryWindowSum X H f y),
    sq_nonneg (ordinaryWindowSum X H f (y - H) -
      ordinaryWindowSum X H f (y + H)),
    sq_nonneg (ordinaryWindowSum X H f y -
      ordinaryWindowSum X H f (y + H))]

theorem integrable_sq_scaledCenteredWindowSum
    (X H lambda : ℝ) (f : ℕ → ℂ) :
    Integrable (fun x : ℝ ↦ scaledCenteredWindowSum X H lambda f x ^ 2) := by
  -- Expanding the square first would create cross terms.  Instead use the
  -- finite coefficient-mass bound to dominate the square by a constant times
  -- the integrable unsquared window.
  have hsumInt : Integrable (scaledCenteredWindowSum X H lambda f) := by
    unfold scaledCenteredWindowSum
    apply integrable_finset_sum
    intro m hm
    have hi :
        (fun x : ℝ ↦ if |x - lambda * (m : ℝ)| ≤ H then ‖f m‖ else 0) =
          (Set.Icc (lambda * m - H) (lambda * m + H)).indicator
            (fun _ : ℝ ↦ ‖f m‖) := by
      funext x
      by_cases hx : |x - lambda * (m : ℝ)| ≤ H
      · have hmem : x ∈ Set.Icc (lambda * m - H) (lambda * m + H) := by
          rw [abs_le] at hx
          constructor <;> linarith
        simp [hx, hmem]
      · have hnot : x ∉ Set.Icc (lambda * m - H) (lambda * m + H) := by
          intro hmem
          apply hx
          rw [abs_le]
          constructor <;> linarith [hmem.1, hmem.2]
        simp [hx, hnot]
    rw [hi]
    exact (integrableOn_const (C := ‖f m‖) measure_Icc_lt_top.ne)
      |>.integrable_indicator measurableSet_Icc
  let C := coefficientMass X f
  have hbound : ∀ x, ‖scaledCenteredWindowSum X H lambda f x‖ ≤ C := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (scaledCenteredWindowSum_nonneg X H lambda f x)]
    unfold scaledCenteredWindowSum C coefficientMass
    apply Finset.sum_le_sum
    intro m hm
    split_ifs <;> simp
  have hmul := hsumInt.bdd_mul hsumInt.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  simpa [pow_two] using hmul

/-- The square integral of the rescaled centered window is at most `16` times
the exact source sliding mass. -/
theorem integral_sq_scaledCenteredWindowSum_mul_le
    {X H lambda : ℝ} {f : ℕ → ℂ}
    (hH : 0 ≤ H) (hlower : 1 / 2 ≤ lambda) :
    (∫ y : ℝ, scaledCenteredWindowSum X H lambda f (lambda * y) ^ 2) ≤
      16 * ordinarySlidingMass X H f := by
  have hrightBase := integrable_sq_ordinaryWindowSum X H f
  have hA : Integrable (fun y : ℝ ↦
      ordinaryWindowSum X H f (y - 2 * H) ^ 2) := by
    simpa [sub_eq_add_neg] using hrightBase.comp_add_right (-2 * H)
  have hB : Integrable (fun y : ℝ ↦
      ordinaryWindowSum X H f (y - H) ^ 2) := by
    simpa [sub_eq_add_neg] using hrightBase.comp_add_right (-H)
  have hC : Integrable (fun y : ℝ ↦
      ordinaryWindowSum X H f y ^ 2) := hrightBase
  have hD : Integrable (fun y : ℝ ↦
      ordinaryWindowSum X H f (y + H) ^ 2) :=
    hrightBase.comp_add_right H
  have hright : Integrable (fun y : ℝ ↦
      4 * (ordinaryWindowSum X H f (y - 2 * H) ^ 2 +
        ordinaryWindowSum X H f (y - H) ^ 2 +
        ordinaryWindowSum X H f y ^ 2 +
        ordinaryWindowSum X H f (y + H) ^ 2)) := by
    exact (((hA.add hB).add hC).add hD).const_mul 4
  have hAB :
      (∫ y : ℝ, ordinaryWindowSum X H f (y - 2 * H) ^ 2 +
        ordinaryWindowSum X H f (y - H) ^ 2) =
      (∫ y : ℝ, ordinaryWindowSum X H f (y - 2 * H) ^ 2) +
        ∫ y : ℝ, ordinaryWindowSum X H f (y - H) ^ 2 := by
    simpa only [Pi.add_apply] using integral_add hA hB
  have hABC :
      (∫ y : ℝ, (ordinaryWindowSum X H f (y - 2 * H) ^ 2 +
        ordinaryWindowSum X H f (y - H) ^ 2) +
          ordinaryWindowSum X H f y ^ 2) =
      (∫ y : ℝ, ordinaryWindowSum X H f (y - 2 * H) ^ 2 +
        ordinaryWindowSum X H f (y - H) ^ 2) +
        ∫ y : ℝ, ordinaryWindowSum X H f y ^ 2 := by
    simpa only [Pi.add_apply] using integral_add (hA.add hB) hC
  have hABCD :
      (∫ y : ℝ, ((ordinaryWindowSum X H f (y - 2 * H) ^ 2 +
        ordinaryWindowSum X H f (y - H) ^ 2) +
          ordinaryWindowSum X H f y ^ 2) +
          ordinaryWindowSum X H f (y + H) ^ 2) =
      (∫ y : ℝ, (ordinaryWindowSum X H f (y - 2 * H) ^ 2 +
        ordinaryWindowSum X H f (y - H) ^ 2) +
          ordinaryWindowSum X H f y ^ 2) +
        ∫ y : ℝ, ordinaryWindowSum X H f (y + H) ^ 2 := by
    simpa only [Pi.add_apply] using integral_add ((hA.add hB).add hC) hD
  calc
    (∫ y : ℝ, scaledCenteredWindowSum X H lambda f (lambda * y) ^ 2) ≤
        ∫ y : ℝ, 4 * (ordinaryWindowSum X H f (y - 2 * H) ^ 2 +
          ordinaryWindowSum X H f (y - H) ^ 2 +
          ordinaryWindowSum X H f y ^ 2 +
          ordinaryWindowSum X H f (y + H) ^ 2) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun y ↦ sq_nonneg _
      · exact hright
      · exact Filter.Eventually.of_forall fun y ↦
          scaledCenteredWindowSum_mul_sq_le_four_windows hH hlower
    _ = 16 * ordinarySlidingMass X H f := by
      rw [integral_const_mul]
      change 4 * (∫ a : ℝ,
        ((((fun y : ℝ ↦ ordinaryWindowSum X H f (y - 2 * H) ^ 2) +
          (fun y : ℝ ↦ ordinaryWindowSum X H f (y - H) ^ 2)) +
          (fun y : ℝ ↦ ordinaryWindowSum X H f y ^ 2)) +
          (fun y : ℝ ↦ ordinaryWindowSum X H f (y + H) ^ 2)) a) = _
      simp only [Pi.add_apply]
      rw [hABCD, hABC, hAB]
      have hshiftA :
          (∫ y : ℝ, ordinaryWindowSum X H f (y + (-(2 * H))) ^ 2) =
            ∫ y : ℝ, ordinaryWindowSum X H f y ^ 2 :=
        integral_add_right_eq_self
          (fun y : ℝ ↦ ordinaryWindowSum X H f y ^ 2) (-(2 * H))
      have hshiftB :
          (∫ y : ℝ, ordinaryWindowSum X H f (y + (-H)) ^ 2) =
            ∫ y : ℝ, ordinaryWindowSum X H f y ^ 2 :=
        integral_add_right_eq_self
          (fun y : ℝ ↦ ordinaryWindowSum X H f y ^ 2) (-H)
      have hshiftD :
          (∫ y : ℝ, ordinaryWindowSum X H f (y + H) ^ 2) =
            ∫ y : ℝ, ordinaryWindowSum X H f y ^ 2 :=
        integral_add_right_eq_self
          (fun y : ℝ ↦ ordinaryWindowSum X H f y ^ 2) H
      simp only [sub_eq_add_neg]
      rw [hshiftA, hshiftB, hshiftD]
      rw [ordinarySlidingMass_eq_integral_ordinaryWindowSum]
      ring

/-- Exact scale-dependent form before imposing an upper bound on `lambda`. -/
theorem integral_sq_scaledCenteredWindowSum_le_lambda_mul
    {X H lambda : ℝ} {f : ℕ → ℂ}
    (hH : 0 ≤ H) (hlower : 1 / 2 ≤ lambda) :
    (∫ x : ℝ, scaledCenteredWindowSum X H lambda f x ^ 2) ≤
      16 * lambda * ordinarySlidingMass X H f := by
  have hlpos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlower
  have hscale := Measure.integral_comp_mul_left
    (fun x : ℝ ↦ scaledCenteredWindowSum X H lambda f x ^ 2) lambda
  have hmul :
      lambda * (∫ y : ℝ,
        scaledCenteredWindowSum X H lambda f (lambda * y) ^ 2) =
        ∫ x : ℝ, scaledCenteredWindowSum X H lambda f x ^ 2 := by
    rw [hscale]
    simp only [abs_inv, abs_of_pos hlpos, smul_eq_mul]
    change lambda * (lambda⁻¹ *
      (∫ y : ℝ, scaledCenteredWindowSum X H lambda f y ^ 2)) = _
    rw [← mul_assoc, mul_inv_cancel₀ hlpos.ne', one_mul]
  rw [← hmul]
  have henergy := integral_sq_scaledCenteredWindowSum_mul_le
    (X := X) (f := f) hH hlower
  calc
    lambda * (∫ y : ℝ,
        scaledCenteredWindowSum X H lambda f (lambda * y) ^ 2) ≤
        lambda * (16 * ordinarySlidingMass X H f) :=
      mul_le_mul_of_nonneg_left henergy hlpos.le
    _ = 16 * lambda * ordinarySlidingMass X H f := by ring

/-- A one-sided window of length `4H` is covered by four translates of the
literal `H`-window. -/
theorem ordinaryWindowSum_four_mul_le_four_windows
    {X H x : ℝ} {f : ℕ → ℂ} (hH : 0 ≤ H) :
    ordinaryWindowSum X (4 * H) f x ≤
      ordinaryWindowSum X H f x + ordinaryWindowSum X H f (x + H) +
      ordinaryWindowSum X H f (x + 2 * H) +
      ordinaryWindowSum X H f (x + 3 * H) := by
  unfold ordinaryWindowSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hw : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + 4 * H
  · rw [if_pos hw]
    by_cases h₁ : (n : ℝ) ≤ x + H
    · have hm : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + H := ⟨hw.1, h₁⟩
      rw [if_pos hm]
      split_ifs <;> nlinarith [norm_nonneg (f n)]
    · by_cases h₂ : (n : ℝ) ≤ x + 2 * H
      · have hm : x + H ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + H + H := by
          constructor <;> linarith
        rw [if_pos hm]
        split_ifs <;> nlinarith [norm_nonneg (f n)]
      · by_cases h₃ : (n : ℝ) ≤ x + 3 * H
        · have hm : x + 2 * H ≤ (n : ℝ) ∧
              (n : ℝ) ≤ x + 2 * H + H := by
            constructor <;> linarith
          rw [if_pos hm]
          split_ifs <;> nlinarith [norm_nonneg (f n)]
        · have hm : x + 3 * H ≤ (n : ℝ) ∧
              (n : ℝ) ≤ x + 3 * H + H := by
            constructor <;> linarith [hw.2]
          rw [if_pos hm]
          split_ifs <;> nlinarith [norm_nonneg (f n)]
  · rw [if_neg hw]
    positivity

theorem ordinaryWindowSum_four_mul_sq_le
    {X H x : ℝ} {f : ℕ → ℂ} (hH : 0 ≤ H) :
    ordinaryWindowSum X (4 * H) f x ^ 2 ≤
      4 * (ordinaryWindowSum X H f x ^ 2 +
        ordinaryWindowSum X H f (x + H) ^ 2 +
        ordinaryWindowSum X H f (x + 2 * H) ^ 2 +
        ordinaryWindowSum X H f (x + 3 * H) ^ 2) := by
  have hcover := ordinaryWindowSum_four_mul_le_four_windows
    (X := X) (x := x) (f := f) hH
  have h0 := ordinaryWindowSum_nonneg X (4 * H) f x
  have ha := ordinaryWindowSum_nonneg X H f x
  have hb := ordinaryWindowSum_nonneg X H f (x + H)
  have hc := ordinaryWindowSum_nonneg X H f (x + 2 * H)
  have hd := ordinaryWindowSum_nonneg X H f (x + 3 * H)
  nlinarith [
    sq_nonneg (ordinaryWindowSum X H f x - ordinaryWindowSum X H f (x + H)),
    sq_nonneg (ordinaryWindowSum X H f x - ordinaryWindowSum X H f (x + 2 * H)),
    sq_nonneg (ordinaryWindowSum X H f x - ordinaryWindowSum X H f (x + 3 * H)),
    sq_nonneg (ordinaryWindowSum X H f (x + H) - ordinaryWindowSum X H f (x + 2 * H)),
    sq_nonneg (ordinaryWindowSum X H f (x + H) - ordinaryWindowSum X H f (x + 3 * H)),
    sq_nonneg (ordinaryWindowSum X H f (x + 2 * H) - ordinaryWindowSum X H f (x + 3 * H))]

/-- Fourfold dilation costs at most `16` in the literal sliding mass. -/
theorem ordinarySlidingMass_four_mul_le
    {X H : ℝ} {f : ℕ → ℂ} (hH : 0 ≤ H) :
    ordinarySlidingMass X (4 * H) f ≤
      16 * ordinarySlidingMass X H f := by
  rw [ordinarySlidingMass_eq_integral_ordinaryWindowSum,
    ordinarySlidingMass_eq_integral_ordinaryWindowSum]
  have hbase := integrable_sq_ordinaryWindowSum X H f
  have hA : Integrable (fun x : ℝ ↦ ordinaryWindowSum X H f x ^ 2) := hbase
  have hB : Integrable (fun x : ℝ ↦ ordinaryWindowSum X H f (x + H) ^ 2) :=
    hbase.comp_add_right H
  have hC : Integrable (fun x : ℝ ↦ ordinaryWindowSum X H f (x + 2 * H) ^ 2) :=
    hbase.comp_add_right (2 * H)
  have hD : Integrable (fun x : ℝ ↦ ordinaryWindowSum X H f (x + 3 * H) ^ 2) :=
    hbase.comp_add_right (3 * H)
  have hright : Integrable (fun x : ℝ ↦ 4 *
      (ordinaryWindowSum X H f x ^ 2 +
        ordinaryWindowSum X H f (x + H) ^ 2 +
        ordinaryWindowSum X H f (x + 2 * H) ^ 2 +
        ordinaryWindowSum X H f (x + 3 * H) ^ 2)) :=
    (((hA.add hB).add hC).add hD).const_mul 4
  calc
    (∫ x : ℝ, ordinaryWindowSum X (4 * H) f x ^ 2) ≤
        ∫ x : ℝ, 4 * (ordinaryWindowSum X H f x ^ 2 +
          ordinaryWindowSum X H f (x + H) ^ 2 +
          ordinaryWindowSum X H f (x + 2 * H) ^ 2 +
          ordinaryWindowSum X H f (x + 3 * H) ^ 2) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x ↦ sq_nonneg _
      · exact hright
      · exact Filter.Eventually.of_forall fun x ↦
          ordinaryWindowSum_four_mul_sq_le hH
    _ = 16 * ∫ x : ℝ, ordinaryWindowSum X H f x ^ 2 := by
      rw [integral_const_mul]
      have hAB : (∫ x : ℝ, ordinaryWindowSum X H f x ^ 2 +
          ordinaryWindowSum X H f (x + H) ^ 2) =
          (∫ x : ℝ, ordinaryWindowSum X H f x ^ 2) +
          ∫ x : ℝ, ordinaryWindowSum X H f (x + H) ^ 2 := by
        simpa only [Pi.add_apply] using integral_add hA hB
      have hABC : (∫ x : ℝ, (ordinaryWindowSum X H f x ^ 2 +
          ordinaryWindowSum X H f (x + H) ^ 2) +
          ordinaryWindowSum X H f (x + 2 * H) ^ 2) =
          (∫ x : ℝ, ordinaryWindowSum X H f x ^ 2 +
            ordinaryWindowSum X H f (x + H) ^ 2) +
          ∫ x : ℝ, ordinaryWindowSum X H f (x + 2 * H) ^ 2 := by
        simpa only [Pi.add_apply] using integral_add (hA.add hB) hC
      have hABCD : (∫ x : ℝ, ((ordinaryWindowSum X H f x ^ 2 +
          ordinaryWindowSum X H f (x + H) ^ 2) +
          ordinaryWindowSum X H f (x + 2 * H) ^ 2) +
          ordinaryWindowSum X H f (x + 3 * H) ^ 2) =
          (∫ x : ℝ, (ordinaryWindowSum X H f x ^ 2 +
            ordinaryWindowSum X H f (x + H) ^ 2) +
            ordinaryWindowSum X H f (x + 2 * H) ^ 2) +
          ∫ x : ℝ, ordinaryWindowSum X H f (x + 3 * H) ^ 2 := by
        simpa only [Pi.add_apply] using integral_add ((hA.add hB).add hC) hD
      rw [hABCD, hABC, hAB,
        integral_add_right_eq_self (fun x : ℝ ↦ ordinaryWindowSum X H f x ^ 2) H,
        integral_add_right_eq_self (fun x : ℝ ↦ ordinaryWindowSum X H f x ^ 2) (2 * H),
        integral_add_right_eq_self (fun x : ℝ ↦ ordinaryWindowSum X H f x ^ 2) (3 * H)]
      ring

/-- Quarter-range version needed by the MAP projection weld.  The constants
`1/8` and `17/4` are literal; `1088` is an explicit harmless absolute cost. -/
theorem integral_sq_scaledCenteredWindowSum_quarter_range
    {X H lambda : ℝ} {f : ℕ → ℂ}
    (hH : 0 ≤ H) (hlower : 1 / 8 ≤ lambda) (hupper : lambda ≤ 17 / 4) :
    (∫ x : ℝ, scaledCenteredWindowSum X H lambda f x ^ 2) ≤
      1088 * ordinarySlidingMass X H f := by
  let L : ℝ := 4 * lambda
  have hLlower : 1 / 2 ≤ L := by unfold L; linarith
  have hLupper : L ≤ 17 := by unfold L; linarith
  have hpoint : ∀ x : ℝ,
      scaledCenteredWindowSum X (4 * H) L f (4 * x) =
        scaledCenteredWindowSum X H lambda f x := by
    intro x
    unfold scaledCenteredWindowSum L
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    rw [show 4 * x - 4 * lambda * (n : ℝ) =
      4 * (x - lambda * n) by ring, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<4)]
    apply propext
    constructor <;> intro h <;> linarith
  have hscale := Measure.integral_comp_mul_left
    (fun z : ℝ ↦ scaledCenteredWindowSum X (4 * H) L f z ^ 2) 4
  have heq : (∫ x : ℝ, scaledCenteredWindowSum X H lambda f x ^ 2) =
      (1 / 4) * ∫ z : ℝ, scaledCenteredWindowSum X (4 * H) L f z ^ 2 := by
    calc
      (∫ x : ℝ, scaledCenteredWindowSum X H lambda f x ^ 2) =
          ∫ x : ℝ, scaledCenteredWindowSum X (4 * H) L f (4 * x) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hpoint]
      _ = (1 / 4) * ∫ z : ℝ,
          scaledCenteredWindowSum X (4 * H) L f z ^ 2 := by
        simpa [abs_of_pos (by norm_num : (0 : ℝ) < 4), smul_eq_mul] using hscale
  rw [heq]
  have hlong := integral_sq_scaledCenteredWindowSum_le_lambda_mul
    (X := X) (H := 4 * H) (lambda := L) (f := f) (by positivity) hLlower
  have hmass := ordinarySlidingMass_four_mul_le (X := X) (f := f) hH
  have hm0 : 0 ≤ ordinarySlidingMass X (4 * H) f := by
    unfold ordinarySlidingMass
    positivity
  have hm1 : 0 ≤ ordinarySlidingMass X H f := by
    unfold ordinarySlidingMass
    positivity
  calc
    (1 / 4) * (∫ z : ℝ, scaledCenteredWindowSum X (4 * H) L f z ^ 2) ≤
        (1 / 4) * (16 * L * ordinarySlidingMass X (4 * H) f) := by
      gcongr
    _ ≤ 68 * ordinarySlidingMass X (4 * H) f := by
      have := mul_le_mul_of_nonneg_right hLupper hm0
      nlinarith
    _ ≤ 68 * (16 * ordinarySlidingMass X H f) := by gcongr
    _ = 1088 * ordinarySlidingMass X H f := by ring

/-- Whole-line form after the literal rescaling `x=λy`.  The absolute
constant `32` is uniform on the explicit representative of `λ ≍ 1`.
-/
theorem integral_sq_scaledCenteredWindowSum_le_ordinarySlidingMass
    {X H lambda : ℝ} {f : ℕ → ℂ}
    (hH : 0 ≤ H) (hlower : 1 / 2 ≤ lambda) (hupper : lambda ≤ 2) :
    (∫ x : ℝ, scaledCenteredWindowSum X H lambda f x ^ 2) ≤
      32 * ordinarySlidingMass X H f := by
  have hlpos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlower
  have hscale := Measure.integral_comp_mul_left
    (fun x : ℝ ↦ scaledCenteredWindowSum X H lambda f x ^ 2) lambda
  have hmul :
      lambda * (∫ y : ℝ,
        scaledCenteredWindowSum X H lambda f (lambda * y) ^ 2) =
        ∫ x : ℝ, scaledCenteredWindowSum X H lambda f x ^ 2 := by
    rw [hscale]
    simp only [abs_inv, abs_of_pos hlpos, smul_eq_mul]
    change lambda * (lambda⁻¹ *
      (∫ y : ℝ, scaledCenteredWindowSum X H lambda f y ^ 2)) = _
    rw [← mul_assoc, mul_inv_cancel₀ hlpos.ne', one_mul]
  rw [← hmul]
  have henergy := integral_sq_scaledCenteredWindowSum_mul_le
    (X := X) (f := f) hH hlower
  have hmass : 0 ≤ ordinarySlidingMass X H f := by
    unfold ordinarySlidingMass
    positivity
  calc
    lambda * (∫ y : ℝ,
        scaledCenteredWindowSum X H lambda f (lambda * y) ^ 2) ≤
        lambda * (16 * ordinarySlidingMass X H f) :=
      mul_le_mul_of_nonneg_left henergy hlpos.le
    _ ≤ 32 * ordinarySlidingMass X H f := by nlinarith

end
end MAPMRTProposition51ProjectionHighGeometry

#print axioms MAPMRTProposition51ProjectionHighGeometry.scaledCenteredWindowSum_mul_le_four_windows
#print axioms MAPMRTProposition51ProjectionHighGeometry.integral_sq_scaledCenteredWindowSum_mul_le
#print axioms MAPMRTProposition51ProjectionHighGeometry.integral_sq_scaledCenteredWindowSum_quarter_range
#print axioms MAPMRTProposition51ProjectionHighGeometry.integral_sq_scaledCenteredWindowSum_le_ordinarySlidingMass
