import MRTFaithfulLowProjectionIdentity
import MRTProposition51ProjectionHighGeometry

/-!
# MRT Proposition 5.1: deterministic page-47 logarithmic geometry

This file isolates the exact coordinate transport used after the localized
one-integration-by-parts estimate.  No summation or analytic estimate is used:
the statements only turn the physical packet condition into a centered
coefficient window after `z = w - log n + log X`.
-/

namespace MAPMRTFaithfulLowPage47Geometry

open Set
open MAPMRTCorollary53Source
open MAPMRTProposition51HardBranch
open MAPMRTProposition51FirstAnalytic
open MAPMRTProposition51ProjectionHighGeometry
open MAPMRTProposition51ProjectionLowAmplitude
open MAPMRTFaithfulSmoothCutoff
open MAPMRTFaithfulSmoothCutoffBudgets

noncomputable section

/-- The page-47 displacement variable. -/
def page47LogDisplacement (X : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  w - Real.log n + Real.log X

/-- Exact multiplicative content of `z = w - log n + log X`. -/
theorem natCast_mul_exp_page47LogDisplacement
    {X : ℝ} {n : ℕ} {w : ℝ} (hX : 0 < X) (hn : 0 < n) :
    (n : ℝ) * Real.exp (page47LogDisplacement X n w) =
      X * Real.exp w := by
  unfold page47LogDisplacement
  rw [show w - Real.log (n : ℝ) + Real.log X =
      (w + Real.log X) - Real.log (n : ℝ) by ring,
    Real.exp_sub, Real.exp_add, Real.exp_log hX,
    Real.exp_log (by exact_mod_cast hn : (0 : ℝ) < n)]
  field_simp

/-- Equivalent inverse form, useful when the coefficient variable is the
centered variable. -/
theorem exp_neg_page47LogDisplacement_mul_physical
    {X : ℝ} {n : ℕ} {w : ℝ} (hX : 0 < X) (hn : 0 < n) :
    Real.exp (-page47LogDisplacement X n w) * (X * Real.exp w) = n := by
  have h := natCast_mul_exp_page47LogDisplacement
    (X := X) (n := n) (w := w) hX hn
  have hz : 0 < Real.exp (page47LogDisplacement X n w) := Real.exp_pos _
  rw [Real.exp_neg]
  calc
    (Real.exp (page47LogDisplacement X n w))⁻¹ * (X * Real.exp w) =
        (Real.exp (page47LogDisplacement X n w))⁻¹ *
          ((n : ℝ) * Real.exp (page47LogDisplacement X n w)) := by rw [h]
    _ = n := by field_simp

/-- Exact error transport: physical distance is multiplied by `exp (-z)`.
This is the equality behind `n = e^{-z}x + O(H)`. -/
theorem abs_natCast_sub_exp_neg_mul_eq
    {X x : ℝ} {n : ℕ} {w : ℝ} (hX : 0 < X) (hn : 0 < n) :
    |(n : ℝ) - Real.exp (-page47LogDisplacement X n w) * x| =
      Real.exp (-page47LogDisplacement X n w) *
        |X * Real.exp w - x| := by
  have hid := exp_neg_page47LogDisplacement_mul_physical
    (X := X) (n := n) (w := w) hX hn
  calc
    |(n : ℝ) - Real.exp (-page47LogDisplacement X n w) * x| =
        |Real.exp (-page47LogDisplacement X n w) *
          (X * Real.exp w - x)| := by rw [mul_sub, hid]
    _ = _ := by rw [abs_mul, abs_of_pos (Real.exp_pos _)]

/-- On the exact source ranges, the physical point `X exp w` stays in the
fixed interval `[X/4,17X/4]`. -/
theorem physical_point_mem_quarter_range
    {X H x w : ℝ} (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hphysical : |X * Real.exp w - x| ≤ H) :
    X / 4 ≤ X * Real.exp w ∧ X * Real.exp w ≤ 17 * X / 4 := by
  rw [abs_le] at hphysical
  constructor <;> linarith

/-- The logarithmic dilation `exp z` is uniformly bounded on the literal
coefficient and physical support. -/
theorem exp_page47LogDisplacement_mem
    {X H x w : ℝ} {n : ℕ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 4)
    (hnLower : X ≤ n) (hnUpper : (n : ℝ) ≤ 2 * X)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hphysical : |X * Real.exp w - x| ≤ H) :
    1 / 8 ≤ Real.exp (page47LogDisplacement X n w) ∧
      Real.exp (page47LogDisplacement X n w) ≤ 17 / 4 := by
  have hnposR : (0 : ℝ) < n := lt_of_lt_of_le hX hnLower
  have hnpos : 0 < n := by exact_mod_cast hnposR
  have heq := natCast_mul_exp_page47LogDisplacement
    (X := X) (n := n) (w := w) hX hnpos
  have hp := physical_point_mem_quarter_range hHquarter
    hxLower hxUpper hphysical
  have hexp := Real.exp_pos (page47LogDisplacement X n w)
  constructor
  · nlinarith
  · nlinarith

/-- Consequently the inverse dilation is bounded by `8`; this turns the
transported physical error into an absolute `8H` coefficient error. -/
theorem exp_neg_page47LogDisplacement_le_eight
    {X H x w : ℝ} {n : ℕ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 4)
    (hnLower : X ≤ n) (hnUpper : (n : ℝ) ≤ 2 * X)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hphysical : |X * Real.exp w - x| ≤ H) :
    Real.exp (-page47LogDisplacement X n w) ≤ 8 := by
  have hz := (exp_page47LogDisplacement_mem hX hH hHquarter hnLower hnUpper
    hxLower hxUpper hphysical).1
  rw [Real.exp_neg]
  have hpos := Real.exp_pos (page47LogDisplacement X n w)
  exact (inv_le_comm₀ hpos (by norm_num)).2 (by norm_num at hz ⊢; exact hz)

/-- Literal page-47 implication `n = e^{-z}x + O(H)`, with an explicit
constant valid on the manuscript's full quarter-range support. -/
theorem page47_coefficient_distance_le_eight_mul
    {X H x w : ℝ} {n : ℕ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 4)
    (hnLower : X ≤ n) (hnUpper : (n : ℝ) ≤ 2 * X)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hphysical : |X * Real.exp w - x| ≤ H) :
    |(n : ℝ) - Real.exp (-page47LogDisplacement X n w) * x| ≤ 8 * H := by
  rw [abs_natCast_sub_exp_neg_mul_eq hX
    (by
      have : (0 : ℝ) < n := lt_of_lt_of_le hX hnLower
      exact_mod_cast this)]
  exact mul_le_mul
    (exp_neg_page47LogDisplacement_le_eight hX hH hHquarter hnLower hnUpper
      hxLower hxUpper hphysical)
    hphysical (abs_nonneg _) (by norm_num)

/-- Exact closed interval form ready for insertion into a nonnegative
coefficient-window sum. -/
theorem page47_coefficient_mem_centered_window
    {X H x w : ℝ} {n : ℕ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 4)
    (hnLower : X ≤ n) (hnUpper : (n : ℝ) ≤ 2 * X)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hphysical : |X * Real.exp w - x| ≤ H) :
    Real.exp (-page47LogDisplacement X n w) * x - 8 * H ≤ n ∧
      (n : ℝ) ≤ Real.exp (-page47LogDisplacement X n w) * x + 8 * H := by
  have hdist := page47_coefficient_distance_le_eight_mul hX hH hHquarter
    hnLower hnUpper hxLower hxUpper hphysical
  rw [abs_le] at hdist
  constructor <;> linarith

/-- The actual support radius `1/8` of the faithful cutoff improves the
coarse page-47 transport to the original coefficient scale `H`. -/
theorem faithful_exp_page47LogDisplacement_mem
    {X H x w : ℝ} {n : ℕ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 4)
    (hnLower : X ≤ n) (hnUpper : (n : ℝ) ≤ 2 * X)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hphysical : |X * Real.exp w - x| ≤ H / 8) :
    15 / 64 ≤ Real.exp (page47LogDisplacement X n w) ∧
      Real.exp (page47LogDisplacement X n w) ≤ 129 / 32 := by
  have hnposR : (0 : ℝ) < n := lt_of_lt_of_le hX hnLower
  have hnpos : 0 < n := by exact_mod_cast hnposR
  have heq := natCast_mul_exp_page47LogDisplacement
    (X := X) (n := n) (w := w) hX hnpos
  have hp : 15 * X / 32 ≤ X * Real.exp w ∧
      X * Real.exp w ≤ 129 * X / 32 := by
    rw [abs_le] at hphysical
    constructor <;> nlinarith
  have hexp := Real.exp_pos (page47LogDisplacement X n w)
  constructor <;> nlinarith

theorem faithful_exp_neg_page47LogDisplacement_le
    {X H x w : ℝ} {n : ℕ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 4)
    (hnLower : X ≤ n) (hnUpper : (n : ℝ) ≤ 2 * X)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hphysical : |X * Real.exp w - x| ≤ H / 8) :
    Real.exp (-page47LogDisplacement X n w) ≤ 64 / 15 := by
  have hz := (faithful_exp_page47LogDisplacement_mem hX hH hHquarter
    hnLower hnUpper hxLower hxUpper hphysical).1
  rw [Real.exp_neg]
  have hpos := Real.exp_pos (page47LogDisplacement X n w)
  exact (inv_le_comm₀ hpos (by norm_num)).2 (by norm_num at hz ⊢; exact hz)

/-- Sharp form of `n=e^{-z}x+O(H)` retaining the faithful cutoff's true
support.  Unlike the coarse geometry, no dilation of the source window is
needed. -/
theorem faithful_page47_coefficient_distance_le
    {X H x w : ℝ} {n : ℕ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 4)
    (hnLower : X ≤ n) (hnUpper : (n : ℝ) ≤ 2 * X)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hphysical : |X * Real.exp w - x| ≤ H / 8) :
    |(n : ℝ) - Real.exp (-page47LogDisplacement X n w) * x| ≤ H := by
  rw [abs_natCast_sub_exp_neg_mul_eq hX
    (by
      have : (0 : ℝ) < n := lt_of_lt_of_le hX hnLower
      exact_mod_cast this)]
  have hmul : Real.exp (-page47LogDisplacement X n w) *
      |X * Real.exp w - x| ≤ (64 / 15) * (H / 8) := by
    exact mul_le_mul
      (faithful_exp_neg_page47LogDisplacement_le hX hH hHquarter
        hnLower hnUpper hxLower hxUpper hphysical)
      hphysical (abs_nonneg _) (by norm_num)
  nlinarith

/-- The full derivative amplitude in (78), not merely its cutoff factor,
vanishes strictly outside the faithful physical radius `H/8`. -/
theorem faithfulLowProjectionAmplitudeDeriv_eq_zero_of_outside
    {X H beta eta x u w : ℝ} (hH : 0 < H)
    (hout : H / 8 < |X * Real.exp w - x|) :
    lowProjectionAmplitudeDeriv X H beta eta x u
      faithfulCutoff faithfulCutoffDeriv
      (cutoffFourierKernel faithfulCutoff)
      faithfulCutoffFourierDeriv w = 0 := by
  have harg : 1 / 8 < |(X * Real.exp w - x) / H| := by
    rw [abs_div, abs_of_pos hH]
    calc
      1 / 8 = (H / 8) / H := by field_simp [hH.ne']
      _ < |X * Real.exp w - x| / H :=
        (div_lt_div_iff_of_pos_right hH).2 hout
  have hc : faithfulCutoff ((X * Real.exp w - x) / H) = 0 :=
    faithfulCutoff_zero harg.le
  have hcd : faithfulCutoffDeriv ((X * Real.exp w - x) / H) = 0 := by
    by_contra hn
    exact (not_le_of_gt harg)
      (MAPMRTFaithfulSmoothCutoffBudgets.abs_le_eighth_of_faithfulCutoffDeriv_ne_zero hn)
  unfold lowProjectionAmplitudeDeriv
  simp [hc, hcd]

/-- Support implication in the direction consumed by the localized integral:
every nonzero derivative-amplitude point satisfies the sharp physical bound. -/
theorem faithful_physical_bound_of_lowProjectionAmplitudeDeriv_ne_zero
    {X H beta eta x u w : ℝ} (hH : 0 < H)
    (hne : lowProjectionAmplitudeDeriv X H beta eta x u
      faithfulCutoff faithfulCutoffDeriv
      (cutoffFourierKernel faithfulCutoff)
      faithfulCutoffFourierDeriv w ≠ 0) :
    |X * Real.exp w - x| ≤ H / 8 := by
  by_contra hout
  exact hne (faithfulLowProjectionAmplitudeDeriv_eq_zero_of_outside hH
    (lt_of_not_ge hout))

theorem page47LogDisplacement_inverse_substitution
    (X z : ℝ) (n : ℕ) :
    page47LogDisplacement X n (z + Real.log n - Real.log X) = z := by
  unfold page47LogDisplacement
  ring

/-- Literal transformed coefficient sum with the faithful radius retained. -/
def faithfulPage47ChangedPhysicalWindowSum
    (X H z : ℝ) (f : ℕ → ℂ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    if |X * Real.exp (z + Real.log n - Real.log X) - x| ≤ H / 8
    then ‖f n‖ else 0

/-- Two source-scale one-sided windows cover the sharp centered window. -/
def faithfulPage47OrdinaryMajorant
    (X H z : ℝ) (f : ℕ → ℂ) (x : ℝ) : ℝ :=
  ordinaryWindowSum X H f (Real.exp (-z) * x - H) +
    ordinaryWindowSum X H f (Real.exp (-z) * x)

theorem faithfulPage47ChangedPhysicalWindowSum_le_majorant
    {X H z x : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X) :
    faithfulPage47ChangedPhysicalWindowSum X H z f x ≤
      faithfulPage47OrdinaryMajorant X H z f x := by
  unfold faithfulPage47ChangedPhysicalWindowSum faithfulPage47OrdinaryMajorant
  unfold ordinaryWindowSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hp :
      |X * Real.exp (z + Real.log n - Real.log X) - x| ≤ H / 8
  · rw [if_pos hp]
    have hnbox := Finset.mem_Ioc.mp hn
    have hnLowerStrict : X < (n : ℝ) :=
      (Nat.floor_lt hX.le).mp hnbox.1
    have hnFloor : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by
      exact_mod_cast hnbox.2
    have hnUpper : (n : ℝ) ≤ 2 * X :=
      hnFloor.trans (Nat.floor_le (by positivity : 0 ≤ 2 * X))
    have hdist := faithful_page47_coefficient_distance_le
      (X := X) (H := H) (x := x)
      (w := z + Real.log n - Real.log X) (n := n)
      hX hH hHquarter hnLowerStrict.le hnUpper hxLower hxUpper hp
    rw [show page47LogDisplacement X n
        (z + Real.log n - Real.log X) = z by
      unfold page47LogDisplacement
      ring] at hdist
    rw [abs_le] at hdist
    by_cases hleft : (n : ℝ) ≤ Real.exp (-z) * x
    · have hw : Real.exp (-z) * x - H ≤ (n : ℝ) ∧
          (n : ℝ) ≤ (Real.exp (-z) * x - H) + H := by
        constructor <;> linarith
      rw [if_pos hw]
      split_ifs <;> nlinarith [norm_nonneg (f n)]
    · have hw : Real.exp (-z) * x ≤ (n : ℝ) ∧
          (n : ℝ) ≤ Real.exp (-z) * x + H := by
        constructor <;> linarith
      rw [if_pos hw]
      split_ifs <;> nlinarith [norm_nonneg (f n)]
  · rw [if_neg hp]
    positivity

/-- The physical window after substituting
`w = z + log n - log X`.  This is the literal finite sum left by the
page-47 change of variables before taking absolute values. -/
def page47ChangedPhysicalWindowSum
    (X H z : ℝ) (f : ℕ → ℂ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    if |X * Real.exp (z + Real.log n - Real.log X) - x| ≤ H
    then ‖f n‖ else 0

/-- The single ordinary-window majorant produced by the deterministic
transport. -/
def page47OrdinaryMajorant
    (X H z : ℝ) (f : ℕ → ℂ) (x : ℝ) : ℝ :=
  ordinaryWindowSum X (16 * H) f (Real.exp (-z) * x - 8 * H)

/-- Every summand surviving after the logarithmic change lies in one explicit
one-sided interval of length `16H`.  Thus the remaining finite coefficient
sum is pointwise dominated by the exact `ordinaryWindowSum` used to define
`ordinarySlidingMass`. -/
theorem page47ChangedPhysicalWindowSum_le_ordinaryWindowSum
    {X H z x : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X) :
    page47ChangedPhysicalWindowSum X H z f x ≤
      page47OrdinaryMajorant X H z f x := by
  unfold page47OrdinaryMajorant
  unfold page47ChangedPhysicalWindowSum ordinaryWindowSum
  apply Finset.sum_le_sum
  intro n hn
  by_cases hp :
      |X * Real.exp (z + Real.log n - Real.log X) - x| ≤ H
  · rw [if_pos hp]
    have hnbox := Finset.mem_Ioc.mp hn
    have hnLowerStrict : X < (n : ℝ) :=
      (Nat.floor_lt hX.le).mp hnbox.1
    have hnLower : X ≤ (n : ℝ) := hnLowerStrict.le
    have hnFloor : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by
      exact_mod_cast hnbox.2
    have hnUpper : (n : ℝ) ≤ 2 * X :=
      hnFloor.trans (Nat.floor_le (by positivity : 0 ≤ 2 * X))
    have hcenter := page47_coefficient_mem_centered_window
      (X := X) (H := H) (x := x)
      (w := z + Real.log n - Real.log X) (n := n)
      hX hH hHquarter hnLower hnUpper hxLower hxUpper hp
    rw [page47LogDisplacement_inverse_substitution] at hcenter
    have hwindow :
        Real.exp (-z) * x - 8 * H ≤ (n : ℝ) ∧
          (n : ℝ) ≤ (Real.exp (-z) * x - 8 * H) + 16 * H := by
      constructor <;> linarith [hcenter.1, hcenter.2]
    rw [if_pos hwindow]
  · rw [if_neg hp]
    positivity

/-- Exact Jacobian for the transported one-sided window. -/
theorem integral_sq_page47OrdinaryMajorant
    (X H z : ℝ) (f : ℕ → ℂ) :
    (∫ x : ℝ, page47OrdinaryMajorant X H z f x ^ 2) =
      Real.exp z * ordinarySlidingMass X (16 * H) f := by
  let F : ℝ → ℝ := fun y ↦ ordinaryWindowSum X (16 * H) f
    (y - 8 * H) ^ 2
  have hscale := MeasureTheory.Measure.integral_comp_mul_left F (Real.exp (-z))
  have hinvabs : |(Real.exp (-z))⁻¹| = Real.exp z := by
    rw [abs_of_pos (inv_pos.mpr (Real.exp_pos _)), Real.exp_neg]
    simp
  have hshift : (∫ y : ℝ, F y) = ordinarySlidingMass X (16 * H) f := by
    unfold F
    have htranslate := MeasureTheory.integral_add_right_eq_self
      (μ := MeasureTheory.volume)
      (fun y : ℝ ↦ ordinaryWindowSum X (16 * H) f y ^ 2) (-8 * H)
    rw [show (fun y : ℝ ↦
        ordinaryWindowSum X (16 * H) f (y - 8 * H) ^ 2) =
      (fun y : ℝ ↦ ordinaryWindowSum X (16 * H) f (y + (-8 * H)) ^ 2) by
      funext y
      congr 2 <;> ring]
    rw [htranslate]
    rw [← ordinarySlidingMass_eq_integral_ordinaryWindowSum]
  unfold page47OrdinaryMajorant
  change (∫ x : ℝ, F (Real.exp (-z) * x)) = _
  rw [hscale, hinvabs, hshift]
  rfl


theorem faithful_exp_page47LogDisplacement_mem_half_range
    {X H x w : ℝ} {n : ℕ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 2)
    (hnLower : X ≤ n) (hnUpper : (n : ℝ) ≤ 2 * X)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hphysical : |X * Real.exp w - x| ≤ H / 8) :
    7 / 32 ≤ Real.exp (page47LogDisplacement X n w) ∧
      Real.exp (page47LogDisplacement X n w) ≤ 65 / 16 := by
  have hnposR : (0 : ℝ) < n := lt_of_lt_of_le hX hnLower
  have hnpos : 0 < n := by exact_mod_cast hnposR
  have heq := natCast_mul_exp_page47LogDisplacement
    (X := X) (n := n) (w := w) hX hnpos
  have hp : 7 * X / 16 ≤ X * Real.exp w ∧
      X * Real.exp w ≤ 65 * X / 16 := by
    rw [abs_le] at hphysical
    constructor <;> nlinarith
  have hexp := Real.exp_pos (page47LogDisplacement X n w)
  constructor <;> nlinarith

theorem faithful_exp_neg_page47LogDisplacement_le_half_range
    {X H x w : ℝ} {n : ℕ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 2)
    (hnLower : X ≤ n) (hnUpper : (n : ℝ) ≤ 2 * X)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hphysical : |X * Real.exp w - x| ≤ H / 8) :
    Real.exp (-page47LogDisplacement X n w) ≤ 32 / 7 := by
  have hz := (faithful_exp_page47LogDisplacement_mem_half_range hX hH hHquarter
    hnLower hnUpper hxLower hxUpper hphysical).1
  rw [Real.exp_neg]
  have hpos := Real.exp_pos (page47LogDisplacement X n w)
  exact (inv_le_comm₀ hpos (by norm_num)).2 (by norm_num at hz ⊢; exact hz)

theorem faithful_page47_coefficient_distance_le_half_range
    {X H x w : ℝ} {n : ℕ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 2)
    (hnLower : X ≤ n) (hnUpper : (n : ℝ) ≤ 2 * X)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hphysical : |X * Real.exp w - x| ≤ H / 8) :
    |(n : ℝ) - Real.exp (-page47LogDisplacement X n w) * x| ≤ H := by
  rw [abs_natCast_sub_exp_neg_mul_eq hX
    (by
      have : (0 : ℝ) < n := lt_of_lt_of_le hX hnLower
      exact_mod_cast this)]
  have hmul : Real.exp (-page47LogDisplacement X n w) *
      |X * Real.exp w - x| ≤ (32 / 7) * (H / 8) := by
    exact mul_le_mul
      (faithful_exp_neg_page47LogDisplacement_le_half_range hX hH hHquarter
        hnLower hnUpper hxLower hxUpper hphysical)
      hphysical (abs_nonneg _) (by norm_num)
  nlinarith

theorem faithfulPage47ChangedPhysicalWindowSum_le_majorant_half_range
    {X H z x : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X) :
    faithfulPage47ChangedPhysicalWindowSum X H z f x ≤
      faithfulPage47OrdinaryMajorant X H z f x := by
  unfold faithfulPage47ChangedPhysicalWindowSum faithfulPage47OrdinaryMajorant
  unfold ordinaryWindowSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hp :
      |X * Real.exp (z + Real.log n - Real.log X) - x| ≤ H / 8
  · rw [if_pos hp]
    have hnbox := Finset.mem_Ioc.mp hn
    have hnLowerStrict : X < (n : ℝ) :=
      (Nat.floor_lt hX.le).mp hnbox.1
    have hnFloor : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by
      exact_mod_cast hnbox.2
    have hnUpper : (n : ℝ) ≤ 2 * X :=
      hnFloor.trans (Nat.floor_le (by positivity : 0 ≤ 2 * X))
    have hdist := faithful_page47_coefficient_distance_le_half_range
      (X := X) (H := H) (x := x)
      (w := z + Real.log n - Real.log X) (n := n)
      hX hH hHquarter hnLowerStrict.le hnUpper hxLower hxUpper hp
    rw [show page47LogDisplacement X n
        (z + Real.log n - Real.log X) = z by
      unfold page47LogDisplacement
      ring] at hdist
    rw [abs_le] at hdist
    by_cases hleft : (n : ℝ) ≤ Real.exp (-z) * x
    · have hw : Real.exp (-z) * x - H ≤ (n : ℝ) ∧
          (n : ℝ) ≤ (Real.exp (-z) * x - H) + H := by
        constructor <;> linarith
      rw [if_pos hw]
      split_ifs <;> nlinarith [norm_nonneg (f n)]
    · have hw : Real.exp (-z) * x ≤ (n : ℝ) ∧
          (n : ℝ) ≤ Real.exp (-z) * x + H := by
        constructor <;> linarith
      rw [if_pos hw]
      split_ifs <;> nlinarith [norm_nonneg (f n)]
  · rw [if_neg hp]
    positivity

end
end MAPMRTFaithfulLowPage47Geometry

#print axioms MAPMRTFaithfulLowPage47Geometry.natCast_mul_exp_page47LogDisplacement
#print axioms MAPMRTFaithfulLowPage47Geometry.abs_natCast_sub_exp_neg_mul_eq
#print axioms MAPMRTFaithfulLowPage47Geometry.page47_coefficient_distance_le_eight_mul
#print axioms MAPMRTFaithfulLowPage47Geometry.page47_coefficient_mem_centered_window
#print axioms MAPMRTFaithfulLowPage47Geometry.faithful_exp_page47LogDisplacement_mem
#print axioms MAPMRTFaithfulLowPage47Geometry.faithful_page47_coefficient_distance_le
#print axioms MAPMRTFaithfulLowPage47Geometry.faithfulLowProjectionAmplitudeDeriv_eq_zero_of_outside
#print axioms MAPMRTFaithfulLowPage47Geometry.faithful_physical_bound_of_lowProjectionAmplitudeDeriv_ne_zero
#print axioms MAPMRTFaithfulLowPage47Geometry.faithfulPage47ChangedPhysicalWindowSum_le_majorant
#print axioms MAPMRTFaithfulLowPage47Geometry.page47ChangedPhysicalWindowSum_le_ordinaryWindowSum
#print axioms MAPMRTFaithfulLowPage47Geometry.integral_sq_page47OrdinaryMajorant
