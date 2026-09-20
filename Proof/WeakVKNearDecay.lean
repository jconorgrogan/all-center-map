import CGLMeshFormalization

/-!
# A weak Vinogradov--Korobov gap is enough for the MAP near-one window

This file contains no zero-free theorem.  It certifies the deterministic
calculus bridge needed by the MAP near-one branch: any zero-free gap of size
`c / (log X)^theta` with a fixed `theta < 1` beats every fixed power of
`log X` after it is inserted into the factor `X^(-omega / 12)`.

Keeping this bridge separate makes the only remaining analytic input exact:
one needs a genuine sub-logarithmic zero-free denominator.  A classical
de la Vallee Poussin gap `c / log(qT)` corresponds to `theta = 1` and does
not satisfy the hypotheses below.
-/

namespace WeakVKNear

open Filter Asymptotics

noncomputable section

/-- A stretched exponential in the logarithmic coordinate dominates every
fixed power.  This is the basic calculus fact behind the weak-VK route. -/
theorem stretchedExp_beats_rpow
    (theta c P A : ℝ)
    (htheta : theta < 1) (hc : 0 < c)
    (hP : 0 ≤ P) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop,
      Real.rpow L P * Real.exp (-(c / 12) * Real.rpow L (1 - theta)) ≤
        Real.rpow L (-A) := by
  have hs : 0 < 1 - theta := sub_pos.mpr htheta
  let D : ℝ := 12 * (P + A + 1) / c
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hsmall0 :=
    ((isLittleO_log_rpow_rpow_atTop (1 : ℝ) hs).const_mul_left D).eventuallyLE
  have hsmall : ∀ᶠ L : ℝ in atTop,
      D * Real.log L ≤ Real.rpow L (1 - theta) := by
    filter_upwards [hsmall0, eventually_gt_atTop (1 : ℝ)] with L hbound hL
    have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL.le
    have hDlog0 : 0 ≤ D * Real.log L := mul_nonneg hD.le hlog0
    have hrpow0 : 0 ≤ Real.rpow L (1 - theta) :=
      Real.rpow_nonneg (zero_lt_one.trans hL).le _
    have hbound' :
        |D * Real.rpow (Real.log L) 1| ≤
          |Real.rpow L (1 - theta)| := by
      simpa [Real.norm_eq_abs] using hbound
    have hrpowOne : Real.rpow (Real.log L) (1 : ℝ) = Real.log L :=
      Real.rpow_one (Real.log L)
    rw [hrpowOne, abs_of_nonneg hDlog0,
      abs_of_nonneg hrpow0] at hbound'
    exact hbound'
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with L hsmallL hL
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL.le
  have hPA : P + A ≤ P + A + 1 := by linarith
  have hDidentity : (c / 12) * D = P + A + 1 := by
    dsimp [D]
    field_simp
  have hbudget :
      (P + A) * Real.log L ≤
        (c / 12) * Real.rpow L (1 - theta) := by
    have hleft :
        (P + A) * Real.log L ≤ (P + A + 1) * Real.log L :=
      mul_le_mul_of_nonneg_right hPA hlog0
    have hscaled := mul_le_mul_of_nonneg_left hsmallL (show 0 ≤ c / 12 by positivity)
    calc
      (P + A) * Real.log L ≤ (P + A + 1) * Real.log L := hleft
      _ = ((c / 12) * D) * Real.log L := by rw [hDidentity]
      _ = (c / 12) * (D * Real.log L) := by ring
      _ ≤ (c / 12) * Real.rpow L (1 - theta) := hscaled
  rw [show Real.rpow L P = Real.exp (Real.log L * P) from
        Real.rpow_def_of_pos hL0 P,
      show Real.rpow L (-A) = Real.exp (Real.log L * (-A)) from
        Real.rpow_def_of_pos hL0 (-A)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The preceding logarithmic-coordinate estimate after the substitution
`L = log X`. -/
theorem stretchedExp_beats_polylog
    (theta c P A : ℝ)
    (htheta : theta < 1) (hc : 0 < c)
    (hP : 0 ≤ P) (hA : 0 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      Real.rpow (Real.log X) P *
          Real.exp (-(c / 12) * Real.rpow (Real.log X) (1 - theta)) ≤
        Real.rpow (Real.log X) (-A) := by
  exact Real.tendsto_log_atTop.eventually
    (stretchedExp_beats_rpow theta c P A htheta hc hP hA)

/-- Exact conversion of the weak gap in the exponent of `X` to the stretched
exponential in `log X`. -/
theorem rpow_weakGap_eq_stretchedExp
    {X theta c : ℝ} (hX : 1 < X) :
    Real.rpow X (-(c * Real.rpow (Real.log X) (-theta) / 12)) =
      Real.exp (-(c / 12) * Real.rpow (Real.log X) (1 - theta)) := by
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hlogX0 : 0 < Real.log X := Real.log_pos hX
  have hrpow :
      Real.rpow (Real.log X) (1 - theta) =
        Real.log X * Real.rpow (Real.log X) (-theta) := by
    calc
      Real.rpow (Real.log X) (1 - theta) =
          Real.rpow (Real.log X) (1 + (-theta)) := by ring_nf
      _ = Real.rpow (Real.log X) 1 *
          Real.rpow (Real.log X) (-theta) :=
        Real.rpow_add hlogX0 1 (-theta)
      _ = Real.log X * Real.rpow (Real.log X) (-theta) := by simp
  calc
    Real.rpow X (-(c * Real.rpow (Real.log X) (-theta) / 12)) =
        Real.exp (Real.log X *
          (-(c * Real.rpow (Real.log X) (-theta) / 12))) :=
      Real.rpow_def_of_pos hX0 _
    _ = Real.exp (-(c / 12) * Real.rpow (Real.log X) (1 - theta)) := by
      rw [hrpow]
      congr 1
      ring

/-- The sharp obstruction at the classical exponent.  When `theta = 1`,
the near-one factor is a fixed constant, so it cannot by itself supply even
one negative power of `log X`. -/
theorem classicalGap_nearFactor_eq_constant
    {X c : ℝ} (hX : 1 < X) :
    Real.rpow X (-(c * Real.rpow (Real.log X) (-1 : ℝ) / 12)) =
      Real.exp (-(c / 12)) := by
  rw [rpow_weakGap_eq_stretchedExp (theta := 1) (c := c) hX]
  norm_num

/-- A weak zero-free lower bound for `omega` gives arbitrary logarithmic
saving in the exact MAP near-one factor `X^(-omega/12)`, including any fixed
polylogarithmic prefactor. -/
theorem weakGap_nearFactor_beats_polylog
    (theta c P A : ℝ)
    (htheta : theta < 1) (hc : 0 < c)
    (hP : 0 ≤ P) (hA : 0 ≤ A) :
    ∀ᶠ X : ℝ in atTop, ∀ omega : ℝ,
      c * Real.rpow (Real.log X) (-theta) ≤ omega →
      Real.rpow (Real.log X) P * Real.rpow X (-(omega / 12)) ≤
        Real.rpow (Real.log X) (-A) := by
  filter_upwards
    [stretchedExp_beats_polylog theta c P A htheta hc hP hA,
      eventually_gt_atTop (1 : ℝ)] with X hdecay hX omega homega
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hmono :
      Real.rpow X (-(omega / 12)) ≤
        Real.rpow X (-(c * Real.rpow (Real.log X) (-theta) / 12)) := by
    apply Real.rpow_le_rpow_of_exponent_le hX.le
    nlinarith
  calc
    Real.rpow (Real.log X) P * Real.rpow X (-(omega / 12)) ≤
        Real.rpow (Real.log X) P *
          Real.rpow X (-(c * Real.rpow (Real.log X) (-theta) / 12)) := by
      exact mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg (Real.log_pos hX).le _)
    _ = Real.rpow (Real.log X) P *
        Real.exp (-(c / 12) * Real.rpow (Real.log X) (1 - theta)) := by
      rw [rpow_weakGap_eq_stretchedExp hX]
    _ ≤ Real.rpow (Real.log X) (-A) := hdecay

end

end WeakVKNear

#print axioms WeakVKNear.stretchedExp_beats_rpow
#print axioms WeakVKNear.stretchedExp_beats_polylog
#print axioms WeakVKNear.rpow_weakGap_eq_stretchedExp
#print axioms WeakVKNear.classicalGap_nearFactor_eq_constant
#print axioms WeakVKNear.weakGap_nearFactor_beats_polylog
