import JutilaP53TwoScaleContour

/-!
# Finite shifted contour and left-line decomposition for Jutila p.53

This specializes the already certified holomorphy of the two-scale integrand
to the literal rectangle with right edge `Re w = 1` and left edge
`Re w = -a`.  The exact identity retains both horizontal edges; quantitative
Gamma decay can therefore be attached without changing the contour algebra.
-/

namespace MAPJutilaP53FiniteShift

open Complex Real MeasureTheory Set
open MAPJutilaP53TwoScaleContour

noncomputable section

/-- Exact finite nonprincipal displacement from `Re w=1` to `Re w=-a`. -/
theorem finiteRectangle_p53TwoScale_nonprincipal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) {U V a T : ℝ} (hU : 0 < U) (hV : 0 < V)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hT : 0 ≤ T) :
    (∫ x : ℝ in -a..1,
        p53TwoScaleContourIntegrand chi s U V (x - T * I)) -
      (∫ x : ℝ in -a..1,
        p53TwoScaleContourIntegrand chi s U V (x + T * I)) +
      I • (∫ y : ℝ in -T..T,
        p53TwoScaleContourIntegrand chi s U V (1 + y * I)) -
      I • (∫ y : ℝ in -T..T,
        p53TwoScaleContourIntegrand chi s U V (-a + y * I)) = 0 := by
  let z : ℂ := (-a : ℂ) - (T : ℂ) * I
  let w : ℂ := (1 : ℂ) + (T : ℂ) * I
  have hstrip : ∀ u ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im),
      -1 < u.re := by
    intro u hu
    have hleft : -a ≤ u.re := by
      simpa [z, w, min_eq_left (by linarith : -a ≤ (1 : ℝ))] using hu.1.1
    linarith
  have h := p53TwoScaleContourIntegrand_boundary_rectangle_nonprincipal
    hchi s hU hV z w hstrip
  simpa [z, w, min_eq_left (by linarith : -T ≤ T),
    max_eq_right (by linarith : -T ≤ T), sub_eq_add_neg] using h

/-- Solved form: the right vertical line is the left vertical line plus the
oriented horizontal correction. -/
theorem p53TwoScale_right_eq_left_add_horizontals
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) {U V a T : ℝ} (hU : 0 < U) (hV : 0 < V)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hT : 0 ≤ T) :
    (∫ y : ℝ in -T..T,
        p53TwoScaleContourIntegrand chi s U V (1 + y * I)) =
      (∫ y : ℝ in -T..T,
        p53TwoScaleContourIntegrand chi s U V (-a + y * I)) +
      I * ((∫ x : ℝ in -a..1,
        p53TwoScaleContourIntegrand chi s U V (x - T * I)) -
        (∫ x : ℝ in -a..1,
          p53TwoScaleContourIntegrand chi s U V (x + T * I))) := by
  have h := finiteRectangle_p53TwoScale_nonprincipal chi hchi s hU hV
    ha0 ha1 hT
  simp only [smul_eq_mul] at h ⊢
  have hh := congrArg (fun z : ℂ => (-I) * z) h
  simp [mul_add, mul_sub, ← mul_assoc, Complex.I_mul_I] at hh
  linear_combination hh

/-- Triangle-inequality left-line estimate with both finite horizontal errors
shown separately.  This is the exact quantitative interface needed for Gamma
decay and fixed-strip L-function bounds. -/
theorem norm_p53TwoScale_right_le_left_add_horizontals
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) {U V a T : ℝ} (hU : 0 < U) (hV : 0 < V)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hT : 0 ≤ T) :
    ‖∫ y : ℝ in -T..T,
        p53TwoScaleContourIntegrand chi s U V (1 + y * I)‖ ≤
      ‖∫ y : ℝ in -T..T,
        p53TwoScaleContourIntegrand chi s U V (-a + y * I)‖ +
      ‖∫ x : ℝ in -a..1,
        p53TwoScaleContourIntegrand chi s U V (x - T * I)‖ +
      ‖∫ x : ℝ in -a..1,
        p53TwoScaleContourIntegrand chi s U V (x + T * I)‖ := by
  rw [p53TwoScale_right_eq_left_add_horizontals chi hchi s hU hV
    ha0 ha1 hT]
  calc
    ‖(∫ y : ℝ in -T..T,
          p53TwoScaleContourIntegrand chi s U V (-a + y * I)) +
        I * ((∫ x : ℝ in -a..1,
          p53TwoScaleContourIntegrand chi s U V (x - T * I)) -
          (∫ x : ℝ in -a..1,
            p53TwoScaleContourIntegrand chi s U V (x + T * I)))‖ ≤
      ‖∫ y : ℝ in -T..T,
          p53TwoScaleContourIntegrand chi s U V (-a + y * I)‖ +
        ‖I * ((∫ x : ℝ in -a..1,
          p53TwoScaleContourIntegrand chi s U V (x - T * I)) -
          (∫ x : ℝ in -a..1,
            p53TwoScaleContourIntegrand chi s U V (x + T * I)))‖ := norm_add_le _ _
    _ = ‖∫ y : ℝ in -T..T,
          p53TwoScaleContourIntegrand chi s U V (-a + y * I)‖ +
        ‖(∫ x : ℝ in -a..1,
          p53TwoScaleContourIntegrand chi s U V (x - T * I)) -
          (∫ x : ℝ in -a..1,
            p53TwoScaleContourIntegrand chi s U V (x + T * I))‖ := by
      rw [norm_mul, norm_I, one_mul]
    _ ≤ ‖∫ y : ℝ in -T..T,
          p53TwoScaleContourIntegrand chi s U V (-a + y * I)‖ +
        (‖∫ x : ℝ in -a..1,
          p53TwoScaleContourIntegrand chi s U V (x - T * I)‖ +
        ‖∫ x : ℝ in -a..1,
          p53TwoScaleContourIntegrand chi s U V (x + T * I)‖) := by
      have hh := add_le_add_left (norm_sub_le
        (∫ x : ℝ in -a..1,
          p53TwoScaleContourIntegrand chi s U V (x - T * I))
        (∫ x : ℝ in -a..1,
          p53TwoScaleContourIntegrand chi s U V (x + T * I)))
        ‖∫ y : ℝ in -T..T,
          p53TwoScaleContourIntegrand chi s U V (-a + y * I)‖
      simpa only [add_assoc, add_comm, add_left_comm] using hh
    _ = _ := by ring

end

end MAPJutilaP53FiniteShift

#print axioms MAPJutilaP53FiniteShift.finiteRectangle_p53TwoScale_nonprincipal
#print axioms MAPJutilaP53FiniteShift.norm_p53TwoScale_right_le_left_add_horizontals
