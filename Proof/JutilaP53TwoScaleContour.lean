import JutilaP53InnerMellinRightLine
import DirichletZeros
import PrimitiveLFixedStripGrowth
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The exact two-scale contour used on Jutila p.53

The difference of the two exponential smoothing scales removes the Gamma
pole at `w=0`.  This file constructs the removable quotient, proves the
nonprincipal finite-rectangle displacement, and identifies the sole
principal residue at `w=-s`.  Quantitative bounds and the infinite-height
limit remain separate.
-/

namespace MAPJutilaP53TwoScaleContour

open Complex Real MeasureTheory Set Filter
open DirichletZeros
open MAPPrimitiveLFixedStrip MAPGammaMellinInversion

noncomputable section

def p53ScaleDifference (U V : ℝ) (w : ℂ) : ℂ :=
  (U : ℂ) ^ w - (V : ℂ) ^ w

def p53ScaleRemovableQuotient (U V : ℝ) : ℂ → ℂ :=
  Function.update
    (fun w : ℂ => p53ScaleDifference U V w / w)
    0 (Complex.log (U : ℂ) - Complex.log (V : ℂ))

theorem continuousAt_p53ScaleRemovableQuotient_zero
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V) :
    ContinuousAt (p53ScaleRemovableQuotient U V) 0 := by
  have hUC : (U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU.ne'
  have hVC : (V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV.ne'
  have hA := (hasDerivAt_id' (0 : ℂ)).const_cpow
    (c := (U : ℂ)) (Or.inl hUC)
  have hB := (hasDerivAt_id' (0 : ℂ)).const_cpow
    (c := (V : ℂ)) (Or.inl hVC)
  have hdiff := hA.sub hB
  have hcont := hdiff.continuousAt_div
  simpa [p53ScaleRemovableQuotient, p53ScaleDifference] using hcont

theorem analyticAt_p53ScaleRemovableQuotient_zero
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V) :
    AnalyticAt ℂ (p53ScaleRemovableQuotient U V) 0 := by
  have hUC : (U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU.ne'
  have hVC : (V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV.ne'
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [self_mem_nhdsWithin] with w hw
    have hw0 : w ≠ 0 := by simpa using hw
    have hbase : DifferentiableAt ℂ
        (fun u : ℂ => p53ScaleDifference U V u / u) w := by
      apply DifferentiableAt.div _ differentiableAt_id hw0
      exact
        ((hasDerivAt_id' w).const_cpow
          (c := (U : ℂ)) (Or.inl hUC)).differentiableAt.sub
        ((hasDerivAt_id' w).const_cpow
          (c := (V : ℂ)) (Or.inl hVC)).differentiableAt
    refine hbase.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hw0] with u hu
    simp [p53ScaleRemovableQuotient, Function.update_of_ne hu]
  · exact continuousAt_p53ScaleRemovableQuotient_zero hU hV

theorem differentiableAt_p53ScaleRemovableQuotient
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (w : ℂ) :
    DifferentiableAt ℂ (p53ScaleRemovableQuotient U V) w := by
  rcases eq_or_ne w 0 with rfl | hw
  · exact (analyticAt_p53ScaleRemovableQuotient_zero hU hV).differentiableAt
  · have hUC : (U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU.ne'
    have hVC : (V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV.ne'
    have hbase : DifferentiableAt ℂ
        (fun u : ℂ => p53ScaleDifference U V u / u) w := by
      apply DifferentiableAt.div _ differentiableAt_id hw
      exact
        ((hasDerivAt_id' w).const_cpow
          (c := (U : ℂ)) (Or.inl hUC)).differentiableAt.sub
        ((hasDerivAt_id' w).const_cpow
          (c := (V : ℂ)) (Or.inl hVC)).differentiableAt
    refine hbase.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hw] with u hu
    simp [p53ScaleRemovableQuotient, Function.update_of_ne hu]

def p53TwoScaleContourIntegrand
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (s : ℂ) (U V : ℝ) (w : ℂ) : ℂ :=
  Complex.Gamma (w + 1) * p53ScaleRemovableQuotient U V w *
    DirichletCharacter.LFunction chi (1 + s + w)

def p53RightOneScaleIntegrand
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (s : ℂ) (U : ℝ) (v : ℝ) : ℂ :=
  DirichletCharacter.LFunction chi
      (1 + s + ((1 : ℝ) : ℂ) + v * I) *
    Complex.Gamma (((1 : ℝ) : ℂ) + v * I) *
    (U : ℂ) ^ (((1 : ℝ) : ℂ) + v * I)

theorem integrable_p53RightOneScaleIntegrand
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 ≤ s.re) {U : ℝ} (hU : 0 < U) :
    Integrable (p53RightOneScaleIntegrand chi s U) := by
  letI : NeZero (U : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr hU.ne'⟩
  have hLcont : Continuous (fun v : ℝ =>
      DirichletCharacter.LFunction chi
        (1 + s + ((1 : ℝ) : ℂ) + v * I)) := by
    rw [continuous_iff_continuousAt]
    intro v
    have harg : 1 + s + ((1 : ℝ) : ℂ) + (v : ℂ) * I ≠ 1 := by
      intro heq
      have hre := congrArg Complex.re heq
      simp at hre
      linarith
    have hinner : ContinuousAt (fun u : ℝ =>
        1 + s + ((1 : ℝ) : ℂ) + (u : ℂ) * I) v := by fun_prop
    have houter : ContinuousAt (DirichletCharacter.LFunction chi)
        (1 + s + ((1 : ℝ) : ℂ) + (v : ℂ) * I) :=
      (DirichletCharacter.differentiableAt_LFunction chi _
        (Or.inl harg)).continuousAt
    simpa only [Function.comp_apply] using
      (ContinuousAt.comp
        (f := fun u : ℝ =>
          1 + s + ((1 : ℝ) : ℂ) + (u : ℂ) * I)
        (g := DirichletCharacter.LFunction chi)
        (x := v) houter hinner)
  have hGcont : Continuous (fun v : ℝ =>
      Complex.Gamma (((1 : ℝ) : ℂ) + v * I)) := by
    rw [continuous_iff_continuousAt]
    intro v
    have hnp : ∀ n : ℕ,
        (((1 : ℝ) : ℂ) + (v : ℂ) * I) ≠ -(n : ℂ) := by
      intro n hn
      have hre := congrArg Complex.re hn
      norm_num [Complex.neg_re] at hre
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hinner : ContinuousAt (fun u : ℝ =>
        ((1 : ℝ) : ℂ) + (u : ℂ) * I) v := by fun_prop
    have houter : ContinuousAt Complex.Gamma
        (((1 : ℝ) : ℂ) + (v : ℂ) * I) :=
      Complex.continuousAt_Gamma _ hnp
    simpa only [Function.comp_apply] using
      (ContinuousAt.comp
        (f := fun u : ℝ => ((1 : ℝ) : ℂ) + (u : ℂ) * I)
        (g := Complex.Gamma) (x := v) houter hinner)
  have hPowCont : Continuous (fun v : ℝ =>
      (U : ℂ) ^ (((1 : ℝ) : ℂ) + v * I)) :=
    continuous_const_cpow (U : ℂ) |>.comp (by fun_prop)
  have hmeas : AEStronglyMeasurable (p53RightOneScaleIntegrand chi s U) :=
    ((hLcont.mul hGcont).mul hPowCont).aestronglyMeasurable
  have hGamma : Integrable (fun v : ℝ =>
      Complex.Gamma (((1 : ℝ) : ℂ) + v * I)) :=
    verticalIntegrable_Gamma zero_lt_one
  have hmajor : Integrable (fun v : ℝ =>
      (3 * U) * ‖Complex.Gamma (((1 : ℝ) : ℂ) + v * I)‖) :=
    hGamma.norm.const_mul (3 * U)
  apply hmajor.mono' hmeas
  filter_upwards [] with v
  have hargRe : 2 ≤
      (1 + s + ((1 : ℝ) : ℂ) + (v : ℂ) * I).re := by
    simp
    linarith
  have hL := (norm_LFunction_lt_three_of_two_le_re chi hargRe).le
  have hpow :
      ‖(U : ℂ) ^ (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ = U := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hU]
    simp
  unfold p53RightOneScaleIntegrand
  rw [norm_mul, norm_mul, hpow]
  have hG0 := norm_nonneg
    (Complex.Gamma (((1 : ℝ) : ℂ) + (v : ℂ) * I))
  calc
    ‖DirichletCharacter.LFunction chi
          (1 + s + ((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ *
          ‖Complex.Gamma (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ * U ≤
        3 *
          ‖Complex.Gamma (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ * U := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hL hG0) hU.le
    _ = 3 * U *
        ‖Complex.Gamma (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ := by ring

theorem p53TwoScaleContourIntegrand_eq_raw
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (s : ℂ) (U V : ℝ) {w : ℂ} (hw : w ≠ 0) :
    p53TwoScaleContourIntegrand chi s U V w =
      DirichletCharacter.LFunction chi (1 + s + w) *
        Complex.Gamma w * p53ScaleDifference U V w := by
  unfold p53TwoScaleContourIntegrand p53ScaleRemovableQuotient
  rw [Function.update_of_ne hw, Complex.Gamma_add_one w hw]
  field_simp

theorem differentiableAt_p53TwoScaleContourIntegrand_nonprincipal
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hchi : chi ≠ 1) (s : ℂ) {U V : ℝ}
    (hU : 0 < U) (hV : 0 < V) (w : ℂ) (hw : -1 < w.re) :
    DifferentiableAt ℂ (p53TwoScaleContourIntegrand chi s U V) w := by
  have hGammaNoPole : ∀ n : ℕ, w + 1 ≠ -(n : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num [Complex.neg_re] at hre
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hGamma : DifferentiableAt ℂ (fun u : ℂ => Complex.Gamma (u + 1)) w :=
    (Complex.differentiableAt_Gamma (w + 1) hGammaNoPole).comp w (by fun_prop)
  have hL : DifferentiableAt ℂ
      (fun u : ℂ => DirichletCharacter.LFunction chi (1 + s + u)) w :=
    (DirichletCharacter.differentiable_LFunction hchi (1 + s + w)).comp
      w (by fun_prop)
  exact (hGamma.mul
    (differentiableAt_p53ScaleRemovableQuotient hU hV w)).mul hL

theorem p53TwoScaleContourIntegrand_boundary_rectangle_nonprincipal
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hchi : chi ≠ 1) (s : ℂ) {U V : ℝ}
    (hU : 0 < U) (hV : 0 < V) (z w : ℂ)
    (hstrip : ∀ u ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im),
      -1 < u.re) :
    (∫ x : ℝ in z.re..w.re,
          p53TwoScaleContourIntegrand chi s U V
            (x + z.im * Complex.I)) -
        (∫ x : ℝ in z.re..w.re,
          p53TwoScaleContourIntegrand chi s U V
            (x + w.im * Complex.I)) +
        Complex.I • (∫ y : ℝ in z.im..w.im,
          p53TwoScaleContourIntegrand chi s U V
            (w.re + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in z.im..w.im,
          p53TwoScaleContourIntegrand chi s U V
            (z.re + y * Complex.I)) = 0 := by
  apply Complex.integral_boundary_rect_eq_zero_of_differentiableOn
  intro u hu
  exact (differentiableAt_p53TwoScaleContourIntegrand_nonprincipal
    hchi s hU hV u (hstrip u hu)).differentiableWithinAt

def p53PrincipalResidue
    (q : ℕ) [NeZero q] (s : ℂ) (U V : ℝ) : ℂ :=
  Complex.Gamma (1 - s) * p53ScaleRemovableQuotient U V (-s) *
    regularizedLFunction (1 : DirichletCharacter ℂ q) 1

/-- The only principal L-pole crossed by the p.53 two-scale contour is at
`w=-s`, and its residue retains the exact conductor Euler factor. -/
theorem p53TwoScaleContourIntegrand_principal_residue
    (q : ℕ) [NeZero q] {s : ℂ} (hs : s.re < 1)
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V) :
    Tendsto
      (fun w : ℂ => (w - (-s)) *
        p53TwoScaleContourIntegrand
          (1 : DirichletCharacter ℂ q) s U V w)
      (nhdsWithin (-s) ({(-s)}ᶜ))
      (nhds (p53PrincipalResidue q s U V)) := by
  let p : ℂ := -s
  let A : ℂ → ℂ := fun w =>
    Complex.Gamma (w + 1) * p53ScaleRemovableQuotient U V w *
      regularizedLFunction (1 : DirichletCharacter ℂ q) (1 + s + w)
  have hpStrip : -1 < p.re := by dsimp [p]; simp; linarith
  have hGammaNoPole : ∀ n : ℕ, p + 1 ≠ -(n : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num [Complex.neg_re] at hre
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hGamma : ContinuousAt (fun w : ℂ => Complex.Gamma (w + 1)) p :=
    ((Complex.differentiableAt_Gamma (p + 1) hGammaNoPole).comp
      p (by fun_prop)).continuousAt
  have hQ : ContinuousAt (p53ScaleRemovableQuotient U V) p :=
    (differentiableAt_p53ScaleRemovableQuotient hU hV p).continuousAt
  have hreg : ContinuousAt (fun w : ℂ =>
      regularizedLFunction (1 : DirichletCharacter ℂ q) (1 + s + w)) p :=
    ((differentiable_regularizedLFunction
      (1 : DirichletCharacter ℂ q)).differentiableAt.comp
        p (by fun_prop)).continuousAt
  have hA : ContinuousAt A p := (hGamma.mul hQ).mul hreg
  have hAp : A p = p53PrincipalResidue q s U V := by
    unfold A p53PrincipalResidue
    have harg : 1 + s + p = 1 := by dsimp [p]; ring
    rw [harg]
    congr 2
    congr 1
    dsimp [p]
    ring
  have hlim : Tendsto A (nhdsWithin p ({p}ᶜ))
      (nhds (p53PrincipalResidue q s U V)) := by
    rw [← hAp]
    exact hA.tendsto.mono_left inf_le_left
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hwp : w ≠ p := by simpa using hw
  have harg : 1 + s + w ≠ 1 := by
    intro heq
    apply hwp
    dsimp [p]
    linear_combination heq
  have hregEq :
      regularizedLFunction (1 : DirichletCharacter ℂ q) (1 + s + w) =
        (s + w) * DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ q) (1 + s + w) := by
    simp only [regularizedLFunction, if_pos]
    unfold DirichletCharacter.LFunctionTrivChar₁
    rw [Function.update_of_ne harg]
    ring
  unfold A p53TwoScaleContourIntegrand
  rw [hregEq]
  ring

end

end MAPJutilaP53TwoScaleContour

#print axioms MAPJutilaP53TwoScaleContour.p53TwoScaleContourIntegrand_boundary_rectangle_nonprincipal
#print axioms MAPJutilaP53TwoScaleContour.p53TwoScaleContourIntegrand_principal_residue
