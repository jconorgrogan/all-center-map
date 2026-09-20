import JutilaP53DivisorKernelAbsoluteMass
import FinitePoleRectangle

/-!
# Principal-character finite-pole contour on Jutila p.53

The principal `L`-pole at `w=-s` is removed by taking the divided difference
of its entire numerator.  This gives the exact finite rectangle identity with
the conductor Euler factor retained in the residue.
-/

namespace MAPJutilaP53PrincipalFinitePole

open Complex Real MeasureTheory Set Filter
open MAPJutilaP53TwoScaleContour
open RamachandraShiftedGammaPoleContour
open FinitePoleRectangle
open DirichletZeros

noncomputable section

def p53PrincipalNumerator (q : ℕ) [NeZero q]
    (s : ℂ) (U V : ℝ) (w : ℂ) : ℂ :=
  Complex.Gamma (w + 1) * p53ScaleRemovableQuotient U V w *
    regularizedLFunction (1 : DirichletCharacter ℂ q) (1 + s + w)

def p53PrincipalRemainder (q : ℕ) [NeZero q]
    (s : ℂ) (U V : ℝ) : ℂ → ℂ :=
  dslope (p53PrincipalNumerator q s U V) (-s)

private theorem analyticAt_dslope_of_analyticAt
    {f : ℂ → ℂ} {p z : ℂ} (hp : AnalyticAt ℂ f p)
    (hz : AnalyticAt ℂ f z) : AnalyticAt ℂ (dslope f p) z := by
  by_cases hzp : z = p
  · subst z
    rcases hp with ⟨P, hP⟩
    exact ⟨P.fslope, hP.has_fpower_series_dslope_fslope⟩
  · have hdiv : AnalyticAt ℂ (fun w : ℂ => (f w - f p) / (w - p)) z :=
      hz.sub analyticAt_const |>.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr hzp)
    apply hdiv.congr
    filter_upwards [dslope_eventuallyEq_slope_of_ne f hzp] with w hw
    rw [hw]
    simp only [slope, vsub_eq_sub, div_eq_inv_mul]
    ring

theorem analyticAt_p53PrincipalNumerator
    (q : ℕ) [NeZero q] {s w : ℂ} {U V : ℝ}
    (hU : 0 < U) (hV : 0 < V) (hw : -1 < w.re) :
    AnalyticAt ℂ (p53PrincipalNumerator q s U V) w := by
  let S : Set ℂ := {z | -1 < z.re}
  have hSopen : IsOpen S := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ (p53PrincipalNumerator q s U V) S := by
    intro z hz
    have hzstrip : -1 < z.re := hz
    have hGammaNoPole : ∀ n : ℕ, z + 1 ≠ -(n : ℂ) := by
      intro n hn
      have hre := congrArg Complex.re hn
      norm_num [Complex.neg_re] at hre
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    unfold p53PrincipalNumerator
    have hGamma : DifferentiableAt ℂ
        (fun u : ℂ => Complex.Gamma (u + 1)) z :=
      (Complex.differentiableAt_Gamma (z + 1) hGammaNoPole).comp z (by fun_prop)
    have hQ := differentiableAt_p53ScaleRemovableQuotient hU hV z
    have hreg : DifferentiableAt ℂ (fun u : ℂ =>
        regularizedLFunction (1 : DirichletCharacter ℂ q) (1 + s + u)) z :=
      (differentiable_regularizedLFunction
        (1 : DirichletCharacter ℂ q)).differentiableAt.comp z (by fun_prop)
    exact ((hGamma.mul hQ).mul hreg).differentiableWithinAt
  exact hdiff.analyticAt (hSopen.mem_nhds hw)

theorem analyticAt_p53PrincipalRemainder
    (q : ℕ) [NeZero q] {s w : ℂ} {U V : ℝ}
    (hU : 0 < U) (hV : 0 < V) (hs : s.re < 1)
    (hw : -1 < w.re) :
    AnalyticAt ℂ (p53PrincipalRemainder q s U V) w := by
  unfold p53PrincipalRemainder
  apply analyticAt_dslope_of_analyticAt
  · apply analyticAt_p53PrincipalNumerator q hU hV
    simp
    linarith
  · exact analyticAt_p53PrincipalNumerator q hU hV hw

@[simp] theorem p53PrincipalNumerator_at_pole
    (q : ℕ) [NeZero q] (s : ℂ) (U V : ℝ) :
    p53PrincipalNumerator q s U V (-s) =
      p53PrincipalResidue q s U V := by
  unfold p53PrincipalNumerator p53PrincipalResidue
  have harg : 1 + s + -s = 1 := by ring
  rw [harg]
  ring

/-- Away from `w=-s`, the literal integrand is the holomorphic remainder
plus its exact principal part. -/
theorem p53PrincipalIntegrand_eq_remainder_add_residue
    (q : ℕ) [NeZero q] {s w : ℂ} {U V : ℝ}
    (hwp : w ≠ -s) :
    p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V w =
      p53PrincipalRemainder q s U V w +
        p53PrincipalResidue q s U V * (w - (-s))⁻¹ := by
  have harg : 1 + s + w ≠ 1 := by
    intro heq
    apply hwp
    linear_combination heq
  have hreg :
      regularizedLFunction (1 : DirichletCharacter ℂ q) (1 + s + w) =
        (s + w) * DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ q) (1 + s + w) := by
    simp only [regularizedLFunction, if_pos]
    unfold DirichletCharacter.LFunctionTrivChar₁
    rw [Function.update_of_ne harg]
    ring
  have hden : w - (-s) ≠ 0 := sub_ne_zero.mpr hwp
  have hraw :
      p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V w =
        p53PrincipalNumerator q s U V w / (w - (-s)) := by
    unfold p53TwoScaleContourIntegrand p53PrincipalNumerator
    rw [hreg]
    field_simp [hden]
    ring
  have hds : p53PrincipalRemainder q s U V w =
      (p53PrincipalNumerator q s U V w -
        p53PrincipalNumerator q s U V (-s)) / (w - (-s)) := by
    rw [p53PrincipalRemainder, dslope_of_ne]
    · simp only [slope, vsub_eq_sub, div_eq_inv_mul]
      ring
    · exact hwp
  rw [hraw, hds, p53PrincipalNumerator_at_pole]
  field_simp [hden]
  ring

/-- Exact finite rectangle shift across the sole principal pole `w=-s`. -/
theorem rectangleBoundaryIntegral_p53Principal_eq_residue
    (q : ℕ) [NeZero q] {s : ℂ} {U V a b u v r : ℝ}
    (hU : 0 < U) (hV : 0 < V) (hs : s.re < 1)
    (hr : 0 < r) (haStrip : -1 < a)
    (hleft : a < (-s).re - r) (hright : (-s).re + r < b)
    (hbottom : u < (-s).im - r) (htop : (-s).im + r < v) :
    rectangleBoundaryIntegral
        (p53TwoScaleContourIntegrand
          (1 : DirichletCharacter ℂ q) s U V) a b u v =
      (2 * Real.pi * Complex.I) * p53PrincipalResidue q s U V := by
  let p : Unit → ℂ := fun _ => -s
  let R : Unit → ℂ := fun _ => p53PrincipalResidue q s U V
  let rad : Unit → ℝ := fun _ => r
  let g := p53PrincipalRemainder q s U V
  have hab : a ≤ b := by linarith
  have huv : u ≤ v := by linarith
  have hleft' : a < -s.re - r := by simpa using hleft
  have hright' : -s.re + r < b := by simpa using hright
  have hbottom' : u < -s.im - r := by simpa using hbottom
  have htop' : -s.im + r < v := by simpa using htop
  have hgdiff : DifferentiableOn ℂ g
      (Set.uIcc a b ×ℂ Set.uIcc u v) := by
    intro z hz
    have hzre : a ≤ z.re := by
      have h := hz.1.1
      rw [min_eq_left hab] at h
      exact h
    exact (analyticAt_p53PrincipalRemainder q hU hV hs
      (haStrip.trans_le hzre)).differentiableAt.differentiableWithinAt
  have hedge (z : ℂ) (hzp : z ≠ -s) :
      p53TwoScaleContourIntegrand
          (1 : DirichletCharacter ℂ q) s U V z =
        g z + p53PrincipalResidue q s U V * (z - (-s))⁻¹ := by
    exact p53PrincipalIntegrand_eq_remainder_add_residue q hzp
  have hsum : (∑ i ∈ ({()} : Finset Unit), R i) =
      p53PrincipalResidue q s U V := by simp [R]
  rw [← hsum]
  apply rectangleBoundaryIntegral_eq_two_pi_I_mul_sum_residue
    ({()} : Finset Unit) p R rad
    (p53TwoScaleContourIntegrand
      (1 : DirichletCharacter ℂ q) s U V) g a b u v
  · intro i hi; simpa [rad] using hr
  · intro i hi; simpa [p, rad] using hleft
  · intro i hi; simpa [p, rad] using hright
  · intro i hi; simpa [p, rad] using hbottom
  · intro i hi; simpa [p, rad] using htop
  · exact boundaryIntervalIntegrable_of_differentiableOn hgdiff
  · exact hgdiff
  · intro x
    have hzp : (x : ℂ) + (u : ℂ) * I ≠ -s := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith [hbottom']
    simpa [p, R, g] using hedge ((x : ℂ) + (u : ℂ) * I) hzp
  · intro x
    have hzp : (x : ℂ) + (v : ℂ) * I ≠ -s := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith [htop']
    simpa [p, R, g] using hedge ((x : ℂ) + (v : ℂ) * I) hzp
  · intro y
    have hzp : (b : ℂ) + (y : ℂ) * I ≠ -s := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith [hright']
    simpa [p, R, g] using hedge ((b : ℂ) + (y : ℂ) * I) hzp
  · intro y
    have hzp : (a : ℂ) + (y : ℂ) * I ≠ -s := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith [hleft']
    simpa [p, R, g] using hedge ((a : ℂ) + (y : ℂ) * I) hzp

/-- Solved finite-line form of the principal displacement.  Both horizontal
edges and the exact residue remain visible. -/
theorem p53Principal_right_eq_left_add_horizontals_add_residue
    (q : ℕ) [NeZero q] {s : ℂ} {U V a b u v r : ℝ}
    (hU : 0 < U) (hV : 0 < V) (hs : s.re < 1)
    (hr : 0 < r) (haStrip : -1 < a)
    (hleft : a < (-s).re - r) (hright : (-s).re + r < b)
    (hbottom : u < (-s).im - r) (htop : (-s).im + r < v) :
    (∫ y : ℝ in u..v,
        p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q)
          s U V (b + y * I)) =
      (∫ y : ℝ in u..v,
        p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q)
          s U V (a + y * I)) +
      I * ((∫ x : ℝ in a..b,
        p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q)
          s U V (x + u * I)) -
        (∫ x : ℝ in a..b,
          p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q)
            s U V (x + v * I))) +
      (2 * Real.pi : ℂ) * p53PrincipalResidue q s U V := by
  have hrect := rectangleBoundaryIntegral_p53Principal_eq_residue q
    hU hV hs hr haStrip hleft hright hbottom htop
  unfold rectangleBoundaryIntegral at hrect
  have hh := congrArg (fun z : ℂ => (-I) * z) hrect
  simp [mul_add, mul_sub, ← mul_assoc, Complex.I_mul_I] at hh
  have hres :
      -(I * 2 * (Real.pi : ℂ) * I * p53PrincipalResidue q s U V) =
        (2 * Real.pi : ℂ) * p53PrincipalResidue q s U V := by
    calc
      _ = -((I * I) * ((2 * Real.pi : ℂ) *
          p53PrincipalResidue q s U V)) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [hres] at hh
  linear_combination hh

end

end MAPJutilaP53PrincipalFinitePole

#print axioms MAPJutilaP53PrincipalFinitePole.analyticAt_p53PrincipalNumerator
#print axioms MAPJutilaP53PrincipalFinitePole.analyticAt_p53PrincipalRemainder
#print axioms MAPJutilaP53PrincipalFinitePole.p53PrincipalIntegrand_eq_remainder_add_residue
#print axioms MAPJutilaP53PrincipalFinitePole.rectangleBoundaryIntegral_p53Principal_eq_residue
#print axioms MAPJutilaP53PrincipalFinitePole.p53Principal_right_eq_left_add_horizontals_add_residue
