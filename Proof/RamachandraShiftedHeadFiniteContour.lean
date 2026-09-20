import RamachandraShiftedFunctionalEquationBridge
import FinitePoleRectangle
import KoukFunctionalEquationNonreal

/-!
# Finite reflected-head contour in shifted Ramachandra Lemma 3

The reflected head is a genuinely finite Dirichlet polynomial.  This module
replaces its `tsum` presentation by the exact finite sum and proves that the
head integrand is holomorphic throughout the pole-free strip `-1 < Re w < 0`.
Consequently its finite rectangle boundary integral vanishes.  Sending the
horizontal edges to infinity is a separate quantitative step.
-/

namespace RamachandraShiftedHeadFiniteContour

open Complex MeasureTheory Set
open scoped BigOperators LSeries.notation Interval
open BHPRamachandraMeanValueFromDyadicAFE
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedFunctionalEquationBridge
open FinitePoleRectangle
open MAPFunctionalZeroTransport

noncomputable section

set_option maxHeartbeats 800000

/-- Exact finite-sum presentation of the source's endpoint convention
`n ≤ X`.  The term at `n=0` is retained and is definitionally zero. -/
theorem ramachandraReflectedHead_eq_finset
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {X : ℝ} (hX : 0 ≤ X) (z : ℂ) :
    ramachandraReflectedHead psi X z =
      ∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        ramachandraReflectedTerm psi z n := by
  unfold ramachandraReflectedHead
  rw [tsum_eq_sum (s := Finset.range (⌊X⌋₊ + 1))]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnle : (n : ℝ) ≤ X := by
      rw [← Nat.le_floor_iff hX]
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    simp [hnle]
  · intro n hn
    have hfloor : ⌊X⌋₊ + 1 ≤ n := Nat.le_of_not_gt (by
      simpa using hn)
    have hXn : X < (n : ℝ) := by
      exact (Nat.lt_floor_add_one X).trans_le (by exact_mod_cast hfloor)
    simp [not_le.mpr hXn]

/-- A reflected divisor term is entire as a function of the reflected point.
The `n=0` branch is identically zero. -/
theorem differentiable_ramachandraReflectedTerm
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d) (n : ℕ) :
    Differentiable ℂ (fun z : ℂ => ramachandraReflectedTerm psi z n) := by
  by_cases hn : n = 0
  · subst n
    simp [ramachandraReflectedTerm, LSeries.term_zero]
  · unfold ramachandraReflectedTerm
    simp_rw [LSeries.term_of_ne_zero hn]
    apply Differentiable.div (differentiable_const _)
      ((differentiable_const (1 : ℂ)).sub differentiable_id |>.const_cpow
        (Or.inl (Nat.cast_ne_zero.mpr hn)))
    intro z
    exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Nat.cast_ne_zero.mpr hn))

/-- The reflected head is entire because it is the finite sum above. -/
theorem differentiable_ramachandraReflectedHead
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {X : ℝ} (hX : 0 ≤ X) :
    Differentiable ℂ (fun z : ℂ => ramachandraReflectedHead psi X z) := by
  rw [show (fun z : ℂ => ramachandraReflectedHead psi X z) =
      fun z : ℂ => ∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        ramachandraReflectedTerm psi z n by
    funext z
    exact ramachandraReflectedHead_eq_finset psi hX z]
  have hsum : Differentiable ℂ
      (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        (fun z : ℂ => ramachandraReflectedTerm psi z n)) := by
    apply Differentiable.sum
    intro n hn
    exact differentiable_ramachandraReflectedTerm psi n
  convert hsum using 1
  ext z
  simp

/-- A Dirichlet Gamma factor is holomorphic at every point of positive real
part. -/
theorem differentiableAt_gammaFactor_of_re_pos
    {d : ℕ} (psi : DirichletCharacter ℂ d) {z : ℂ}
    (hz : 0 < z.re) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor psi) z := by
  have hpoleEven : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    linarith
  have hpoleOdd : ∀ m : ℕ, (z + 1) / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    linarith
  rcases psi.even_or_odd with heven | hodd
  · rw [show DirichletCharacter.gammaFactor psi = Complex.Gammaℝ by
      funext u
      exact heven.gammaFactor_def u]
    change DifferentiableAt ℂ
      (fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2) * Complex.Gamma (u / 2)) z
    exact ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
        ((Complex.differentiableAt_Gamma (z / 2) hpoleEven).comp z (by fun_prop))
  · rw [show DirichletCharacter.gammaFactor psi =
      fun u => Complex.Gammaℝ (u + 1) by
      funext u
      exact hodd.gammaFactor_def u]
    change DifferentiableAt ℂ
      (fun u : ℂ => (Real.pi : ℂ) ^ (-(u + 1) / 2) *
        Complex.Gamma ((u + 1) / 2)) z
    exact (((differentiableAt_id.add_const 1).neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
        ((Complex.differentiableAt_Gamma ((z + 1) / 2) hpoleOdd).comp z
          (by fun_prop))

/-- The exact functional-equation multiplier is holomorphic wherever the
reflected numerator Gamma factor has positive real part. -/
theorem differentiableAt_ramachandraFunctionalFactor
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d) {z : ℂ}
    (hz : 0 < (1 - z).re) :
    DifferentiableAt ℂ (ramachandraFunctionalFactor psi) z := by
  unfold ramachandraFunctionalFactor
  rw [div_eq_mul_inv]
  have hpow : DifferentiableAt ℂ (fun u : ℂ =>
      (d : ℂ) ^ (1 / 2 - u)) z :=
    ((differentiableAt_const (1 / 2 : ℂ)).sub differentiableAt_id).const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne d)))
  have hnum : DifferentiableAt ℂ (fun u : ℂ =>
      psi⁻¹.gammaFactor (1 - u)) z :=
    (differentiableAt_gammaFactor_of_re_pos psi⁻¹ hz).comp z
      (by fun_prop)
  have hden : DifferentiableAt ℂ (fun u : ℂ =>
      (psi.gammaFactor u)⁻¹) z :=
    (analyticAt_gammaFactor_inv psi z).differentiableAt
  exact (((hpow.mul (differentiableAt_const psi.rootNumber)).mul hnum).mul hden)

/-- Gamma is holomorphic in the open strip between its poles at `-1` and
`0`. -/
theorem differentiableAt_Gamma_neg_one_zero {w : ℂ}
    (hwLo : -1 < w.re) (hwHi : w.re < 0) :
    DifferentiableAt ℂ Complex.Gamma w := by
  apply Complex.differentiableAt_Gamma
  intro m hm
  have hre := congrArg Complex.re hm
  have hre' : w.re = -(m : ℝ) := by simpa using hre
  by_cases hm0 : m = 0
  · subst m
    norm_num at hre'
    linarith
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith

/-- The literal reflected-head Mellin integrand as a function of `w`. -/
def shiftedHeadIntegrand {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (s : ℂ) (X : ℝ) (w : ℂ) : ℂ :=
  ramachandraFunctionalFactor psi (s + w) ^ 2 *
    ramachandraReflectedHead psi X (s + w) *
      Complex.Gamma w * (X : ℂ) ^ w

/-- Holomorphy of the finite-head integrand on the exact pole-free region
used in its contour displacement. -/
theorem differentiableAt_shiftedHeadIntegrand
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (s : ℂ) {X : ℝ} (hX : 0 < X) {w : ℂ}
    (hwLo : -1 < w.re) (hwHi : w.re < 0)
    (hz : (s + w).re < 1) :
    DifferentiableAt ℂ (shiftedHeadIntegrand psi s X) w := by
  unfold shiftedHeadIntegrand
  have hinner : DifferentiableAt ℂ (fun x : ℂ => s + x) w :=
    (differentiableAt_const s).add differentiableAt_id
  have hfactor : DifferentiableAt ℂ (fun x : ℂ =>
      ramachandraFunctionalFactor psi (s + x)) w :=
    (differentiableAt_ramachandraFunctionalFactor psi
      (z := s + w) (by simpa using sub_pos.mpr hz)).comp w hinner
  have hhead : DifferentiableAt ℂ (fun x : ℂ =>
      ramachandraReflectedHead psi X (s + x)) w :=
    (differentiable_ramachandraReflectedHead psi hX.le).differentiableAt.comp
      w hinner
  have hgamma := differentiableAt_Gamma_neg_one_zero hwLo hwHi
  have hscale : DifferentiableAt ℂ (fun x : ℂ => (X : ℂ) ^ x) w :=
    differentiableAt_id.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  exact (((hfactor.pow 2).mul hhead).mul hgamma).mul hscale

/-- Finite Cauchy--Goursat rectangle for the reflected head. -/
theorem rectangleBoundaryIntegral_shiftedHead_eq_zero
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (s : ℂ) {X a b u v : ℝ} (hX : 0 < X)
    (hab : a ≤ b) (ha : -1 < a) (hb : b < 0) (hz : s.re + b < 1) :
    rectangleBoundaryIntegral (shiftedHeadIntegrand psi s X) a b u v = 0 := by
  apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn
  intro w hw
  have hwre := hw.1
  rw [uIcc_of_le hab] at hwre
  apply (differentiableAt_shiftedHeadIntegrand psi s hX
    (show -1 < w.re by
      linarith [hwre.1])
    (show w.re < 0 by
      linarith [hwre.2])
    (show (s + w).re < 1 by
      simp only [add_re]
      linarith [hwre.2])).differentiableWithinAt

/-! ## Normalized finite deformation identity -/

def shiftedHeadVerticalLine {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (s : ℂ)
    (X c u v : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ y in u..v, shiftedHeadIntegrand psi s X ((c : ℂ) + y * I)

def shiftedHeadHorizontalEdges {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (s : ℂ)
    (X a b u v : ℝ) : ℂ :=
  ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) *
    ((∫ x in a..b,
        shiftedHeadIntegrand psi s X ((x : ℂ) + (u : ℂ) * I)) -
      ∫ x in a..b,
        shiftedHeadIntegrand psi s X ((x : ℂ) + (v : ℂ) * I))

/-- Exact finite-height head deformation.  There is no residue because both
vertical lines stay strictly between the Gamma poles at `-1` and `0`. -/
theorem shiftedHeadVerticalLine_eq_left_sub_horizontal
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (s : ℂ) {X a b u v : ℝ} (hX : 0 < X)
    (hab : a ≤ b) (ha : -1 < a) (hb : b < 0) (hz : s.re + b < 1) :
    shiftedHeadVerticalLine psi s X b u v =
      shiftedHeadVerticalLine psi s X a u v -
        shiftedHeadHorizontalEdges psi s X a b u v := by
  have hrect := rectangleBoundaryIntegral_shiftedHead_eq_zero
    psi s hX hab ha hb hz (u := u) (v := v)
  unfold rectangleBoundaryIntegral at hrect
  unfold shiftedHeadVerticalLine shiftedHeadHorizontalEdges
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpiC : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hpi
  apply mul_left_cancel₀ (mul_ne_zero hpiC I_ne_zero)
  field_simp [hpiC, I_ne_zero] at hrect ⊢
  push_cast at hrect ⊢
  linear_combination hrect

end
end RamachandraShiftedHeadFiniteContour

#print axioms RamachandraShiftedHeadFiniteContour.ramachandraReflectedHead_eq_finset
#print axioms RamachandraShiftedHeadFiniteContour.differentiable_ramachandraReflectedHead
#print axioms RamachandraShiftedHeadFiniteContour.differentiableAt_ramachandraFunctionalFactor
#print axioms RamachandraShiftedHeadFiniteContour.rectangleBoundaryIntegral_shiftedHead_eq_zero
#print axioms RamachandraShiftedHeadFiniteContour.shiftedHeadVerticalLine_eq_left_sub_horizontal
