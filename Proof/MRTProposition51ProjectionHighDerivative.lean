import MRTProposition51FirstAnalytic
import MRTVanDerCorputCore

/-!
# MRT Proposition 5.1: the literal derivative before equation (77)

MRT p.45--46 differentiates the source function `G` under its `x` integral.
This module proves the pointwise derivative of the exact integrand and its
algebraic identification with `logarithmicDualFunction`.  It deliberately does
not postulate the differentiated-integral identity or the desired projection
estimate.
-/

namespace MAPMRTProposition51ProjectionHighDerivative

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTVanDerCorputProof

noncomputable section

/-- The `x`-integrand in the source definition of `G` at MRT (74), with every
normalizing factor retained. -/
def sourceDualIntegrand
    (X H beta : ℝ) (cutoff : ℝ → ℝ) (g : ℝ → ℂ)
    (u x : ℝ) : ℂ :=
  (Real.sqrt X : ℂ) * (Real.exp (u / 2) : ℂ) *
    additivePhase (beta * X * Real.exp u) *
      (cutoff ((X * Real.exp u - x) / H) : ℂ) * g x

/-- The literal derivative of the preceding integrand.  It is kept as a
definition so the subsequent dominated-convergence obligation has an exact
target rather than an unspecified `G'`. -/
def sourceDualIntegrandDerivative
    (X H beta : ℝ) (cutoff cutoff' : ℝ → ℝ) (g : ℝ → ℂ)
    (u x : ℝ) : ℂ :=
  ((Real.sqrt X : ℂ) * (Real.exp (u / 2) / 2 : ℂ) *
      additivePhase (beta * X * Real.exp u) *
      (cutoff ((X * Real.exp u - x) / H) : ℂ) +
    (Real.sqrt X : ℂ) * (Real.exp (u / 2) : ℂ) *
      (((2 * Real.pi : ℂ) * Complex.I *
          (beta * X * Real.exp u : ℂ)) *
        additivePhase (beta * X * Real.exp u)) *
      (cutoff ((X * Real.exp u - x) / H) : ℂ) +
    (Real.sqrt X : ℂ) * (Real.exp (u / 2) : ℂ) *
      additivePhase (beta * X * Real.exp u) *
      (cutoff' ((X * Real.exp u - x) / H) : ℂ) *
      (X * Real.exp u / H : ℂ)) * g x

set_option maxHeartbeats 800000

/-- Pointwise calculus for the exact source integrand.  No interchange of
derivative and integral is used here. -/
theorem hasDerivAt_sourceDualIntegrand
    {X H beta u x : ℝ} {cutoff cutoff' : ℝ → ℝ} {g : ℝ → ℂ}
    (hH : H ≠ 0)
    (hcutoff : ∀ y, HasDerivAt cutoff (cutoff' y) y) :
    HasDerivAt (fun z ↦ sourceDualIntegrand X H beta cutoff g z x)
      (sourceDualIntegrandDerivative X H beta cutoff cutoff' g u x) u := by
  have hexpHalf : HasDerivAt (fun z : ℝ ↦ (Real.exp (z / 2) : ℂ))
      (Real.exp (u / 2) / 2 : ℂ) u := by
    convert ((Real.hasDerivAt_exp (u / 2)).scomp u
      ((hasDerivAt_id u).div_const 2)).ofReal_comp using 1 <;>
      simp [Function.comp_def, smul_eq_mul, div_eq_mul_inv] <;> ring
  have hphaseReal : HasDerivAt (fun z : ℝ ↦ beta * X * Real.exp z)
      (beta * X * Real.exp u) u := by
    simpa [mul_assoc] using (Real.hasDerivAt_exp u).const_mul (beta * X)
  have hphase : HasDerivAt
      (fun z : ℝ ↦ additivePhase (beta * X * Real.exp z))
      (((2 * Real.pi : ℂ) * Complex.I *
          (beta * X * Real.exp u : ℂ)) *
        additivePhase (beta * X * Real.exp u)) u :=
    by
      convert (@hasDerivAt_additivePhase_comp
        (fun z : ℝ ↦ beta * X * Real.exp z)
        (fun z : ℝ ↦ beta * X * Real.exp z) u hphaseReal) using 1 <;>
        push_cast <;> ring
  have harg : HasDerivAt
      (fun z : ℝ ↦ (X * Real.exp z - x) / H)
      (X * Real.exp u / H) u := by
    simpa [div_eq_mul_inv, mul_assoc] using
      (((Real.hasDerivAt_exp u).const_mul X).sub_const x).div_const H
  have hcutReal : HasDerivAt
      (fun z : ℝ ↦ cutoff ((X * Real.exp z - x) / H))
      (cutoff' ((X * Real.exp u - x) / H) *
        (X * Real.exp u / H)) u := by
    convert (hcutoff _).scomp u harg using 1 <;>
      simp [Function.comp_def, smul_eq_mul] <;> ring
  have hcut : HasDerivAt
      (fun z : ℝ ↦ (cutoff ((X * Real.exp z - x) / H) : ℂ))
      ((cutoff' ((X * Real.exp u - x) / H) *
        (X * Real.exp u / H) : ℝ) : ℂ) u := hcutReal.ofReal_comp
  have hprod := (((hexpHalf.const_mul (Real.sqrt X : ℂ)).mul hphase).mul hcut)
    |>.mul_const (g x)
  dsimp only [Pi.mul_apply] at hprod
  unfold sourceDualIntegrand sourceDualIntegrandDerivative
  convert hprod using 1 <;> push_cast <;> ring

/-- Moving the scalar factors inside the `x` integral recovers the exact
definition of `G`; this is the algebraic half of the differentiation step. -/
theorem logarithmicDualFunction_eq_integral_sourceDualIntegrand
    {X H beta u : ℝ} {cutoff : ℝ → ℝ} {g : ℝ → ℂ}
    (hint : Integrable (fun x : ℝ ↦
      (cutoff ((X * Real.exp u - x) / H) : ℂ) * g x)) :
    logarithmicDualFunction X H beta cutoff g u =
      ∫ x : ℝ, sourceDualIntegrand X H beta cutoff g u x := by
  unfold logarithmicDualFunction sourceDualIntegrand
  let C : ℂ := (Real.sqrt X : ℂ) * (Real.exp (u / 2) : ℂ) *
    additivePhase (beta * X * Real.exp u)
  calc
    (Real.sqrt X : ℂ) * (Real.exp (u / 2) : ℂ) *
        additivePhase (beta * X * Real.exp u) *
        ∫ x : ℝ, (cutoff ((X * Real.exp u - x) / H) : ℂ) * g x =
      C * ∫ x : ℝ, (cutoff ((X * Real.exp u - x) / H) : ℂ) * g x := by rfl
    _ = ∫ x : ℝ, C *
        ((cutoff ((X * Real.exp u - x) / H) : ℂ) * g x) := by
      rw [integral_const_mul]
    _ = ∫ x : ℝ,
        (Real.sqrt X : ℂ) * (Real.exp (u / 2) : ℂ) *
          additivePhase (beta * X * Real.exp u) *
          (cutoff ((X * Real.exp u - x) / H) : ℂ) * g x := by
      apply integral_congr_ae
      filter_upwards with x
      unfold C
      ring

/-- The exact `x=Xe^u+O(H)` window occurring in the derivative estimate on
MRT p.46. -/
def sourceDerivativeWindow (X H u : ℝ) : Set ℝ :=
  Set.Icc (X * Real.exp u - H) (X * Real.exp u + H)

theorem mem_sourceDerivativeWindow_iff
    {X H u x : ℝ} (hH : 0 ≤ H) :
    x ∈ sourceDerivativeWindow X H u ↔
      |X * Real.exp u - x| ≤ H := by
  unfold sourceDerivativeWindow
  rw [Set.mem_Icc, abs_le]
  constructor
  · intro hx
    constructor <;> linarith [hx.1, hx.2]
  · intro hx
    constructor <;> linarith [hx.1, hx.2]

/-- Both cutoff terms in the exact derivative vanish outside the printed
localized window. -/
theorem sourceDualIntegrandDerivative_eq_zero_off_window
    {X H beta u x : ℝ} {cutoff cutoff' : ℝ → ℝ} {g : ℝ → ℂ}
    (hH : 0 < H)
    (hcutoffSupport : ∀ y, 1 < |y| → cutoff y = 0)
    (hcutoffDerivSupport : ∀ y, 1 < |y| → cutoff' y = 0)
    (hx : x ∉ sourceDerivativeWindow X H u) :
    sourceDualIntegrandDerivative X H beta cutoff cutoff' g u x = 0 := by
  have habs : H < |X * Real.exp u - x| := by
    have hnot : ¬ |X * Real.exp u - x| ≤ H := by
      intro hle
      exact hx ((mem_sourceDerivativeWindow_iff hH.le).2 hle)
    exact lt_of_not_ge hnot
  have hquot : 1 < |(X * Real.exp u - x) / H| := by
    rw [abs_div, abs_of_pos hH]
    exact (lt_div_iff₀ hH).2 (by simpa [one_mul] using habs)
  unfold sourceDualIntegrandDerivative
  rw [hcutoffSupport _ hquot, hcutoffDerivSupport _ hquot]
  simp

/-- The formal derivative integral is exactly localized to the source window.
This is the measure-theoretic version of the display at source lines
2323--2326, before estimating its norm. -/
theorem integral_sourceDualIntegrandDerivative_eq_window
    {X H beta u : ℝ} {cutoff cutoff' : ℝ → ℝ} {g : ℝ → ℂ}
    (hH : 0 < H)
    (hcutoffSupport : ∀ y, 1 < |y| → cutoff y = 0)
    (hcutoffDerivSupport : ∀ y, 1 < |y| → cutoff' y = 0) :
    (∫ x : ℝ,
      sourceDualIntegrandDerivative X H beta cutoff cutoff' g u x) =
      ∫ x : ℝ in sourceDerivativeWindow X H u,
        sourceDualIntegrandDerivative X H beta cutoff cutoff' g u x := by
  unfold sourceDerivativeWindow
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ sourceDerivativeWindow X H u
  · have hx' : x ∈ Set.Icc (X * Real.exp u - H) (X * Real.exp u + H) := hx
    rw [Set.indicator_of_mem hx']
  · rw [sourceDualIntegrandDerivative_eq_zero_off_window hH
      hcutoffSupport hcutoffDerivSupport hx]
    have hx' : x ∉ Set.Icc (X * Real.exp u - H) (X * Real.exp u + H) := hx
    rw [Set.indicator_of_notMem hx']

/-- A global pointwise majorant for the literal derivative.  Its only inputs
are the `C¹` cutoff bounds.  This is the domination needed for differentiating
under the `x` integral; localization is supplied separately by
`integral_sourceDualIntegrandDerivative_eq_window`. -/
theorem norm_sourceDualIntegrandDerivative_le
    {X H beta u x B : ℝ} {cutoff cutoff' : ℝ → ℝ} {g : ℝ → ℂ}
    (hH : 0 < H) (hB : 0 ≤ B)
    (hcutoff : ∀ y, |cutoff y| ≤ B)
    (hcutoff' : ∀ y, |cutoff' y| ≤ B) :
    ‖sourceDualIntegrandDerivative X H beta cutoff cutoff' g u x‖ ≤
      Real.sqrt X * Real.exp (u / 2) *
        (B / 2 + 2 * Real.pi * |beta| * |X| * Real.exp u * B +
          B * (|X| * Real.exp u / H)) * ‖g x‖ := by
  let A : ℂ := (Real.sqrt X : ℂ) * (Real.exp (u / 2) / 2 : ℂ) *
      additivePhase (beta * X * Real.exp u) *
      (cutoff ((X * Real.exp u - x) / H) : ℂ)
  let P : ℂ := (Real.sqrt X : ℂ) * (Real.exp (u / 2) : ℂ) *
      (((2 * Real.pi : ℂ) * Complex.I *
          (beta * X * Real.exp u : ℂ)) *
        additivePhase (beta * X * Real.exp u)) *
      (cutoff ((X * Real.exp u - x) / H) : ℂ)
  let C : ℂ := (Real.sqrt X : ℂ) * (Real.exp (u / 2) : ℂ) *
      additivePhase (beta * X * Real.exp u) *
      (cutoff' ((X * Real.exp u - x) / H) : ℂ) *
      (X * Real.exp u / H : ℂ)
  have htri : ‖A + P + C‖ ≤ ‖A‖ + ‖P‖ + ‖C‖ := by
    nlinarith [norm_add_le A P, norm_add_le (A + P) C]
  have hA : ‖A‖ ≤
      Real.sqrt X * Real.exp (u / 2) * (B / 2) := by
    unfold A
    simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      norm_additivePhase]
    rw [abs_of_nonneg (Real.sqrt_nonneg X)]
    norm_num
    have hc := hcutoff ((X * Real.exp u - x) / H)
    calc
      Real.sqrt X * (Real.exp (u / 2) / 2) *
          |cutoff ((X * Real.exp u - x) / H)| =
        (Real.sqrt X * Real.exp (u / 2) / 2) *
          |cutoff ((X * Real.exp u - x) / H)| := by ring
      _ ≤ (Real.sqrt X * Real.exp (u / 2) / 2) * B := by
        exact mul_le_mul_of_nonneg_left hc (by positivity)
      _ = Real.sqrt X * Real.exp (u / 2) * (B / 2) := by ring
  have hP : ‖P‖ ≤
      Real.sqrt X * Real.exp (u / 2) *
        (2 * Real.pi * |beta| * |X| * Real.exp u * B) := by
    unfold P
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, norm_additivePhase, mul_one]
    rw [abs_of_nonneg (Real.sqrt_nonneg X),
      abs_of_nonneg (Real.exp_nonneg _),
      abs_of_pos Real.pi_pos,
      abs_of_nonneg (Real.exp_nonneg _)]
    norm_num
    have hc := hcutoff ((X * Real.exp u - x) / H)
    let Q := Real.sqrt X * Real.exp (u / 2) *
      (2 * Real.pi * |beta| * |X| * Real.exp u)
    calc
      Real.sqrt X * Real.exp (u / 2) *
          (2 * Real.pi * (|beta| * |X| * Real.exp u)) *
          |cutoff ((X * Real.exp u - x) / H)| =
        Q * |cutoff ((X * Real.exp u - x) / H)| := by unfold Q; ring
      _ ≤ Q * B := by
        exact mul_le_mul_of_nonneg_left hc (by unfold Q; positivity)
      _ = Real.sqrt X * Real.exp (u / 2) *
          (2 * Real.pi * |beta| * |X| * Real.exp u * B) := by
        unfold Q
        ring
  have hC : ‖C‖ ≤
      Real.sqrt X * Real.exp (u / 2) *
        (B * (|X| * Real.exp u / H)) := by
    unfold C
    simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      norm_additivePhase]
    rw [abs_of_nonneg (Real.sqrt_nonneg X),
      abs_of_nonneg (Real.exp_nonneg _), abs_of_pos hH,
      abs_of_nonneg (Real.exp_nonneg _)]
    have hc := hcutoff' ((X * Real.exp u - x) / H)
    let Q := Real.sqrt X * Real.exp (u / 2) *
      (|X| * Real.exp u / H)
    calc
      Real.sqrt X * Real.exp (u / 2) * 1 *
          |cutoff' ((X * Real.exp u - x) / H)| *
          (|X| * Real.exp u / H) =
        Q * |cutoff' ((X * Real.exp u - x) / H)| := by unfold Q; ring
      _ ≤ Q * B := by
        exact mul_le_mul_of_nonneg_left hc (by unfold Q; positivity)
      _ = Real.sqrt X * Real.exp (u / 2) *
          (B * (|X| * Real.exp u / H)) := by unfold Q; ring
  unfold sourceDualIntegrandDerivative
  rw [norm_mul]
  change ‖A + P + C‖ * ‖g x‖ ≤ _
  calc
    ‖A + P + C‖ * ‖g x‖ ≤ (‖A‖ + ‖P‖ + ‖C‖) * ‖g x‖ :=
      mul_le_mul_of_nonneg_right htri (norm_nonneg _)
    _ ≤ (Real.sqrt X * Real.exp (u / 2) * (B / 2) +
        Real.sqrt X * Real.exp (u / 2) *
          (2 * Real.pi * |beta| * |X| * Real.exp u * B) +
        Real.sqrt X * Real.exp (u / 2) *
          (B * (|X| * Real.exp u / H))) * ‖g x‖ := by
      gcongr
    _ = _ := by ring

/-- The exact derivative-under-the-integral statement needed to specialize
equation (77) to the source `G`.  This is a named proposition, not an axiom;
the module proves its pointwise integrand derivative above but does not claim
an inhabitant without the dominated-convergence proof. -/
def SourceDifferentiatedIntegralIdentity : Prop :=
  ∀ (X H beta : ℝ) (cutoff cutoff' : ℝ → ℝ) (g : ℝ → ℂ),
    0 < H → Integrable g →
    (∀ y, HasDerivAt cutoff (cutoff' y) y) →
    (∃ B : ℝ, 0 ≤ B ∧
      (∀ y, |cutoff y| ≤ B) ∧ (∀ y, |cutoff' y| ≤ B)) →
    ∀ u, HasDerivAt
      (logarithmicDualFunction X H beta cutoff g)
      (∫ x : ℝ,
        sourceDualIntegrandDerivative X H beta cutoff cutoff' g u x) u

end
end MAPMRTProposition51ProjectionHighDerivative

#print axioms MAPMRTProposition51ProjectionHighDerivative.hasDerivAt_sourceDualIntegrand
#print axioms MAPMRTProposition51ProjectionHighDerivative.logarithmicDualFunction_eq_integral_sourceDualIntegrand
#print axioms MAPMRTProposition51ProjectionHighDerivative.sourceDualIntegrandDerivative_eq_zero_off_window
#print axioms MAPMRTProposition51ProjectionHighDerivative.integral_sourceDualIntegrandDerivative_eq_window
