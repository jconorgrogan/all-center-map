import PrincipalZetaDetectorPoleRemoval
import FinitePoleRectangle
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exact finite contour for the principal zeta detector

The principal detector has one crossed pole at `z = 1 - rho`.  This file
applies the certified finite-pole rectangle theorem to that literal pole and
the analytic remainder from `PrincipalZetaDetectorPoleRemoval`.  It proves the
finite contour identity with the exact residue; no zero-density or asymptotic
estimate is assumed.
-/

namespace MAPPrincipalZetaPoleContour

open Set MeasureTheory Complex Filter
open scoped Topology
open MAPMellinDetectorLeaf MAPMollifierCoefficientIdentity
open MAPPrincipalZetaDetectorPoleRemoval

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

/-- Raw Gamma--zeta--mollifier detector away from the translated zeta pole. -/
def principalRawDetector
    (rho : ℂ) (U : ℕ) (Y : ℝ) (z : ℂ) : ℂ :=
  gammaMellinWeight Y z * riemannZeta (rho + z) *
    mollifier chiOne U (rho + z)

/-- On every pole-free point, the raw detector is the analytic remainder plus
its one literal principal part. -/
theorem principalRawDetector_eq_poleRemoved_add
    {rho z : ℂ} {U : ℕ} {Y : ℝ}
    (hrho : principalF rho = 0) (hz : z ≠ 0)
    (hpole : z ≠ principalPoleLocation rho) :
    principalRawDetector rho U Y z =
      principalPoleRemovedDetector rho U Y z +
        principalDetectorResidue rho U Y *
          (z - principalPoleLocation rho)⁻¹ := by
  have h := principalPoleRemoved_eq_raw_sub_residue
    (rho := rho) (z := z) (U := U) (Y := Y) hrho hz hpole
  unfold principalRawDetector
  rw [div_eq_mul_inv] at h
  rw [h]
  ring

/-- Exact positively-oriented boundary integral.  The excision radius is half
the horizontal distance from the translated zeta pole to the right edge, so
the argument works throughout `1/2 < beta <= 1`. -/
theorem principalRawDetector_rectangleBoundaryIntegral
    {rho : ℂ} {U : ℕ} {Y B : ℝ}
    (hrho : principalF rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (hY : 0 < Y) (hB : |rho.im| + (rho.re - 1 / 2) / 2 < B) :
    FinitePoleRectangle.rectangleBoundaryIntegral
        (principalRawDetector rho U Y)
        (1 / 2 - rho.re) (1 / 2) (-B) B =
      (2 * Real.pi * I) * principalDetectorResidue rho U Y := by
  let a : ℝ := 1 / 2 - rho.re
  let b : ℝ := 1 / 2
  let u : ℝ := -B
  let v : ℝ := B
  let p : Unit → ℂ := fun _ => principalPoleLocation rho
  let residue : Unit → ℂ := fun _ => principalDetectorResidue rho U Y
  let radius : Unit → ℝ := fun _ => (rho.re - 1 / 2) / 2
  let f : ℂ → ℂ := principalRawDetector rho U Y
  let g : ℂ → ℂ := principalPoleRemovedDetector rho U Y
  have hBpos : 0 < B := by
    nlinarith [abs_nonneg rho.im]
  have hgDifferentiable : DifferentiableOn ℂ g (Set.uIcc a b ×ℂ Set.uIcc u v) := by
    intro z hz
    apply (analyticAt_principalPoleRemovedDetector hY hbetaHigh ?_).differentiableAt.differentiableWithinAt
    change -1 < z.re
    have hab : a ≤ b := by dsimp [a, b]; linarith
    have hzre : a ≤ z.re := by
      rw [Set.uIcc_of_le hab] at hz
      exact (Complex.mem_reProdIm.mp hz).1.1
    dsimp [a] at hzre
    linarith
  have hgIntegrable : FinitePoleRectangle.BoundaryIntervalIntegrable g a b u v :=
    FinitePoleRectangle.boundaryIntervalIntegrable_of_differentiableOn hgDifferentiable
  have hrhoOne : rho ≠ 1 := by
    intro h
    subst rho
    simpa using hrho
  have hedge (z : ℂ) (hz0 : z ≠ 0)
      (hzp : z ≠ principalPoleLocation rho) :
      f z = g z + residue () * (z - p ())⁻¹ := by
    simpa [f, g, residue, p] using
      principalRawDetector_eq_poleRemoved_add
        (rho := rho) (z := z) (U := U) (Y := Y) hrho hz0 hzp
  have hresult :=
    FinitePoleRectangle.rectangleBoundaryIntegral_eq_two_pi_I_mul_sum_residue
      ({()} : Finset Unit) p residue radius f g a b u v
      (by intro i hi; simp [radius]; linarith)
      (by intro i hi; simp [a, p, radius, principalPoleLocation]; linarith)
      (by intro i hi; simp [b, p, radius, principalPoleLocation]; linarith)
      (by
        intro i hi
        simp only [Finset.mem_singleton] at hi
        cases i
        simp [u, p, radius, principalPoleLocation]
        have him : rho.im ≤ |rho.im| := le_abs_self _
        linarith)
      (by
        intro i hi
        simp only [Finset.mem_singleton] at hi
        cases i
        simp [v, p, radius, principalPoleLocation]
        have him : -rho.im ≤ |rho.im| := neg_le_abs _
        linarith)
      hgIntegrable hgDifferentiable
      (by
        intro x
        apply (show f ((x : ℂ) + (u : ℂ) * I) =
          g ((x : ℂ) + (u : ℂ) * I) + residue () *
            (((x : ℂ) + (u : ℂ) * I) - p ())⁻¹ from hedge _ ?_ ?_) |>.trans
        · simp
        · intro hz
          have him := congrArg Complex.im hz
          simp [u] at him
          linarith
        · intro hzp
          have him := congrArg Complex.im hzp
          simp [u, principalPoleLocation] at him
          have habs := le_abs_self rho.im
          linarith)
      (by
        intro x
        apply (show f ((x : ℂ) + (v : ℂ) * I) =
          g ((x : ℂ) + (v : ℂ) * I) + residue () *
            (((x : ℂ) + (v : ℂ) * I) - p ())⁻¹ from hedge _ ?_ ?_) |>.trans
        · simp
        · intro hz
          have him := congrArg Complex.im hz
          simp [v] at him
          linarith
        · intro hzp
          have him := congrArg Complex.im hzp
          simp [v, principalPoleLocation] at him
          have habs := neg_le_abs rho.im
          linarith)
      (by
        intro y
        apply (show f ((b : ℂ) + (y : ℂ) * I) =
          g ((b : ℂ) + (y : ℂ) * I) + residue () *
            (((b : ℂ) + (y : ℂ) * I) - p ())⁻¹ from hedge _ ?_ ?_) |>.trans
        · simp
        · intro hz
          have hre := congrArg Complex.re hz
          norm_num [b] at hre
        · intro hzp
          have hre := congrArg Complex.re hzp
          simp [b, principalPoleLocation] at hre
          linarith)
      (by
        intro y
        apply (show f ((a : ℂ) + (y : ℂ) * I) =
          g ((a : ℂ) + (y : ℂ) * I) + residue () *
            (((a : ℂ) + (y : ℂ) * I) - p ())⁻¹ from hedge _ ?_ ?_) |>.trans
        · simp
        · intro hz
          have hre := congrArg Complex.re hz
          simp [a] at hre
          linarith
        · intro hzp
          have hre := congrArg Complex.re hzp
          simp [a, principalPoleLocation] at hre)
  simpa [a, b, u, v, f, residue] using hresult

/-- Abstract infinite-height passage with one fixed residue.  This is the
residue-bearing counterpart of the pole-free contour limit used in Appendix
A.4. -/
theorem full_vertical_integrals_eq_add_residue_of_boundary
    (F : ℂ → ℂ) {a c : ℝ} (R : ℂ)
    (hleft : Integrable (fun t : ℝ => F (a + t * I)))
    (hright : Integrable (fun t : ℝ => F (c + t * I)))
    (hminus : Tendsto (fun B : ℝ =>
        ∫ x : ℝ in a..c, F (x - B * I)) atTop (𝓝 0))
    (hplus : Tendsto (fun B : ℝ =>
        ∫ x : ℝ in a..c, F (x + B * I)) atTop (𝓝 0))
    (hboundary : ∀ᶠ B : ℝ in atTop,
      FinitePoleRectangle.rectangleBoundaryIntegral F a c (-B) B =
        (2 * Real.pi * I) * R) :
    (∫ t : ℝ, F (c + t * I)) =
      (∫ t : ℝ, F (a + t * I)) + 2 * Real.pi * R := by
  let VR : ℝ → ℂ := fun B => ∫ t : ℝ in -B..B, F (c + t * I)
  let VL : ℝ → ℂ := fun B => ∫ t : ℝ in -B..B, F (a + t * I)
  let Hminus : ℝ → ℂ := fun B => ∫ x : ℝ in a..c, F (x - B * I)
  let Hplus : ℝ → ℂ := fun B => ∫ x : ℝ in a..c, F (x + B * I)
  have hVR : Tendsto VR atTop (𝓝 (∫ t : ℝ, F (c + t * I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hright
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hVL : Tendsto VL atTop (𝓝 (∫ t : ℝ, F (a + t * I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hleft
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hbalance : ∀ᶠ B : ℝ in atTop,
      I * (VR B - VL B) =
        (2 * Real.pi * I) * R + Hplus B - Hminus B := by
    filter_upwards [hboundary] with B hB
    dsimp [VR, VL, Hminus, Hplus]
    rw [FinitePoleRectangle.rectangleBoundaryIntegral] at hB
    simp only [ofReal_neg, neg_mul, sub_eq_add_neg] at hB
    linear_combination hB
  have hlhs : Tendsto (fun B => I * (VR B - VL B)) atTop
      (𝓝 (I * ((∫ t : ℝ, F (c + t * I)) -
        ∫ t : ℝ, F (a + t * I)))) :=
    tendsto_const_nhds.mul (hVR.sub hVL)
  have hrhs : Tendsto (fun B =>
      (2 * Real.pi * I) * R + Hplus B - Hminus B) atTop
      (𝓝 ((2 * Real.pi * I) * R)) := by
    simpa [Hplus, Hminus] using
      (tendsto_const_nhds.add hplus).sub hminus
  have hlhsResidue : Tendsto (fun B => I * (VR B - VL B)) atTop
      (𝓝 ((2 * Real.pi * I) * R)) :=
    hrhs.congr' (hbalance.mono fun B hB => hB.symm)
  have hlimit :
      I * ((∫ t : ℝ, F (c + t * I)) -
        ∫ t : ℝ, F (a + t * I)) =
          (2 * Real.pi * I) * R :=
    tendsto_nhds_unique hlhs hlhsResidue
  have hcancel :
      (∫ t : ℝ, F (c + t * I)) -
        ∫ t : ℝ, F (a + t * I) = 2 * Real.pi * R := by
    have hI : I * (2 * Real.pi * R) = (2 * Real.pi * I) * R := by ring
    apply (mul_left_cancel₀ Complex.I_ne_zero)
    simpa [hI] using hlimit
  linear_combination hcancel

/-- Full principal contour shift, conditional only on the literal raw vertical
integrability and horizontal decay.  The finite residue theorem above supplies
the boundary identity premise-free. -/
theorem principalRawDetector_full_vertical_identity
    {rho : ℂ} {U : ℕ} {Y : ℝ}
    (hrho : principalF rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (hY : 0 < Y)
    (hleft : Integrable (fun t : ℝ =>
      principalRawDetector rho U Y ((1 / 2 - rho.re : ℝ) + t * I)))
    (hright : Integrable (fun t : ℝ =>
      principalRawDetector rho U Y ((1 / 2 : ℝ) + t * I)))
    (hminus : Tendsto (fun B : ℝ =>
      ∫ x : ℝ in (1 / 2 - rho.re)..(1 / 2),
        principalRawDetector rho U Y (x - B * I)) atTop (𝓝 0))
    (hplus : Tendsto (fun B : ℝ =>
      ∫ x : ℝ in (1 / 2 - rho.re)..(1 / 2),
        principalRawDetector rho U Y (x + B * I)) atTop (𝓝 0)) :
    (∫ t : ℝ,
        principalRawDetector rho U Y ((1 / 2 : ℝ) + t * I)) =
      (∫ t : ℝ,
        principalRawDetector rho U Y
          ((1 / 2 - rho.re : ℝ) + t * I)) +
        2 * Real.pi * principalDetectorResidue rho U Y := by
  apply full_vertical_integrals_eq_add_residue_of_boundary
    (principalRawDetector rho U Y) (principalDetectorResidue rho U Y)
    hleft hright hminus hplus
  filter_upwards [eventually_gt_atTop
      (|rho.im| + (rho.re - 1 / 2) / 2)] with B hB
  exact principalRawDetector_rectangleBoundaryIntegral
    hrho hbetaLow hbetaHigh hY hB

end
end MAPPrincipalZetaPoleContour

#print axioms MAPPrincipalZetaPoleContour.principalRawDetector_eq_poleRemoved_add
#print axioms MAPPrincipalZetaPoleContour.principalRawDetector_rectangleBoundaryIntegral
#print axioms MAPPrincipalZetaPoleContour.full_vertical_integrals_eq_add_residue_of_boundary
#print axioms MAPPrincipalZetaPoleContour.principalRawDetector_full_vertical_identity
