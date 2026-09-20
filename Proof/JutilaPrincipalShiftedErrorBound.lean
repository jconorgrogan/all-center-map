import JutilaPrincipalDetectorVerticalIntegrability
import JutilaLemma6SieveCoefficientBridge
import JutilaLemma6DirectTail
import JutilaPseudocharacterHarmonicLower
import JutilaPrincipalDetectorPole

/-!
# Principal shifted error after one-pole displacement

Integrability of both vertical sides is now discharged, so the infinite
one-pole identity holds unconditionally.  The left-line integral is the
literal remainder after the crossed residue `principalDetectorPole` is
removed.  The canonical Mellin series therefore splits as that remainder
plus the pole; the high-ordinate bound `‖pole‖ < 1` is a separate estimate
and is not this identity.
-/

namespace MAPJutilaPrincipalShiftedErrorBound

open Complex Real MeasureTheory Set Filter Topology
open MAPJutilaPrincipalDetectorVerticalIntegrability
open MAPJutilaPrincipalDetectorInfiniteShift
open MAPJutilaPrincipalDetectorFinitePole
open MAPJutilaPrincipalDetectorPole
open MAPJutilaLemma6FiniteContour
open MAPJutilaLemma6SieveCoefficientBridge
open MAPJutilaLemma6DirectTail
open MAPJutilaMEntire
open MAPJutilaMNonnegativeHalfPlaneBound
open MAPJutilaPseudocharacterHarmonicLower
open JutilaPolynomialExponentialIntegral

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

def principalLeftVerticalMass : ℝ :=
  ∫ u : ℝ, (1 + |u|) ^ 7 * Real.exp (-|u|)

theorem integrable_principalLeftVerticalMass_integrand :
    Integrable (fun u : ℝ => (1 + |u|) ^ 7 * Real.exp (-|u|)) := by
  have h := integrable_shiftedAbsPowExp
    (A := 1) (k := 7) (c := 1) (by norm_num) (by norm_num)
  convert h using 1
  ext u
  simp [shiftedAbsPowExp]

theorem principalLeftVerticalMass_nonneg :
    0 ≤ principalLeftVerticalMass :=
  integral_nonneg fun _ => by positivity

theorem principalLeftVerticalMass_le :
    principalLeftVerticalMass ≤
      (2 : ℝ) ^ 7 *
        ((1 : ℝ) ^ 7 * (2 / 1) +
          2 * (1 / 1 : ℝ) ^ ((7 : ℝ) + 1) * (Nat.factorial 7 : ℝ)) := by
  have h := integral_shiftedAbsPowExp_le
    (A := 1) (k := 7) (c := 1) (by norm_num) (by norm_num)
  have hmass : principalLeftVerticalMass =
      ∫ u : ℝ, shiftedAbsPowExp 1 7 1 u := by
    unfold principalLeftVerticalMass shiftedAbsPowExp
    simp
  rw [hmass]
  exact h

/-- Infinite-height one-pole displacement with integrability discharged. -/
theorem principal_detector_right_eq_left_add_residue
    {beta t : ℝ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X : ℝ} (hX : 1 ≤ X)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    (∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X ((1 : ℂ) + u * I)) =
      (∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X (((-beta : ℝ) : ℂ) + u * I)) +
      (2 * Real.pi : ℂ) *
        principalLemmaSixResidue (lemmaSixZeroPoint beta t) xi D S X :=
  principal_detector_right_eq_left_add_residue_of_integrable
    xi hDpos S hX hbetaLo hbetaHi hrho
    (integrable_principal_detector_right xi hDpos S hX
      hbetaLo hbetaHi hrho)
    (integrable_principal_detector_left xi hDpos S hX
      hbetaLo hbetaHi hrho)

/-- Canonical-mollifier form: the crossed residue is `principalDetectorPole`. -/
theorem principal_canonical_right_eq_left_add_principalDetectorPole
    {beta t z1 z2 : ℝ} {R : ℕ} {X : ℝ}
    (hX : 1 ≤ X) (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    (∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
        (jutilaPrimedRSet 1 R) X ((1 : ℂ) + u * I)) =
      (∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
        (jutilaPrimedRSet 1 R) X (((-beta : ℝ) : ℂ) + u * I)) +
      (2 * Real.pi : ℂ) *
        principalDetectorPole (lemmaSixZeroPoint beta t) X z1 z2 R :=
  principal_canonical_right_eq_left_add_principalDetectorPole_of_integrable
    hX hbetaLo hbetaHi hrho
    (fun d hd => (Finset.mem_Icc.mp hd).1)
    (integrable_principal_canonical_right hX hbetaLo hbetaHi hrho)
    (integrable_principal_canonical_left hX hbetaLo hbetaHi hrho)

/-- Absolute left-line remainder after the pole is removed. -/
theorem norm_integral_principal_detector_left_le
    {beta t : ℝ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X C : ℝ} (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hM : ∀ s : ℂ, 0 ≤ s.re →
      ‖jutilaMWeightedSumComplex chiOne xi D S s‖ ≤ C)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    ‖∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X (((-beta : ℝ) : ℂ) + u * I)‖ ≤
      (24000 / (1 - beta)) * (5 + |t|) ^ 6 *
        Real.rpow X (-beta) * C * principalLeftVerticalMass := by
  let K : ℝ := (24000 / (1 - beta)) * (5 + |t|) ^ 6 *
    Real.rpow X (-beta) * C
  have hgap : 0 < 1 - beta := by linarith
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  let F : ℝ → ℂ := fun u =>
    jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
      xi D S X (((-beta : ℝ) : ℂ) + u * I)
  let E : ℝ → ℝ := fun u => K * ((1 + |u|) ^ 7 * Real.exp (-|u|))
  have hEbase := integrable_principalLeftVerticalMass_integrand
  have hE : Integrable E := hEbase.const_mul K
  have hpoint : ∀ u : ℝ, ‖F u‖ ≤ E u := fun u => by
    simpa [F, E, K] using
      norm_principal_detector_left_le xi hDpos S hX hC hM
        hbetaLo hbetaHi hrho (u := u)
  have hFint : Integrable F :=
    integrable_principal_detector_left xi hDpos S hX
      hbetaLo hbetaHi hrho
  calc
    ‖∫ u : ℝ, F u‖ ≤ ∫ u : ℝ, E u :=
      MeasureTheory.norm_integral_le_of_norm_le hE
        (Filter.Eventually.of_forall hpoint)
    _ = K * principalLeftVerticalMass := by
      rw [integral_const_mul]
      rfl
    _ = _ := by dsimp [K]

/-- The left-line integral is exactly the remainder
`∫right − 2π · residue`. -/
theorem principal_left_eq_right_sub_residue
    {beta t : ℝ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X : ℝ} (hX : 1 ≤ X)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    (∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X (((-beta : ℝ) : ℂ) + u * I)) =
      (∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X ((1 : ℂ) + u * I)) -
      (2 * Real.pi : ℂ) *
        principalLemmaSixResidue (lemmaSixZeroPoint beta t) xi D S X := by
  rw [principal_detector_right_eq_left_add_residue
    xi hDpos S hX hbetaLo hbetaHi hrho]
  ring

private theorem one_div_two_pi_mul_two_pi :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * Real.pi : ℂ)) = 1 := by
  have htwo : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
    simp [Complex.ofReal_mul]
  rw [htwo, ← Complex.ofReal_mul]
  have : (1 / (2 * Real.pi) : ℝ) * (2 * Real.pi) = 1 := by
    field_simp [Real.pi_ne_zero]
  rw [this, Complex.ofReal_one]

/-- Canonical Mellin series after the one-pole shift.  This is the detector
identity; it does not assert that the pole itself is small. -/
theorem principal_canonical_directSeries_eq_left_add_principalDetectorPole
    {beta t z1 z2 : ℝ} {R : ℕ} {X : ℝ}
    (hz1 : 1 < z1) (hz12 : z1 < z2)
    (hX : 1 ≤ X) (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    (∑' n : ℕ, jutilaLemmaSixDirectTerm chiOne z1 z2
        (jutilaPrimedRSet 1 R) (lemmaSixZeroPoint beta t) X n) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
          (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
          (jutilaPrimedRSet 1 R) X (((-beta : ℝ) : ℂ) + u * I)) +
      principalDetectorPole (lemmaSixZeroPoint beta t) X z1 z2 R := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hS : jutilaPrimedRSet 1 R ⊆ Finset.Icc 1 R :=
    jutilaPrimedRSet_subset_Icc 1 R
  have hrightRe : 1 < (lemmaSixZeroPoint beta t + (1 : ℂ)).re := by
    simp [lemmaSixZeroPoint]
    linarith
  have hmellin :=
    jutilaSelectedDirectSeries_eq_gamma_rightLine (q := 1) (R := R) chiOne
      hS (fun r hr => squarefree_of_mem_jutilaPrimedRSet hr)
      (fun r hr => coprime_of_mem_jutilaPrimedRSet hr)
      hz1 hz12 (c := 1) (by norm_num) hXpos
      (lemmaSixZeroPoint beta t) hrightRe
  have hrho1 : lemmaSixZeroPoint beta t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [lemmaSixZeroPoint] at hre
    linarith
  have hLrho :
      DirichletCharacter.LFunction chiOne (lemmaSixZeroPoint beta t) = 0 :=
    LFunction_chiOne_eq_zero_of_principalRegularized hrho hrho1
  have hpoint :
      (∫ v : ℝ,
        DirichletCharacter.LFunction chiOne
            (lemmaSixZeroPoint beta t + ((1 : ℂ) + v * I)) *
          jutilaMWeightedSumComplex chiOne
            (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
            (jutilaPrimedRSet 1 R)
            (lemmaSixZeroPoint beta t + ((1 : ℂ) + v * I)) *
          Complex.Gamma ((1 : ℂ) + v * I) *
          (X : ℂ) ^ ((1 : ℂ) + v * I)) =
        ∫ v : ℝ, jutilaDetectorExtension chiOne
          (lemmaSixZeroPoint beta t)
          (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
          (jutilaPrimedRSet 1 R) X ((1 : ℂ) + v * I) := by
    apply integral_congr_ae
    filter_upwards with v
    have hz : (1 : ℂ) + v * I ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
    rw [jutilaDetectorExtension_eq_raw chiOne
      (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
      (jutilaPrimedRSet 1 R) X hLrho hz]
    ring
  have hshift :=
    principal_canonical_right_eq_left_add_principalDetectorPole
      hX hbetaLo hbetaHi hrho (z1 := z1) (z2 := z2) (R := R)
  simp only [Complex.ofReal_one] at hmellin
  rw [hmellin, hpoint, hshift, mul_add]
  have hpole :
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((2 * Real.pi : ℂ) *
          principalDetectorPole (lemmaSixZeroPoint beta t) X z1 z2 R)) =
        principalDetectorPole (lemmaSixZeroPoint beta t) X z1 z2 R := by
    rw [← mul_assoc, one_div_two_pi_mul_two_pi, one_mul]
  rw [hpole]

/-- Shifted error: the canonical series minus the exact pole equals the
normalized left-line remainder. -/
theorem principal_canonical_directSeries_sub_pole_eq_left
    {beta t z1 z2 : ℝ} {R : ℕ} {X : ℝ}
    (hz1 : 1 < z1) (hz12 : z1 < z2)
    (hX : 1 ≤ X) (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    (∑' n : ℕ, jutilaLemmaSixDirectTerm chiOne z1 z2
        (jutilaPrimedRSet 1 R) (lemmaSixZeroPoint beta t) X n) -
      principalDetectorPole (lemmaSixZeroPoint beta t) X z1 z2 R =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
          (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
          (jutilaPrimedRSet 1 R) X (((-beta : ℝ) : ℂ) + u * I)) := by
  rw [principal_canonical_directSeries_eq_left_add_principalDetectorPole
    hz1 hz12 hX hbetaLo hbetaHi hrho]
  ring

theorem norm_principal_canonical_shiftedError_le
    {beta t z1 z2 : ℝ} {R : ℕ} {X C : ℝ}
    (hz1 : 1 < z1) (hz12 : z1 < z2)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hM : ∀ s : ℂ, 0 ≤ s.re →
      ‖jutilaMWeightedSumComplex chiOne (jutilaLambdaComplex z1 z2)
        (jutilaLambdaSupport z2) (jutilaPrimedRSet 1 R) s‖ ≤ C)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    ‖(∑' n : ℕ, jutilaLemmaSixDirectTerm chiOne z1 z2
        (jutilaPrimedRSet 1 R) (lemmaSixZeroPoint beta t) X n) -
      principalDetectorPole (lemmaSixZeroPoint beta t) X z1 z2 R‖ ≤
      (1 / (2 * Real.pi)) *
        ((24000 / (1 - beta)) * (5 + |t|) ^ 6 *
          Real.rpow X (-beta) * C * principalLeftVerticalMass) := by
  have hid := principal_canonical_directSeries_sub_pole_eq_left (R := R)
    hz1 hz12 hX hbetaLo hbetaHi hrho
  have hleft := norm_integral_principal_detector_left_le
    (jutilaLambdaComplex z1 z2)
    (fun d hd => (Finset.mem_Icc.mp hd).1)
    (jutilaPrimedRSet 1 R) hX hC hM hbetaLo hbetaHi hrho
  have hpi : 0 ≤ 1 / (2 * Real.pi) := by positivity
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hpi]
  exact mul_le_mul_of_nonneg_left hleft hpi

end

end MAPJutilaPrincipalShiftedErrorBound

#print axioms MAPJutilaPrincipalShiftedErrorBound.principal_detector_right_eq_left_add_residue
#print axioms MAPJutilaPrincipalShiftedErrorBound.principal_canonical_right_eq_left_add_principalDetectorPole
#print axioms MAPJutilaPrincipalShiftedErrorBound.norm_integral_principal_detector_left_le
#print axioms MAPJutilaPrincipalShiftedErrorBound.principal_canonical_directSeries_eq_left_add_principalDetectorPole
#print axioms MAPJutilaPrincipalShiftedErrorBound.norm_principal_canonical_shiftedError_le
