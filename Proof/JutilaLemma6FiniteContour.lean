import JutilaMEntire
import JutilaLemma6ErrorBound
import AppendixA4Detector

/-!
# Finite residue-cancelled contour shift in Jutila Lemma 6

For a zero `rho` of `L(s,chi)`, the apparent Gamma pole at the translation
variable `z=0` is removable.  This module applies the already certified
divided-difference construction to Jutila's entire finite `M` factor and
proves the exact four-side rectangle identity.  No infinite-height limit or
tail estimate is hidden here.
-/

namespace MAPJutilaLemma6FiniteContour

open Complex Real MeasureTheory Set
open MAPAppendixA4Detector MAPMellinDetectorLeaf
open MAPJutilaMEntire MAPJutilaPseudocharacterMExact
open MAPJutilaLemma6ErrorBound

noncomputable section

def jutilaDetectorExtension {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (rho : ℂ)
    (xi : ℕ → ℂ) (D S : Finset ℕ) (X : ℝ) (z : ℂ) : ℂ :=
  Complex.Gamma (z + 1) * shiftedZeroQuotient chi rho z *
    (X : ℂ) ^ z * jutilaMWeightedSumComplex chi xi D S (rho + z)

theorem analyticAt_jutilaDetectorExtension
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (rho : ℂ) (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X : ℝ} (hX : 0 < X) {z : ℂ} (hz : z ∈ contourStrip) :
    AnalyticAt ℂ (jutilaDetectorExtension chi rho xi D S X) z := by
  unfold jutilaDetectorExtension
  have hpow : Differentiable ℂ (fun w : ℂ => (X : ℂ) ^ w) :=
    differentiable_id.const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  have hM : Differentiable ℂ (fun w : ℂ =>
      jutilaMWeightedSumComplex chi xi D S (rho + w)) :=
    (differentiable_jutilaMWeightedSumComplex chi xi hDpos S).comp
      (by fun_prop)
  exact ((((analyticAt_Gamma_add_one_of_mem_contourStrip hz).mul
    (analyticAt_shiftedZeroQuotient chi hchi rho z)).mul
      (hpow.analyticAt z)).mul (hM.analyticAt z))

theorem jutilaDetectorExtension_eq_raw
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {rho z : ℂ}
    (xi : ℕ → ℂ) (D S : Finset ℕ) (X : ℝ)
    (hrho : DirichletCharacter.LFunction chi rho = 0) (hz : z ≠ 0) :
    jutilaDetectorExtension chi rho xi D S X z =
      Complex.Gamma z * DirichletCharacter.LFunction chi (rho + z) *
        (X : ℂ) ^ z * jutilaMWeightedSumComplex chi xi D S (rho + z) := by
  unfold jutilaDetectorExtension
  rw [shiftedZeroQuotient_eq_div chi hrho hz,
    Complex.Gamma_add_one z hz]
  field_simp

/-- Exact finite four-side balance for the Jutila detector. -/
theorem finiteRectangle_jutilaDetector_shift
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (rho : ℂ) (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X a c B : ℝ} (hX : 0 < X) (haStrip : -1 < a)
    (hac : a ≤ c) (hB : 0 ≤ B) :
    (∫ x : ℝ in a..c,
        jutilaDetectorExtension chi rho xi D S X (x - B * I)) -
      (∫ x : ℝ in a..c,
        jutilaDetectorExtension chi rho xi D S X (x + B * I)) +
      I * (∫ u : ℝ in -B..B,
        jutilaDetectorExtension chi rho xi D S X (c + u * I)) -
      I * (∫ u : ℝ in -B..B,
        jutilaDetectorExtension chi rho xi D S X (a + u * I)) = 0 := by
  apply finite_rectangle_balance
  · exact hac
  · exact hB
  · intro z hz
    apply analyticAt_jutilaDetectorExtension chi hchi rho xi hDpos S hX
    change -1 < z.re
    have haz : a ≤ z.re := by
      simpa [min_eq_left hac] using hz.1.1
    exact haStrip.trans_le haz

def lemmaSixZeroPoint (beta t : ℝ) : ℂ :=
  (beta : ℂ) + (t : ℂ) * I

def lemmaSixLeftPoint (beta u : ℝ) : ℂ :=
  (-beta : ℂ) + (u : ℂ) * I

theorem lemmaSixZero_add_leftPoint
    (beta t u : ℝ) :
    lemmaSixZeroPoint beta t + lemmaSixLeftPoint beta u =
      ((t + u : ℝ) : ℂ) * I := by
  unfold lemmaSixZeroPoint lemmaSixLeftPoint
  push_cast
  ring

theorem jutilaMWeightedSumComplex_zero_add_left_eq
    {q : ℕ} (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    (D S : Finset ℕ) (beta t u : ℝ) :
    jutilaMWeightedSumComplex chi xi D S
        (lemmaSixZeroPoint beta t + lemmaSixLeftPoint beta u) =
      jutilaMWeightedSum chi xi D S (t + u) := by
  rw [lemmaSixZero_add_leftPoint]
  unfold jutilaMWeightedSumComplex jutilaMWeightedSum
  apply Finset.sum_congr rfl
  intro r hr
  rw [jutilaMFiniteComplex_mul_I_eq]

/-- The left vertical side is exactly the literal error integrand already
bounded in `JutilaLemma6ErrorBound`. -/
theorem jutilaDetectorExtension_left_eq_errorIntegrand
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    (D S : Finset ℕ) {beta t X u : ℝ}
    (hbeta : 0 < beta)
    (hrho : DirichletCharacter.LFunction chi
      (lemmaSixZeroPoint beta t) = 0) :
    jutilaDetectorExtension chi (lemmaSixZeroPoint beta t)
        xi D S X (lemmaSixLeftPoint beta u) =
      lemmaSixMellinErrorIntegrand chi xi D S beta t X u := by
  have hz : lemmaSixLeftPoint beta u ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [lemmaSixLeftPoint] at hre
    linarith
  rw [jutilaDetectorExtension_eq_raw chi xi D S X hrho hz,
    jutilaMWeightedSumComplex_zero_add_left_eq]
  unfold lemmaSixMellinErrorIntegrand lemmaSixLeftPoint
  have hleft : (-(beta : ℂ) + (u : ℂ) * I) =
      ((-beta : ℝ) + (u : ℂ) * I) := by
    push_cast
    rfl
  have hsum : lemmaSixZeroPoint beta t +
      ((-beta : ℝ) + (u : ℂ) * I) = ((t + u : ℝ) : ℂ) * I := by
    unfold lemmaSixZeroPoint
    push_cast
    ring
  rw [hleft, hsum]

end

end MAPJutilaLemma6FiniteContour

#print axioms MAPJutilaLemma6FiniteContour.finiteRectangle_jutilaDetector_shift
#print axioms MAPJutilaLemma6FiniteContour.jutilaDetectorExtension_left_eq_errorIntegrand
