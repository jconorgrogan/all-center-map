import JutilaP53PrincipalLeftLineEstimate
import JutilaP53InfiniteShift

/-!
# Infinite principal p.53 contour displacement

This passes the exact finite-pole rectangle to infinite height after the
principal horizontal and vertical tails have been certified.
-/

namespace MAPJutilaP53PrincipalInfiniteShift

open Complex Real MeasureTheory Set Filter Topology
open MAPJutilaP53TwoScaleContour
open MAPJutilaP53InfiniteShift
open MAPJutilaP53PrincipalFinitePole
open MAPJutilaP53PrincipalLeftLineEstimate

noncomputable section

/-- The full principal line displacement with the exact crossed residue. -/
theorem p53TwoScale_principal_right_eq_leftHalf_add_residue
    (q : ℕ) [NeZero q] (s : ℂ) {U V : ℝ}
    (hU : 0 < U) (hV : 0 < V)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 4) :
    (∫ t : ℝ, p53TwoScaleContourIntegrand
        (1 : DirichletCharacter ℂ q) s U V
        (((1 : ℝ) : ℂ) + t * I)) =
      (∫ t : ℝ, p53TwoScaleContourIntegrand
        (1 : DirichletCharacter ℂ q) s U V
        (((-(1 / 2 : ℝ)) : ℂ) + t * I)) +
      (2 * Real.pi : ℂ) * p53PrincipalResidue q s U V := by
  let R : ℝ → ℂ := fun B => ∫ t : ℝ in -B..B,
    p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
      (((1 : ℝ) : ℂ) + t * I)
  let L : ℝ → ℂ := fun B => ∫ t : ℝ in -B..B,
    p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
      (((-(1 / 2 : ℝ)) : ℂ) + t * I)
  let Hminus : ℝ → ℂ := fun B => ∫ x : ℝ in -(1 / 2)..1,
    p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
      ((x : ℂ) - B * I)
  let Hplus : ℝ → ℂ := fun B => ∫ x : ℝ in -(1 / 2)..1,
    p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
      ((x : ℂ) + B * I)
  have hrightInt := integrable_p53TwoScaleContourIntegrand_rightOne
    (1 : DirichletCharacter ℂ q) hsLo hU hV
  have hleftInt := integrable_p53PrincipalIntegrand_leftHalf q s hU hV hsLo hsHi
  have hR : Tendsto R atTop
      (𝓝 (∫ t : ℝ, p53TwoScaleContourIntegrand
        (1 : DirichletCharacter ℂ q) s U V
        (((1 : ℝ) : ℂ) + t * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral hrightInt
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hL : Tendsto L atTop
      (𝓝 (∫ t : ℝ, p53TwoScaleContourIntegrand
        (1 : DirichletCharacter ℂ q) s U V
        (((-(1 / 2 : ℝ)) : ℂ) + t * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral hleftInt
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hminus : Tendsto Hminus atTop (𝓝 0) := by
    have h := tendsto_p53PrincipalFullHorizontalIntegral_zero q s hU hV
      hsLo hsHi (epsilon := (-1 : ℝ)) (by norm_num)
    simpa [Hminus, sub_eq_add_neg, neg_mul] using h
  have hplus : Tendsto Hplus atTop (𝓝 0) := by
    simpa [Hplus] using tendsto_p53PrincipalFullHorizontalIntegral_zero q s hU hV
      hsLo hsHi (epsilon := (1 : ℝ)) (by norm_num)
  let Z : ℂ := (2 * Real.pi : ℂ) * p53PrincipalResidue q s U V
  have hcombo : Tendsto
      (fun B => L B + I * (Hminus B - Hplus B) + Z) atTop
      (𝓝 ((∫ t : ℝ, p53TwoScaleContourIntegrand
        (1 : DirichletCharacter ℂ q) s U V
        (((-(1 / 2 : ℝ)) : ℂ) + t * I)) + I * (0 - 0) + Z)) :=
    (hL.add (tendsto_const_nhds.mul (hminus.sub hplus))).add tendsto_const_nhds
  have heq : ∀ᶠ B : ℝ in atTop,
      R B = L B + I * (Hminus B - Hplus B) + Z := by
    filter_upwards [eventually_ge_atTop (|s.im| + 1)] with B hB
    have hbottom : -B < (-s).im - (1 / 8 : ℝ) := by
      simp only [neg_im]
      have := le_abs_self s.im
      linarith
    have htop : (-s).im + (1 / 8 : ℝ) < B := by
      simp only [neg_im]
      have := neg_le_abs s.im
      linarith
    have hfinite := p53Principal_right_eq_left_add_horizontals_add_residue
      q hU hV (by linarith) (r := (1 / 8 : ℝ)) (a := -(1 / 2))
      (b := 1) (u := -B) (v := B) (by norm_num) (by norm_num)
      (by simp; linarith) (by simp; linarith) hbottom htop
    simpa [R, L, Hminus, Hplus, Z, sub_eq_add_neg] using hfinite
  have hR' : Tendsto R atTop
      (𝓝 ((∫ t : ℝ, p53TwoScaleContourIntegrand
        (1 : DirichletCharacter ℂ q) s U V
        (((-(1 / 2 : ℝ)) : ℂ) + t * I)) + I * (0 - 0) + Z)) :=
    hcombo.congr' (Filter.EventuallyEq.symm heq)
  have hunique := tendsto_nhds_unique hR hR'
  simpa [Z] using hunique

end
end MAPJutilaP53PrincipalInfiniteShift

#print axioms MAPJutilaP53PrincipalInfiniteShift.p53TwoScale_principal_right_eq_leftHalf_add_residue
