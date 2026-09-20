import JutilaP53PrincipalSourceHorizontalDecay
import JutilaP53PrincipalSourceLineIntegral
import JutilaP53InfiniteShift

/-!
# Infinite principal p.53 contour displacement

This passes the exact finite-pole rectangle to infinite height after the
principal horizontal and vertical tails have been certified.
-/

namespace MAPJutilaP53PrincipalSourceInfiniteShift

open Complex Real MeasureTheory Set Filter Topology
open MAPJutilaP53TwoScaleContour
open MAPJutilaP53InfiniteShift
open MAPJutilaP53PrincipalFinitePole
open MAPJutilaP53PrincipalSourceHorizontalDecay

noncomputable section

/-- The full principal line displacement with the exact crossed residue. -/
theorem p53TwoScale_principal_right_eq_source_add_residue_of_integrable
    (q : ℕ) [NeZero q] (s : ℂ) {U V epsilon : ℝ}
    (hU : 0 < U) (hV : 0 < V)
    (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1 / 8)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 2 * epsilon)
    (hleftInt : Integrable (fun t : ℝ => p53TwoScaleContourIntegrand
      (1 : DirichletCharacter ℂ q) s U V
      (((-1 + epsilon : ℝ) : ℂ) + t * I))) :
    (∫ t : ℝ, p53TwoScaleContourIntegrand
        (1 : DirichletCharacter ℂ q) s U V
        (((1 : ℝ) : ℂ) + t * I)) =
      (∫ t : ℝ, p53TwoScaleContourIntegrand
        (1 : DirichletCharacter ℂ q) s U V
        (((-1 + epsilon : ℝ) : ℂ) + t * I)) +
      (2 * Real.pi : ℂ) * p53PrincipalResidue q s U V := by
  let R : ℝ → ℂ := fun B => ∫ t : ℝ in -B..B,
    p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
      (((1 : ℝ) : ℂ) + t * I)
  let L : ℝ → ℂ := fun B => ∫ t : ℝ in -B..B,
    p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
      (((-1 + epsilon : ℝ) : ℂ) + t * I)
  let Hminus : ℝ → ℂ := fun B => ∫ x : ℝ in (-1 + epsilon)..1,
    p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
      ((x : ℂ) - B * I)
  let Hplus : ℝ → ℂ := fun B => ∫ x : ℝ in (-1 + epsilon)..1,
    p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
      ((x : ℂ) + B * I)
  have hrightInt := integrable_p53TwoScaleContourIntegrand_rightOne
    (1 : DirichletCharacter ℂ q) hsLo hU hV
  have hR : Tendsto R atTop
      (𝓝 (∫ t : ℝ, p53TwoScaleContourIntegrand
        (1 : DirichletCharacter ℂ q) s U V
        (((1 : ℝ) : ℂ) + t * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral hrightInt
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hL : Tendsto L atTop
      (𝓝 (∫ t : ℝ, p53TwoScaleContourIntegrand
        (1 : DirichletCharacter ℂ q) s U V
        (((-1 + epsilon : ℝ) : ℂ) + t * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral hleftInt
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hminus : Tendsto Hminus atTop (𝓝 0) := by
    have h := tendsto_p53PrincipalSourceFullHorizontalIntegral_zero q s hU hV
      heps hepsHi hsLo (by linarith : s.re ≤ 1 / 4) (epsilon := (-1 : ℝ)) (by norm_num)
    simpa [Hminus, sub_eq_add_neg, neg_mul] using h
  have hplus : Tendsto Hplus atTop (𝓝 0) := by
    simpa [Hplus] using tendsto_p53PrincipalSourceFullHorizontalIntegral_zero q s hU hV
      heps hepsHi hsLo (by linarith : s.re ≤ 1 / 4) (epsilon := (1 : ℝ)) (by norm_num)
  let Z : ℂ := (2 * Real.pi : ℂ) * p53PrincipalResidue q s U V
  have hcombo : Tendsto
      (fun B => L B + I * (Hminus B - Hplus B) + Z) atTop
      (𝓝 ((∫ t : ℝ, p53TwoScaleContourIntegrand
        (1 : DirichletCharacter ℂ q) s U V
        (((-1 + epsilon : ℝ) : ℂ) + t * I)) + I * (0 - 0) + Z)) :=
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
      q hU hV (by linarith) (r := (1 / 8 : ℝ)) (a := -1 + epsilon)
      (b := 1) (u := -B) (v := B) (by norm_num) (by linarith)
      (by simp; linarith) (by simp; linarith) hbottom htop
    simpa [R, L, Hminus, Hplus, Z, sub_eq_add_neg] using hfinite
  have hR' : Tendsto R atTop
      (𝓝 ((∫ t : ℝ, p53TwoScaleContourIntegrand
        (1 : DirichletCharacter ℂ q) s U V
        (((-1 + epsilon : ℝ) : ℂ) + t * I)) + I * (0 - 0) + Z)) :=
    hcombo.congr' (Filter.EventuallyEq.symm heq)
  have hunique := tendsto_nhds_unique hR hR'
  simpa [Z] using hunique

/-- Actual principal source-line displacement, with integrability supplied
by the proved zeta convexity and source-line majorant. -/
theorem p53TwoScale_principal_right_eq_source_add_residue
    (q : ℕ) [NeZero q] (s : ℂ) {U V epsilon : ℝ}
    (hU : 0 < U) (hV : 0 < V)
    (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1 / 8)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 2 * epsilon) :
    (∫ t : ℝ, p53TwoScaleContourIntegrand
      (1 : DirichletCharacter ℂ q) s U V (((1 : ℝ) : ℂ) + t * I)) =
      (∫ t : ℝ, p53TwoScaleContourIntegrand
        (1 : DirichletCharacter ℂ q) s U V
        (((-1 + epsilon : ℝ) : ℂ) + t * I)) +
      (2 * Real.pi : ℂ) * p53PrincipalResidue q s U V := by
  obtain ⟨K, hK, hsource⟩ :=
    MAPJutilaP53PrincipalSourceLineIntegral.exists_principal_sourceLine_integrable_and_norm_integral_le
      heps hepsHi
  exact p53TwoScale_principal_right_eq_source_add_residue_of_integrable
    q s hU hV heps hepsHi hsLo hsHi (hsource q s U V hU hV hsLo hsHi).1

end
end MAPJutilaP53PrincipalSourceInfiniteShift

#print axioms MAPJutilaP53PrincipalSourceInfiniteShift.p53TwoScale_principal_right_eq_source_add_residue_of_integrable

#print axioms MAPJutilaP53PrincipalSourceInfiniteShift.p53TwoScale_principal_right_eq_source_add_residue
