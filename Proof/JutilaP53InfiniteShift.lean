import JutilaP53LeftLineEstimate
import JutilaP53MellinContourWeld

/-!
# Infinite nonprincipal p.53 contour displacement

The finite rectangle, full horizontal decay, and both vertical integrability
statements are assembled here.  This is the literal infinite-height contour
identity used before the same-character residue aggregation.
-/

namespace MAPJutilaP53InfiniteShift

open Complex Real MeasureTheory Set Filter Topology
open MAPJutilaP53TwoScaleContour
open MAPJutilaP53InnerMellinRightLine
open MAPJutilaP53FiniteShift
open MAPJutilaP53LeftLineEstimate

noncomputable section

/-- Absolute integrability of the movable right contour, inherited from the
two separately certified one-scale Mellin integrals. -/
theorem integrable_p53TwoScaleContourIntegrand_rightOne
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 ≤ s.re) {U V : ℝ}
    (hU : 0 < U) (hV : 0 < V) :
    Integrable (fun t : ℝ =>
      p53TwoScaleContourIntegrand chi s U V
        (((1 : ℝ) : ℂ) + t * I)) := by
  have hUintegrable := integrable_p53RightOneScaleIntegrand chi hs hU
  have hVintegrable := integrable_p53RightOneScaleIntegrand chi hs hV
  have hdiff : Integrable (fun t : ℝ =>
      p53RightOneScaleIntegrand chi s U t -
        p53RightOneScaleIntegrand chi s V t) :=
    hUintegrable.sub hVintegrable
  apply hdiff.congr
  filter_upwards [] with t
  have hw : (((1 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  rw [p53TwoScaleContourIntegrand_eq_raw chi s U V hw]
  unfold p53RightOneScaleIntegrand p53ScaleDifference
  ring

/-- Exact infinite-height displacement from `Re w=1` to `Re w=-1/2` for
the nonprincipal pair character.  The range on `Re s` is precisely the
small collar range used on p.53. -/
theorem p53TwoScale_right_eq_leftHalf
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 2) :
    (∫ t : ℝ, p53TwoScaleContourIntegrand chi s U V
        (((1 : ℝ) : ℂ) + t * I)) =
      ∫ t : ℝ, p53TwoScaleContourIntegrand chi s U V
        (((-(1 / 2 : ℝ)) : ℂ) + t * I) := by
  let R : ℝ → ℂ := fun B => ∫ t : ℝ in -B..B,
    p53TwoScaleContourIntegrand chi s U V (((1 : ℝ) : ℂ) + t * I)
  let L : ℝ → ℂ := fun B => ∫ t : ℝ in -B..B,
    p53TwoScaleContourIntegrand chi s U V
      (((-(1 / 2 : ℝ)) : ℂ) + t * I)
  let Hminus : ℝ → ℂ := fun B => ∫ x : ℝ in -(1 / 2)..1,
    p53TwoScaleContourIntegrand chi s U V ((x : ℂ) - B * I)
  let Hplus : ℝ → ℂ := fun B => ∫ x : ℝ in -(1 / 2)..1,
    p53TwoScaleContourIntegrand chi s U V ((x : ℂ) + B * I)
  have hrightInt := integrable_p53TwoScaleContourIntegrand_rightOne
    chi hsLo hU hV
  have hleftInt := integrable_p53TwoScaleContourIntegrand_leftHalf
    chi hchi s hU hV (by linarith) (by linarith)
  have hR : Tendsto R atTop
      (𝓝 (∫ t : ℝ, p53TwoScaleContourIntegrand chi s U V
        (((1 : ℝ) : ℂ) + t * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral hrightInt
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hL : Tendsto L atTop
      (𝓝 (∫ t : ℝ, p53TwoScaleContourIntegrand chi s U V
        (((-(1 / 2 : ℝ)) : ℂ) + t * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral hleftInt
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hminus : Tendsto Hminus atTop (𝓝 0) := by
    have h := tendsto_p53FullHorizontalIntegral_zero
      chi hchi s hU hV hsLo hsHi (ε := (-1 : ℝ)) (by norm_num)
    simpa [Hminus, sub_eq_add_neg, neg_mul] using h
  have hplus : Tendsto Hplus atTop (𝓝 0) := by
    simpa [Hplus] using tendsto_p53FullHorizontalIntegral_zero
      chi hchi s hU hV hsLo hsHi (ε := (1 : ℝ)) (by norm_num)
  have hcombo : Tendsto (fun B => L B + I * (Hminus B - Hplus B)) atTop
      (𝓝 ((∫ t : ℝ, p53TwoScaleContourIntegrand chi s U V
        (((-(1 / 2 : ℝ)) : ℂ) + t * I)) + I * (0 - 0))) :=
    hL.add (tendsto_const_nhds.mul (hminus.sub hplus))
  have heq : ∀ᶠ B : ℝ in atTop,
      R B = L B + I * (Hminus B - Hplus B) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    simpa [R, L, Hminus, Hplus, sub_eq_add_neg] using
      p53TwoScale_right_eq_left_add_horizontals
        chi hchi s hU hV (a := (1 / 2 : ℝ)) (T := B)
        (by norm_num) (by norm_num) hB
  have hR' : Tendsto R atTop
      (𝓝 ((∫ t : ℝ, p53TwoScaleContourIntegrand chi s U V
        (((-(1 / 2 : ℝ)) : ℂ) + t * I)) + I * (0 - 0))) :=
    hcombo.congr' (Filter.EventuallyEq.symm heq)
  have := tendsto_nhds_unique hR hR'
  simpa using this

end

end MAPJutilaP53InfiniteShift

#print axioms MAPJutilaP53InfiniteShift.integrable_p53TwoScaleContourIntegrand_rightOne
#print axioms MAPJutilaP53InfiniteShift.p53TwoScale_right_eq_leftHalf
