import JutilaP53SourceHorizontalDecay
import JutilaP53SourceLineIntegral

namespace MAPJutilaP53SourceInfiniteShift
open Complex Real MeasureTheory Set Filter Topology
open MAPJutilaP53TwoScaleContour MAPJutilaP53InfiniteShift
open MAPJutilaP53SourceHorizontalDecay MAPJutilaP53FiniteShift
noncomputable section

/-- Exact infinite-height displacement from `Re w=1` to `Re w=-1+epsilon` for
the nonprincipal pair character.  The range on `Re s` is precisely the
small collar range used on p.53. -/
theorem p53TwoScale_right_eq_sourceLine
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) {U V epsilon : ℝ} (hU : 0 < U) (hV : 0 < V)
    (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1 / 8)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 2 * epsilon) :
    (∫ t : ℝ, p53TwoScaleContourIntegrand chi s U V
        (((1 : ℝ) : ℂ) + t * I)) =
      ∫ t : ℝ, p53TwoScaleContourIntegrand chi s U V
        (((-1 + epsilon : ℝ) : ℂ) + t * I) := by
  let R : ℝ → ℂ := fun B => ∫ t : ℝ in -B..B,
    p53TwoScaleContourIntegrand chi s U V (((1 : ℝ) : ℂ) + t * I)
  let L : ℝ → ℂ := fun B => ∫ t : ℝ in -B..B,
    p53TwoScaleContourIntegrand chi s U V
      (((-1 + epsilon : ℝ) : ℂ) + t * I)
  let Hminus : ℝ → ℂ := fun B => ∫ x : ℝ in (-1 + epsilon)..1,
    p53TwoScaleContourIntegrand chi s U V ((x : ℂ) - B * I)
  let Hplus : ℝ → ℂ := fun B => ∫ x : ℝ in (-1 + epsilon)..1,
    p53TwoScaleContourIntegrand chi s U V ((x : ℂ) + B * I)
  have hrightInt := integrable_p53TwoScaleContourIntegrand_rightOne
    chi hsLo hU hV
  obtain ⟨K, hK, hsource⟩ :=
    MAPJutilaP53SourceLineIntegral.exists_sourceLine_integrable_and_norm_integral_le heps hepsHi
  have hleftInt := (hsource q chi hchi s U V hU hV hsLo hsHi).1
  have hR : Tendsto R atTop
      (𝓝 (∫ t : ℝ, p53TwoScaleContourIntegrand chi s U V
        (((1 : ℝ) : ℂ) + t * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral hrightInt
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hL : Tendsto L atTop
      (𝓝 (∫ t : ℝ, p53TwoScaleContourIntegrand chi s U V
        (((-1 + epsilon : ℝ) : ℂ) + t * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral hleftInt
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hminus : Tendsto Hminus atTop (𝓝 0) := by
    have h := tendsto_p53SourceFullHorizontalIntegral_zero
      chi hchi s hU hV heps hepsHi hsLo hsHi (ε := (-1 : ℝ)) (by norm_num)
    simpa [Hminus, sub_eq_add_neg, neg_mul] using h
  have hplus : Tendsto Hplus atTop (𝓝 0) := by
    simpa [Hplus] using tendsto_p53SourceFullHorizontalIntegral_zero
      chi hchi s hU hV heps hepsHi hsLo hsHi (ε := (1 : ℝ)) (by norm_num)
  have hcombo : Tendsto (fun B => L B + I * (Hminus B - Hplus B)) atTop
      (𝓝 ((∫ t : ℝ, p53TwoScaleContourIntegrand chi s U V
        (((-1 + epsilon : ℝ) : ℂ) + t * I)) + I * (0 - 0))) :=
    hL.add (tendsto_const_nhds.mul (hminus.sub hplus))
  have heq : ∀ᶠ B : ℝ in atTop,
      R B = L B + I * (Hminus B - Hplus B) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    simpa [R, L, Hminus, Hplus, sub_eq_add_neg, Complex.ofReal_sub, Complex.ofReal_add, add_comm, add_left_comm, add_assoc] using
      p53TwoScale_right_eq_left_add_horizontals
        chi hchi s hU hV (a := 1 - epsilon) (T := B)
        (by linarith) (by linarith) hB
  have hR' : Tendsto R atTop
      (𝓝 ((∫ t : ℝ, p53TwoScaleContourIntegrand chi s U V
        (((-1 + epsilon : ℝ) : ℂ) + t * I)) + I * (0 - 0))) :=
    hcombo.congr' (Filter.EventuallyEq.symm heq)
  have := tendsto_nhds_unique hR hR'
  simpa using this

end
end MAPJutilaP53SourceInfiniteShift
#print axioms MAPJutilaP53SourceInfiniteShift.p53TwoScale_right_eq_sourceLine
