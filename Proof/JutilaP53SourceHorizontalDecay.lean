import JutilaP53SourceLineEstimate
import JutilaP53InfiniteShift

namespace MAPJutilaP53SourceHorizontalDecay
open Complex Real MeasureTheory Set Filter Topology
open MAPJutilaP53TwoScaleContour MAPJutilaP53LeftLineEstimate
open MAPJutilaP53SourceLineEstimate MAPJutilaP53InfiniteShift
open MAPPrimitiveLFixedStrip
noncomputable section

/-- Literal pointwise envelope on the shifted p.53 line `Re w = x`.
The hypotheses are exactly the Gamma strip and L-function strip conditions. -/
theorem norm_p53TwoScaleContourIntegrand_deepHorizontal_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) {U V a b x t epsilon : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hax : a ≤ x) (hxb : x ≤ b)
    (heps : 0 < epsilon) (haGamma : epsilon ≤ 1 + x) (hbGamma : 1 + x ≤ 1 / 2)
    (hLLo : -1 ≤ 1 + s.re + x) (hLHi : 1 + s.re + x ≤ 2)
    (ht : 1 ≤ |t|) :
    ‖p53TwoScaleContourIntegrand chi s U V ((x : ℂ) + t * I)‖ ≤
      (2400 / epsilon) * (q : ℝ) ^ 2 * (1 + |t|) *
        (5 + |s.im| + |t|) ^ 2 *
          Real.exp (-(Real.pi / 2) * |t|) *
            p53CpowEndpointBound U V a b := by
  let z : ℂ := 1 + s + ((x : ℂ) + t * I)
  have hzRe : z.re = 1 + s.re + x := by simp [z]
  have hzIm : z.im = s.im + t := by simp [z]
  have hL0 := PLInteriorGrowth.norm_LFunction_fixedStrip_le chi hchi
    (by rw [hzRe]; exact hLLo) (by rw [hzRe]; exact hLHi)
  have hzNorm : ‖z + 3‖ ≤ 5 + |s.im| + |t| := by
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |4 + s.re + x| + |s.im + t| := by simp [z]; ring
      _ ≤ 5 + (|s.im| + |t|) := by
        have hre0 : 0 ≤ 4 + s.re + x := by linarith
        rw [abs_of_nonneg hre0]
        exact add_le_add (by linarith [hLHi]) (abs_add_le _ _)
      _ = 5 + |s.im| + |t| := by ring
  have hL : ‖DirichletCharacter.LFunction chi z‖ ≤
      200 * (q : ℝ) ^ 2 * (5 + |s.im| + |t|) ^ 2 :=
    hL0.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hzNorm 2) (by positivity))
  have hGammaPoint : 1 + ((x : ℂ) + t * I) =
      ((1 + x : ℝ) : ℂ) + (t : ℂ) * I := by push_cast; ring
  have hGammaRaw := norm_Gamma_sourceStrip_le (t := t)
    (heps.trans_le haGamma) hbGamma
  have hGamma : ‖Complex.Gamma (1 + ((x : ℂ) + t * I))‖ ≤
      (12 / epsilon) * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
    rw [hGammaPoint]
    exact hGammaRaw.trans (by gcongr)
  have hQ := norm_p53ScaleRemovableQuotient_horizontal_le
    hU hV hax hxb ht
  have hQ0 := p53CpowEndpointBound_nonneg hU hV a b
  have hL' : ‖DirichletCharacter.LFunction chi
      (1 + s + ((x : ℂ) + t * I))‖ ≤
      200 * (q : ℝ) ^ 2 * (5 + |s.im| + |t|) ^ 2 := by
    simpa only [z] using hL
  unfold p53TwoScaleContourIntegrand
  simp only [norm_mul]
  calc
    ‖Complex.Gamma (((x : ℂ) + t * I) + 1)‖ *
          ‖p53ScaleRemovableQuotient U V ((x : ℂ) + t * I)‖ *
          ‖DirichletCharacter.LFunction chi z‖ ≤
        ((12 / epsilon) * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) *
          p53CpowEndpointBound U V a b *
            (200 * (q : ℝ) ^ 2 * (5 + |s.im| + |t|) ^ 2) := by
      gcongr
      · simpa only [add_comm] using hGamma
    _ = _ := by ring

/-- Either oriented horizontal edge tends to zero.  The sign parameter is
restricted to `±1`, exactly the two edges used by the finite rectangle. -/
theorem tendsto_p53DeepHorizontalIntegral_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) {U V a b ε epsilon : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hab : a ≤ b) (heps : 0 < epsilon) (haGamma : epsilon ≤ 1 + a)
    (hbGamma : 1 + b ≤ 1 / 2)
    (hLLo : -1 ≤ 1 + s.re + a) (hLHi : 1 + s.re + b ≤ 2)
    (hε : |ε| = 1) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in a..b,
        p53TwoScaleContourIntegrand chi s U V ((x : ℂ) + (ε * B) * I))
      atTop (𝓝 0) := by
  have henv := tendsto_p53HorizontalEnvelope_zero q s hU hV a b
  have hbound : ∀ᶠ B : ℝ in atTop,
      ‖∫ x : ℝ in a..b,
          p53TwoScaleContourIntegrand chi s U V ((x : ℂ) + (ε * B) * I)‖ ≤
        epsilon⁻¹ * p53HorizontalEnvelope q s U V a b B * |b - a| := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      have := Set.uIoc_subset_uIcc hx
      simpa [Set.uIcc_of_le hab] using this
    have hB0 : 0 ≤ B := le_trans (by norm_num) hB
    have habs : 1 ≤ |ε * B| := by
      rw [abs_mul, hε, one_mul, abs_of_nonneg hB0]
      exact hB
    have haxGamma : epsilon ≤ 1 + x := by linarith [hx'.1]
    have hxbGamma : 1 + x ≤ 1 / 2 := by linarith [hx'.2]
    have hxLLo : -1 ≤ 1 + s.re + x := by
      calc
        -1 ≤ 1 + s.re + a := hLLo
        _ ≤ 1 + s.re + x := by
          convert add_le_add_left hx'.1 (1 + s.re) using 1 <;> ring
    have hxLHi : 1 + s.re + x ≤ 2 := by
      calc
        1 + s.re + x ≤ 1 + s.re + b := by
          convert add_le_add_left hx'.2 (1 + s.re) using 1 <;> ring
        _ ≤ 2 := hLHi
    simpa [p53HorizontalEnvelope, abs_mul, hε, abs_of_nonneg hB0,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      norm_p53TwoScaleContourIntegrand_deepHorizontal_le chi hchi s hU hV
        hx'.1 hx'.2 heps haxGamma hxbGamma hxLLo hxLHi habs
  have henvMul : Tendsto (fun B : ℝ =>
      epsilon⁻¹ * p53HorizontalEnvelope q s U V a b B * |b - a|) atTop (𝓝 0) := by
    simpa using (henv.const_mul epsilon⁻¹).mul_const |b - a|
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  · exact hbound
  · exact henvMul


/-- Both horizontal edges of the literal source rectangle tend to zero. -/
theorem tendsto_p53SourceFullHorizontalIntegral_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) {U V epsilon ε : ℝ} (hU : 0 < U) (hV : 0 < V)
    (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1 / 8)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 2 * epsilon) (hε : |ε| = 1) :
    Tendsto (fun B : ℝ => ∫ x : ℝ in (-1 + epsilon)..1,
      p53TwoScaleContourIntegrand chi s U V ((x : ℂ) + (ε * B) * I))
      atTop (𝓝 0) := by
  have hdeep := tendsto_p53DeepHorizontalIntegral_zero chi hchi s hU hV
    (a := -1 + epsilon) (b := -(1 / 2)) (epsilon := epsilon)
    (by linarith) heps (by linarith) (by norm_num) (by linarith) (by linarith) hε
  have hhigh := tendsto_p53FullHorizontalIntegral_zero chi hchi s hU hV hsLo
    (by linarith : s.re ≤ 1 / 2) hε
  have hsplit : ∀ B : ℝ,
      (∫ x : ℝ in (-1 + epsilon)..1,
        p53TwoScaleContourIntegrand chi s U V ((x : ℂ) + (ε * B) * I)) =
      (∫ x : ℝ in (-1 + epsilon)..(-(1 / 2)),
        p53TwoScaleContourIntegrand chi s U V ((x : ℂ) + (ε * B) * I)) +
      (∫ x : ℝ in (-(1 / 2))..1,
        p53TwoScaleContourIntegrand chi s U V ((x : ℂ) + (ε * B) * I)) := by
    intro B
    have hcont : ContinuousOn
        (fun x : ℝ => p53TwoScaleContourIntegrand chi s U V ((x : ℂ) + (ε * B) * I))
        (Set.uIcc (-1 + epsilon) 1) := by
      intro x hx
      have hx' : x ∈ Set.Icc (-1 + epsilon) 1 := by
        simpa [Set.uIcc_of_le (show -1 + epsilon ≤ 1 by linarith)] using hx
      have houter := (differentiableAt_p53TwoScaleContourIntegrand_nonprincipal
        hchi s hU hV ((x : ℂ) + (ε * B) * I) (by simp; linarith [hx'.1])).continuousAt
      exact (houter.comp (f := fun y : ℝ => ((y : ℂ) + (ε * B) * I))
        (by fun_prop : ContinuousAt (fun y : ℝ => ((y : ℂ) + (ε * B) * I)) x)).continuousWithinAt
    have hall := hcont.intervalIntegrable (μ := volume)
    have hmid : (-(1 / 2) : ℝ) ∈ Set.uIcc (-1 + epsilon) 1 := by
      rw [Set.uIcc_of_le (by linarith)]
      constructor <;> linarith
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hall.mono_set (Set.uIcc_subset_uIcc_left hmid))
      (hall.mono_set (Set.uIcc_subset_uIcc_right hmid))).symm
  have hsum := hdeep.add hhigh
  simpa only [add_zero, ← hsplit] using hsum

end
end MAPJutilaP53SourceHorizontalDecay
#print axioms MAPJutilaP53SourceHorizontalDecay.norm_p53TwoScaleContourIntegrand_deepHorizontal_le

#print axioms MAPJutilaP53SourceHorizontalDecay.tendsto_p53DeepHorizontalIntegral_zero

#print axioms MAPJutilaP53SourceHorizontalDecay.tendsto_p53SourceFullHorizontalIntegral_zero
