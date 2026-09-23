import GuthMaynardLemma295HorizontalPointwise
import GuthMaynardLemma295MellinCompactStrip

/-!
# Vanishing horizontal sides in Guth--Maynard Lemma 29.5

The scalar estimate below is the final asymptotic calculation: two extra
orders of Mellin decay beat the exact polynomial degree of the archimedean
multiplier.  The compact-strip Mellin producer is imported and welded below
once available.
-/

namespace GuthMaynardLemma295HorizontalIntegral

open Real Set Filter Topology
open GuthMaynardLemma295ThetaHorizontal
open GuthMaynardLemma295HorizontalPointwise
open GuthMaynardLemma295MellinCompactStrip
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295DualTail
open GuthMaynardLemma295ReflectedFiniteContour

noncomputable section

theorem horizontalMellinOrder_eq (n : ℕ) :
    horizontalMellinOrder n = (2 * n + 5) + 2 := by
  unfold horizontalMellinOrder
  omega

/-- The literal shifted polynomial divided by the chosen Mellin power tends
to zero. -/
theorem tendsto_horizontalThetaMellinRatio_zero (n : ℕ) (g : ℝ) :
    Tendsto (fun B : ℝ =>
      horizontalThetaRadius n (B - g) ^ (2 * n + 5) /
        (1 + |B| ^ horizontalMellinOrder n))
      atTop (𝓝 0) := by
  let d : ℕ := 2 * n + 5
  let k : ℕ := horizontalMellinOrder n
  let c : ℝ := 4 + 4 * n
  let Q : ℝ := 3 ^ d
  have hdk : d < k := by
    dsimp [d, k]
    rw [horizontalMellinOrder_eq]
    omega
  have hmodel : Tendsto (fun B : ℝ => Q * (B ^ d / B ^ k))
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) hdk).const_mul Q
  rw [show (0 : ℝ) = 0 by rfl]
  apply squeeze_zero'
  · filter_upwards with B
    exact div_nonneg (pow_nonneg (by
      unfold horizontalThetaRadius
      positivity) _) (by positivity)
  · filter_upwards [eventually_ge_atTop (max (max 1 |g|) c)] with B hB
    have hB1 : 1 ≤ B := (le_max_left 1 |g|).trans
      ((le_max_left (max 1 |g|) c).trans hB)
    have hB0 : 0 ≤ B := zero_le_one.trans hB1
    have hgB : |g| ≤ B := (le_max_right 1 |g|).trans
      ((le_max_left (max 1 |g|) c).trans hB)
    have hcB : c ≤ B := (le_max_right (max 1 |g|) c).trans hB
    have habsSub : |B - g| ≤ 2 * B := by
      calc
        |B - g| ≤ |B| + |g| := abs_sub B g
        _ = B + |g| := by rw [abs_of_nonneg hB0]
        _ ≤ 2 * B := by linarith
    have hrad : horizontalThetaRadius n (B - g) ≤ 3 * B := by
      dsimp [horizontalThetaRadius, c] at hcB ⊢
      linarith
    have hrad0 : 0 ≤ horizontalThetaRadius n (B - g) := by
      unfold horizontalThetaRadius
      positivity
    have hpow : horizontalThetaRadius n (B - g) ^ d ≤ Q * B ^ d := by
      calc
        horizontalThetaRadius n (B - g) ^ d ≤ (3 * B) ^ d :=
          pow_le_pow_left₀ hrad0 hrad d
        _ = Q * B ^ d := by simp [Q, mul_pow]
    have hden : B ^ k ≤ 1 + |B| ^ k := by
      rw [abs_of_nonneg hB0]
      linarith [pow_nonneg hB0 k]
    have hBkpos : 0 < B ^ k := pow_pos (lt_of_lt_of_le zero_lt_one hB1) _
    have hdenpos : 0 < 1 + |B| ^ k := by positivity
    calc
      horizontalThetaRadius n (B - g) ^ d /
          (1 + |B| ^ k) ≤ (Q * B ^ d) / (1 + |B| ^ k) :=
        div_le_div_of_nonneg_right hpow hdenpos.le
      _ ≤ (Q * B ^ d) / B ^ k :=
        div_le_div_of_nonneg_left
          (mul_nonneg (by positivity) (pow_nonneg hB0 _)) hBkpos hden
      _ = Q * (B ^ d / B ^ k) := by ring
  · exact hmodel

/-- Complete constant on a reflected horizontal edge. -/
def reflectedHorizontalConstant (N : ℝ) (K n : ℕ) : ℝ :=
  1152 * K *
    max (Real.rpow N (deepLeftSigma n)) (Real.rpow N (1 / 2)) *
      uniformStripMellinDecayConstant n (horizontalMellinOrder n) (1 / 2)

theorem reflectedHorizontalConstant_nonneg
    {N : ℝ} (hN : 0 < N) (K n : ℕ) :
    0 ≤ reflectedHorizontalConstant N K n := by
  unfold reflectedHorizontalConstant
  have hmax : 0 ≤ max (Real.rpow N (deepLeftSigma n))
      (Real.rpow N (1 / 2)) :=
    (Real.rpow_nonneg hN.le _).trans (le_max_left _ _)
  have hC := uniformStripMellinDecayConstant_nonneg
    n (horizontalMellinOrder n) (1 / 2)
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hmax) hC

def reflectedHorizontalEnvelope
    (N g : ℝ) (K n : ℕ) (B : ℝ) : ℝ :=
  reflectedHorizontalConstant N K n *
    (horizontalThetaRadius n (B - g) ^ (2 * n + 5) /
      (1 + |B| ^ horizontalMellinOrder n))

/-- Uniform pointwise envelope across the entire reflected horizontal side. -/
theorem norm_lemma295ReflectedFiniteIntegrand_horizontal_uniform_le
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K n : ℕ) {x B : ℝ}
    (hx : x ∈ Set.Icc (deepLeftSigma n) (1 / 2))
    (hheight : 2 ≤ |B - g|) :
    ‖lemma295ReflectedFiniteIntegrand N g K ((x : ℂ) + B * Complex.I)‖ ≤
      reflectedHorizontalEnvelope N g K n B := by
  let s : ℂ := (x : ℂ) + B * Complex.I
  let z : ℂ := s - g * Complex.I
  have hzform : z = (x : ℂ) + (((B - g : ℝ) : ℂ)) * Complex.I := by
    dsimp [z, s]
    apply Complex.ext <;> simp
  have hzre : z.re = x := by simp [z, s]
  have htheta := norm_sourceZetaTheta_horizontal_le n hx hheight
  rw [← hzform] at htheta
  have hprefix := norm_sourceDualPartialNat_le_card K (z := z) (by
    rw [hzre]
    exact hx.2)
  have hscale := norm_positiveScale_horizontal_le_max hN hx.1 hx.2
    (t := B - g)
  rw [← hzform] at hscale
  have hmellinMul :=
    one_add_absPow_mul_norm_mellin_sourceHZero_deepLeft_to_half_le
      n (horizontalMellinOrder n) hx B
  have hden : 0 < 1 + |B| ^ horizontalMellinOrder n := by positivity
  have hmellin : ‖mellin sourceHZero s‖ ≤
      uniformStripMellinDecayConstant n (horizontalMellinOrder n) (1 / 2) /
        (1 + |B| ^ horizontalMellinOrder n) := by
    apply (le_div_iff₀ hden).2
    simpa [s, mul_comm] using hmellinMul
  have hthetaUp : 0 ≤
      1152 * horizontalThetaRadius n (B - g) ^ (2 * n + 5) :=
    (norm_nonneg _).trans htheta
  have hK : 0 ≤ (K : ℝ) := by positivity
  have hscaleUp : 0 ≤ max (Real.rpow N (deepLeftSigma n))
      (Real.rpow N (1 / 2)) := (norm_nonneg _).trans hscale
  have hmellinUp : 0 ≤
      uniformStripMellinDecayConstant n (horizontalMellinOrder n) (1 / 2) /
        (1 + |B| ^ horizontalMellinOrder n) :=
    (norm_nonneg _).trans hmellin
  unfold lemma295ReflectedFiniteIntegrand reflectedHorizontalEnvelope
    reflectedHorizontalConstant
  dsimp only
  repeat' rw [norm_mul]
  calc
    ‖sourceZetaTheta z‖ * ‖sourceDualPartialNat K z‖ *
        ‖(N : ℂ) ^ z‖ * ‖mellin sourceHZero s‖ ≤
      (1152 * horizontalThetaRadius n (B - g) ^ (2 * n + 5)) * K *
        max (Real.rpow N (deepLeftSigma n)) (Real.rpow N (1 / 2)) *
          (uniformStripMellinDecayConstant n (horizontalMellinOrder n) (1 / 2) /
            (1 + |B| ^ horizontalMellinOrder n)) := by
              exact mul_le_mul
                (mul_le_mul
                  (mul_le_mul htheta hprefix (norm_nonneg _) hthetaUp)
                  hscale (norm_nonneg _) (mul_nonneg hthetaUp hK))
                hmellin (norm_nonneg _)
                  (mul_nonneg (mul_nonneg hthetaUp hK) hscaleUp)
    _ = 1152 * ↑K *
        max (Real.rpow N (deepLeftSigma n)) (Real.rpow N (1 / 2 : ℝ)) *
          uniformStripMellinDecayConstant n (horizontalMellinOrder n) (1 / 2) *
            (horizontalThetaRadius n (B - g) ^ (2 * n + 5) /
              (1 + |B| ^ horizontalMellinOrder n)) := by ring

theorem tendsto_reflectedHorizontalEnvelope_zero
    (N g : ℝ) (K n : ℕ) :
    Tendsto (reflectedHorizontalEnvelope N g K n) atTop (𝓝 0) := by
  unfold reflectedHorizontalEnvelope
  simpa only [mul_zero] using!
    (tendsto_horizontalThetaMellinRatio_zero n g).const_mul
      (reflectedHorizontalConstant N K n)

/-- The full upper horizontal edge of the reflected finite rectangle tends to
zero.  Replacing `B` by `-B` gives the lower edge through the same theorem. -/
theorem tendsto_lemma295ReflectedFinite_horizontalIntegral_zero
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K n : ℕ) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in deepLeftSigma n..(1 / 2),
        lemma295ReflectedFiniteIntegrand N g K ((x : ℂ) + B * Complex.I))
      atTop (𝓝 0) := by
  have henv := tendsto_reflectedHorizontalEnvelope_zero N g K n
  have hbound : ∀ᶠ B : ℝ in atTop,
      ‖∫ x : ℝ in deepLeftSigma n..(1 / 2),
          lemma295ReflectedFiniteIntegrand N g K ((x : ℂ) + B * Complex.I)‖ ≤
        reflectedHorizontalEnvelope N g K n B *
          |(1 / 2 : ℝ) - deepLeftSigma n| := by
    filter_upwards [eventually_ge_atTop (|g| + 2)] with B hB
    have hB0 : 0 ≤ B := by linarith [abs_nonneg g]
    have hheight : 2 ≤ |B - g| := by
      rw [abs_of_nonneg (by linarith [le_abs_self g])]
      linarith [le_abs_self g]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc (deepLeftSigma n) (1 / 2) := by
      have hsub := Set.uIoc_subset_uIcc hx
      have hab : deepLeftSigma n ≤ (1 / 2 : ℝ) := by
        unfold deepLeftSigma
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      rw [Set.uIcc_of_le hab] at hsub
      exact hsub
    exact norm_lemma295ReflectedFiniteIntegrand_horizontal_uniform_le
      hN g K n hx' hheight
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  · exact hbound
  · simpa using henv.mul_const |(1 / 2 : ℝ) - deepLeftSigma n|

/-- The lower reflected horizontal edge, parametrized by positive height
`B`, tends to zero as well. -/
theorem tendsto_lemma295ReflectedFinite_lowerHorizontalIntegral_zero
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K n : ℕ) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in deepLeftSigma n..(1 / 2),
        lemma295ReflectedFiniteIntegrand N g K
          ((x : ℂ) + (-B) * Complex.I))
      atTop (𝓝 0) := by
  have henv := tendsto_reflectedHorizontalEnvelope_zero N (-g) K n
  have hbound : ∀ᶠ B : ℝ in atTop,
      ‖∫ x : ℝ in deepLeftSigma n..(1 / 2),
          lemma295ReflectedFiniteIntegrand N g K
            ((x : ℂ) + (-B) * Complex.I)‖ ≤
        reflectedHorizontalEnvelope N (-g) K n B *
          |(1 / 2 : ℝ) - deepLeftSigma n| := by
    filter_upwards [eventually_ge_atTop (|g| + 2)] with B hB
    have hheight : 2 ≤ |-B - g| := by
      rw [show -B - g = -(B + g) by ring, abs_neg]
      have : 0 ≤ B + g := by linarith [neg_le_abs g]
      rw [abs_of_nonneg this]
      linarith [neg_le_abs g]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc (deepLeftSigma n) (1 / 2) := by
      have hsub := Set.uIoc_subset_uIcc hx
      have hab : deepLeftSigma n ≤ (1 / 2 : ℝ) := by
        unfold deepLeftSigma
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      rw [Set.uIcc_of_le hab] at hsub
      exact hsub
    have hp := norm_lemma295ReflectedFiniteIntegrand_horizontal_uniform_le
      hN g K n hx' hheight
    have henvEq : reflectedHorizontalEnvelope N g K n (-B) =
        reflectedHorizontalEnvelope N (-g) K n B := by
      unfold reflectedHorizontalEnvelope horizontalThetaRadius
      rw [abs_neg]
      have habs : |-B - g| = |B - -g| := by
        rw [show -B - g = -(B - -g) by ring, abs_neg]
      rw [habs]
    rw [henvEq] at hp
    simpa using hp
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  · exact hbound
  · simpa using henv.mul_const |(1 / 2 : ℝ) - deepLeftSigma n|

end
end GuthMaynardLemma295HorizontalIntegral

#print axioms GuthMaynardLemma295HorizontalIntegral.tendsto_horizontalThetaMellinRatio_zero
#print axioms GuthMaynardLemma295HorizontalIntegral.norm_lemma295ReflectedFiniteIntegrand_horizontal_uniform_le
#print axioms GuthMaynardLemma295HorizontalIntegral.tendsto_lemma295ReflectedFinite_horizontalIntegral_zero
#print axioms GuthMaynardLemma295HorizontalIntegral.tendsto_lemma295ReflectedFinite_lowerHorizontalIntegral_zero
