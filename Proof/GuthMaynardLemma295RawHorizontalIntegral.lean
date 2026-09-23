import GuthMaynardLemma295RawZetaHorizontal
import GuthMaynardLemma295MellinCompactStrip

/-!
# Vanishing horizontal sides of the raw Lemma 29.5 rectangle

The first contour is moved from `Re s = 2` to the certified deep-left line.
This file supplies the two horizontal-edge limits.  The zeta factor is
controlled uniformly by the functional equation / regularized compact-strip
bound, while two additional Mellin orders absorb its polynomial growth.
-/

namespace GuthMaynardLemma295RawHorizontalIntegral

open Complex Real Set Filter Topology
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295DualTail
open GuthMaynardLemma295FiniteContour
open GuthMaynardLemma295HorizontalPointwise
open GuthMaynardLemma295MellinCompactStrip
open GuthMaynardLemma295RawZetaHorizontal

noncomputable section

def rawHorizontalMellinOrder (n : ℕ) : ℕ :=
  rawZetaHorizontalDegree n + 2

theorem rawHorizontalMellinOrder_eq (n : ℕ) :
    rawHorizontalMellinOrder n = (2 * n + 6) + 2 := by
  simp [rawHorizontalMellinOrder, rawZetaHorizontalDegree]

/-- The literal shifted zeta polynomial divided by the selected compact-strip
Mellin power tends to zero. -/
theorem tendsto_rawZetaMellinRatio_zero (n : ℕ) (g : ℝ) :
    Tendsto (fun B : ℝ =>
      rawZetaHorizontalRadius n (B - g) ^ rawZetaHorizontalDegree n /
        (1 + |B| ^ rawHorizontalMellinOrder n))
      atTop (𝓝 0) := by
  let d : ℕ := rawZetaHorizontalDegree n
  let k : ℕ := rawHorizontalMellinOrder n
  let c : ℝ := 6 + 4 * n
  let Q : ℝ := 3 ^ d
  have hdk : d < k := by
    dsimp [d, k, rawHorizontalMellinOrder]
    omega
  have hmodel : Tendsto (fun B : ℝ => Q * (B ^ d / B ^ k))
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) hdk).const_mul Q
  apply squeeze_zero'
  · filter_upwards with B
    exact div_nonneg (pow_nonneg (by
      unfold rawZetaHorizontalRadius
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
    have hrad : rawZetaHorizontalRadius n (B - g) ≤ 3 * B := by
      dsimp [rawZetaHorizontalRadius, c] at hcB ⊢
      linarith
    have hrad0 : 0 ≤ rawZetaHorizontalRadius n (B - g) := by
      unfold rawZetaHorizontalRadius
      positivity
    have hpow : rawZetaHorizontalRadius n (B - g) ^ d ≤ Q * B ^ d := by
      calc
        rawZetaHorizontalRadius n (B - g) ^ d ≤ (3 * B) ^ d :=
          pow_le_pow_left₀ hrad0 hrad d
        _ = Q * B ^ d := by simp [Q, mul_pow]
    have hden : B ^ k ≤ 1 + |B| ^ k := by
      rw [abs_of_nonneg hB0]
      linarith [pow_nonneg hB0 k]
    have hBkpos : 0 < B ^ k := pow_pos (lt_of_lt_of_le zero_lt_one hB1) _
    have hdenpos : 0 < 1 + |B| ^ k := by positivity
    calc
      rawZetaHorizontalRadius n (B - g) ^ d /
          (1 + |B| ^ k) ≤ (Q * B ^ d) / (1 + |B| ^ k) :=
        div_le_div_of_nonneg_right hpow hdenpos.le
      _ ≤ (Q * B ^ d) / B ^ k :=
        div_le_div_of_nonneg_left
          (mul_nonneg (by positivity) (pow_nonneg hB0 _)) hBkpos hden
      _ = Q * (B ^ d / B ^ k) := by ring
  · exact hmodel

def rawHorizontalConstant (N : ℝ) (n : ℕ) : ℝ :=
  (1600 * 5 ^ 6) *
    max (Real.rpow N (deepLeftSigma n)) (Real.rpow N 2) *
      uniformStripMellinDecayConstant n (rawHorizontalMellinOrder n) 2

def rawHorizontalEnvelope (N g : ℝ) (n : ℕ) (B : ℝ) : ℝ :=
  rawHorizontalConstant N n *
    (rawZetaHorizontalRadius n (B - g) ^ rawZetaHorizontalDegree n /
      (1 + |B| ^ rawHorizontalMellinOrder n))

/-- Uniform pointwise envelope across the complete raw horizontal edge. -/
theorem norm_lemma295RawIntegrand_horizontal_uniform_le
    {N : ℝ} (hN : 0 < N) (g : ℝ) (n : ℕ) {x B : ℝ}
    (hx : x ∈ Set.Icc (deepLeftSigma n) 2)
    (hheight : 2 ≤ |B - g|) :
    ‖lemma295RawIntegrand N g ((x : ℂ) + B * I)‖ ≤
      rawHorizontalEnvelope N g n B := by
  let s : ℂ := (x : ℂ) + B * I
  let z : ℂ := s - g * I
  have hzform : z = (x : ℂ) + (((B - g : ℝ) : ℂ)) * I := by
    dsimp [z, s]
    apply Complex.ext <;> simp
  have hzeta := norm_riemannZeta_rawHorizontal_le n hx hheight
  rw [← hzform] at hzeta
  have hscale := norm_positiveScale_horizontal_le_max hN hx.1 hx.2
    (t := B - g)
  rw [← hzform] at hscale
  have hmellinMul :=
    one_add_absPow_mul_norm_mellin_sourceHZero_deepLeft_to_two_le
      n (rawHorizontalMellinOrder n) hx B
  have hden : 0 < 1 + |B| ^ rawHorizontalMellinOrder n := by positivity
  have hmellin : ‖mellin sourceHZero s‖ ≤
      uniformStripMellinDecayConstant n (rawHorizontalMellinOrder n) 2 /
        (1 + |B| ^ rawHorizontalMellinOrder n) := by
    apply (le_div_iff₀ hden).2
    simpa [s, mul_comm] using hmellinMul
  have hzetaUp : 0 ≤ (1600 * 5 ^ 6 : ℝ) *
      rawZetaHorizontalRadius n (B - g) ^ rawZetaHorizontalDegree n :=
    (norm_nonneg _).trans hzeta
  have hscaleUp : 0 ≤ max (Real.rpow N (deepLeftSigma n)) (Real.rpow N 2) :=
    (norm_nonneg _).trans hscale
  unfold lemma295RawIntegrand rawHorizontalEnvelope rawHorizontalConstant
  repeat' rw [norm_mul]
  calc
    ‖(N : ℂ) ^ z‖ * ‖riemannZeta z‖ * ‖mellin sourceHZero s‖ ≤
        max (Real.rpow N (deepLeftSigma n)) (Real.rpow N 2) *
          ((1600 * 5 ^ 6) *
            rawZetaHorizontalRadius n (B - g) ^ rawZetaHorizontalDegree n) *
          (uniformStripMellinDecayConstant n (rawHorizontalMellinOrder n) 2 /
            (1 + |B| ^ rawHorizontalMellinOrder n)) := by
      exact mul_le_mul
        (mul_le_mul hscale hzeta (norm_nonneg _) hscaleUp)
        hmellin (norm_nonneg _) (mul_nonneg hscaleUp hzetaUp)
    _ = (1600 * 5 ^ 6) *
        max (Real.rpow N (deepLeftSigma n)) (Real.rpow N 2) *
          uniformStripMellinDecayConstant n (rawHorizontalMellinOrder n) 2 *
            (rawZetaHorizontalRadius n (B - g) ^ rawZetaHorizontalDegree n /
              (1 + |B| ^ rawHorizontalMellinOrder n)) := by ring

theorem tendsto_rawHorizontalEnvelope_zero (N g : ℝ) (n : ℕ) :
    Tendsto (rawHorizontalEnvelope N g n) atTop (𝓝 0) := by
  simpa [rawHorizontalEnvelope] using!
    (tendsto_rawZetaMellinRatio_zero n g).const_mul (rawHorizontalConstant N n)

/-- The upper side of the raw rectangle tends to zero. -/
theorem tendsto_lemma295Raw_horizontalIntegral_zero
    {N : ℝ} (hN : 0 < N) (g : ℝ) (n : ℕ) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in deepLeftSigma n..2,
        lemma295RawIntegrand N g ((x : ℂ) + B * I))
      atTop (𝓝 0) := by
  have henv := tendsto_rawHorizontalEnvelope_zero N g n
  have hbound : ∀ᶠ B : ℝ in atTop,
      ‖∫ x : ℝ in deepLeftSigma n..2,
          lemma295RawIntegrand N g ((x : ℂ) + B * I)‖ ≤
        rawHorizontalEnvelope N g n B * |(2 : ℝ) - deepLeftSigma n| := by
    filter_upwards [eventually_ge_atTop (|g| + 2)] with B hB
    have hB0 : 0 ≤ B := by linarith [abs_nonneg g]
    have hheight : 2 ≤ |B - g| := by
      rw [abs_of_nonneg (by linarith [le_abs_self g])]
      linarith [le_abs_self g]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc (deepLeftSigma n) 2 := by
      have hsub := Set.uIoc_subset_uIcc hx
      have hab : deepLeftSigma n ≤ (2 : ℝ) := by
        unfold deepLeftSigma
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      rw [Set.uIcc_of_le hab] at hsub
      exact hsub
    exact norm_lemma295RawIntegrand_horizontal_uniform_le hN g n hx' hheight
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  · exact hbound
  · simpa using henv.mul_const |(2 : ℝ) - deepLeftSigma n|

/-- The lower side of the raw rectangle, parametrized by positive height,
tends to zero. -/
theorem tendsto_lemma295Raw_lowerHorizontalIntegral_zero
    {N : ℝ} (hN : 0 < N) (g : ℝ) (n : ℕ) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in deepLeftSigma n..2,
        lemma295RawIntegrand N g ((x : ℂ) + (-B) * I))
      atTop (𝓝 0) := by
  have henv := tendsto_rawHorizontalEnvelope_zero N (-g) n
  have hbound : ∀ᶠ B : ℝ in atTop,
      ‖∫ x : ℝ in deepLeftSigma n..2,
          lemma295RawIntegrand N g ((x : ℂ) + (-B) * I)‖ ≤
        rawHorizontalEnvelope N (-g) n B * |(2 : ℝ) - deepLeftSigma n| := by
    filter_upwards [eventually_ge_atTop (|g| + 2)] with B hB
    have hheight : 2 ≤ |-B - g| := by
      rw [show -B - g = -(B + g) by ring, abs_neg]
      have : 0 ≤ B + g := by linarith [neg_le_abs g]
      rw [abs_of_nonneg this]
      linarith [neg_le_abs g]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc (deepLeftSigma n) 2 := by
      have hsub := Set.uIoc_subset_uIcc hx
      have hab : deepLeftSigma n ≤ (2 : ℝ) := by
        unfold deepLeftSigma
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      rw [Set.uIcc_of_le hab] at hsub
      exact hsub
    have hp := norm_lemma295RawIntegrand_horizontal_uniform_le hN g n hx' hheight
    have henvEq : rawHorizontalEnvelope N g n (-B) =
        rawHorizontalEnvelope N (-g) n B := by
      unfold rawHorizontalEnvelope rawZetaHorizontalRadius
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
  · simpa using henv.mul_const |(2 : ℝ) - deepLeftSigma n|

end
end GuthMaynardLemma295RawHorizontalIntegral

#print axioms GuthMaynardLemma295RawHorizontalIntegral.norm_lemma295RawIntegrand_horizontal_uniform_le
#print axioms GuthMaynardLemma295RawHorizontalIntegral.tendsto_lemma295Raw_horizontalIntegral_zero
#print axioms GuthMaynardLemma295RawHorizontalIntegral.tendsto_lemma295Raw_lowerHorizontalIntegral_zero
