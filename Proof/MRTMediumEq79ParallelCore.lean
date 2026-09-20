import MRTProposition51HardBranch

/-!
# MRT equation (79): literal medium-frequency data

This file fixes the signs and constants in the source's equation (79).  It
does not postulate the transform identity.  In particular, the factor
`1/(2π)`, the Mellin phase `n⁻ⁱᵗ`, the factor `Xⁱᵗ`, and the two differently
scaled copies of the same cutoff are all visible in the definitions.
-/

namespace MAPMRTMediumEq79Parallel

open MeasureTheory Set
open MAPMRTProposition51HardBranch MAPMRTProposition51Source

noncomputable section

/-- The source factor `X^{it}`, written without an ambiguous complex-power
convention. -/
def xMellinPhase (X t : ℝ) : ℂ :=
  Complex.exp (((t * Real.log X : ℝ) : ℂ) * Complex.I)

theorem norm_xMellinPhase (X t : ℝ) : ‖xMellinPhase X t‖ = 1 := by
  unfold xMellinPhase
  rw [Complex.norm_exp_ofReal_mul_I]

/-- The parenthesis in the displayed definition of `F̃` following (79). -/
def mediumCutoffMultiplier
    (X beta eta : ℝ) (cutoff : ℝ → ℝ) (t : ℝ) : ℂ :=
  (cutoff (eta * t / (|beta| * X)) : ℂ) -
    (cutoff (t / (10 * eta * |beta| * X)) : ℂ)

/-- The literal `F̃` in MRT (79), including its `1/(2π)` coefficient. -/
def sourceTildePolynomial
    (N : ℕ) (X beta eta : ℝ) (cutoff : ℝ → ℝ)
    (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * finiteCriticalPolynomial N f t *
    xMellinPhase X t * mediumCutoffMultiplier X beta eta cutoff t

/-- The exact two-component frequency region `I` in source equation (69). -/
def sourceFrequencyRegion (X beta eta : ℝ) : Set ℝ :=
  {t | eta * |beta| * X ≤ |t| ∧ |t| ≤ |beta| * X / eta}

theorem mem_sourceFrequencyRegion_iff
    {X beta eta t : ℝ} :
    t ∈ sourceFrequencyRegion X beta eta ↔
      eta * |beta| * X ≤ |t| ∧ |t| ≤ |beta| * X / eta := by
  rfl

/-- The medium multiplier is supported on `I`.  This is the source's claim
immediately after (79), with the numerical use of `η < 1/100` exposed.

At the inner edge both cutoff arguments lie in `[-1/10,1/10]`, hence cancel.
At the outer edge both lie outside `[-1,1]`, hence vanish. -/
theorem mediumCutoffMultiplier_eq_zero_off_sourceFrequencyRegion
    {X beta eta t : ℝ} {cutoff : ℝ → ℝ}
    (hX : 0 < X) (hbeta : beta ≠ 0)
    (heta : 0 < eta) (hetaSmall : eta < 1 / 100)
    (hcutoffOne : ∀ y, |y| ≤ 1 / 10 → cutoff y = 1)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (ht : t ∉ sourceFrequencyRegion X beta eta) :
    mediumCutoffMultiplier X beta eta cutoff t = 0 := by
  have hb : 0 < |beta| := abs_pos.mpr hbeta
  have hden : 0 < |beta| * X := mul_pos hb hX
  have hten : 0 < 10 * eta * |beta| * X := by positivity
  simp only [sourceFrequencyRegion, Set.mem_setOf_eq, not_and_or, not_le] at ht
  rcases ht with hinner | houter
  · have hargOne : |eta * t / (|beta| * X)| ≤ 1 / 10 := by
      rw [abs_div, abs_mul, abs_of_pos heta, abs_of_pos hden]
      have hetaBound : eta ≤ 1 / 100 := hetaSmall.le
      have hsq : eta ^ 2 ≤ 1 / 10000 := by nlinarith
      apply (div_le_iff₀ hden).2
      calc
        eta * |t| ≤ eta * (eta * |beta| * X) :=
          (mul_lt_mul_of_pos_left hinner heta).le
        _ = eta ^ 2 * (|beta| * X) := by ring
        _ ≤ (1 / 10000) * (|beta| * X) :=
          mul_le_mul_of_nonneg_right hsq hden.le
        _ ≤ (1 / 10) * (|beta| * X) := by
          gcongr <;> norm_num
    have hargTwo : |t / (10 * eta * |beta| * X)| ≤ 1 / 10 := by
      rw [abs_div, abs_of_pos hten]
      apply (div_le_iff₀ hten).2
      calc
        |t| ≤ eta * |beta| * X := hinner.le
        _ ≤ (1 / 10) * (10 * eta * |beta| * X) := by
          nlinarith [mul_pos (mul_pos heta hb) hX]
    rw [mediumCutoffMultiplier, hcutoffOne _ hargOne,
      hcutoffOne _ hargTwo]
    simp
  · have hargOne : 1 ≤ |eta * t / (|beta| * X)| := by
      rw [abs_div, abs_mul, abs_of_pos heta, abs_of_pos hden]
      apply (le_div_iff₀ hden).2
      have := mul_lt_mul_of_pos_left houter heta
      field_simp [heta.ne'] at this ⊢
      nlinarith
    have hargTwo : 1 ≤ |t / (10 * eta * |beta| * X)| := by
      rw [abs_div, abs_of_pos hten]
      apply (le_div_iff₀ hten).2
      have hetaSq : 10 * eta ^ 2 < 1 := by
        have : eta < 1 / 100 := hetaSmall
        nlinarith [sq_nonneg (eta - 1 / 100)]
      have houter' : |beta| * X / eta < |t| := houter
      apply le_of_lt
      calc
        1 * (10 * eta * |beta| * X) =
            (10 * eta ^ 2) * (|beta| * X / eta) := by
          field_simp [heta.ne']
        _ < 1 * (|beta| * X / eta) := by
          gcongr
        _ < |t| := by simpa using houter'
    rw [mediumCutoffMultiplier, hcutoffSupport _ hargOne,
      hcutoffSupport _ hargTwo]
    simp

theorem sourceTildePolynomial_eq_zero_off_sourceFrequencyRegion
    {N : ℕ} {X beta eta t : ℝ} {cutoff : ℝ → ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hbeta : beta ≠ 0)
    (heta : 0 < eta) (hetaSmall : eta < 1 / 100)
    (hcutoffOne : ∀ y, |y| ≤ 1 / 10 → cutoff y = 1)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (ht : t ∉ sourceFrequencyRegion X beta eta) :
    sourceTildePolynomial N X beta eta cutoff f t = 0 := by
  rw [sourceTildePolynomial,
    mediumCutoffMultiplier_eq_zero_off_sourceFrequencyRegion hX hbeta heta
      hetaSmall hcutoffOne hcutoffSupport ht]
  simp

/-- The pointwise comparison `F̃(t)=O(|F(t)|)` used before (81), with an
explicit coefficient. -/
theorem norm_sourceTildePolynomial_le
    {N : ℕ} {X beta eta t : ℝ} {cutoff : ℝ → ℝ} {f : ℕ → ℂ}
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1) :
    ‖sourceTildePolynomial N X beta eta cutoff f t‖ ≤
      (1 / Real.pi) * ‖finiteCriticalPolynomial N f t‖ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hmult : ‖mediumCutoffMultiplier X beta eta cutoff t‖ ≤ 2 := by
    unfold mediumCutoffMultiplier
    calc
      ‖(cutoff (eta * t / (|beta| * X)) : ℂ) -
          (cutoff (t / (10 * eta * |beta| * X)) : ℂ)‖ ≤
          ‖(cutoff (eta * t / (|beta| * X)) : ℂ)‖ +
            ‖(cutoff (t / (10 * eta * |beta| * X)) : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
        simpa only [Complex.norm_real, Real.norm_eq_abs] using
          add_le_add (hcutoffBound _) (hcutoffBound _)
      _ = 2 := by norm_num
  unfold sourceTildePolynomial
  rw [norm_mul, norm_mul, norm_mul, norm_xMellinPhase, mul_one]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have hcoef : |1 / (2 * Real.pi)| = 1 / (2 * Real.pi) := by
    rw [abs_of_pos]
    positivity
  rw [hcoef]
  calc
    (1 / (2 * Real.pi)) * ‖finiteCriticalPolynomial N f t‖ *
        ‖mediumCutoffMultiplier X beta eta cutoff t‖ ≤
      (1 / (2 * Real.pi)) * ‖finiteCriticalPolynomial N f t‖ * 2 := by
        gcongr
    _ = (1 / Real.pi) * ‖finiteCriticalPolynomial N f t‖ := by
      field_simp [hpi.ne']

/-- The exact double integral printed as equation (79). -/
def equation79Integral
    (N : ℕ) (X beta eta : ℝ) (cutoff : ℝ → ℝ)
    (f : ℕ → ℂ) (G : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ, ∫ w : ℝ,
    sourceTildePolynomial N X beta eta cutoff f t * G w *
      Complex.exp ((((t * w : ℝ) : ℂ) * Complex.I))

end
end MAPMRTMediumEq79Parallel

#print axioms MAPMRTMediumEq79Parallel.norm_xMellinPhase
#print axioms MAPMRTMediumEq79Parallel.mediumCutoffMultiplier_eq_zero_off_sourceFrequencyRegion
#print axioms MAPMRTMediumEq79Parallel.sourceTildePolynomial_eq_zero_off_sourceFrequencyRegion
#print axioms MAPMRTMediumEq79Parallel.norm_sourceTildePolynomial_le
