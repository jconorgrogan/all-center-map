import APRegularNearLogSaving

/-!
# Exact bulk/collar split for Jutila equation (1.7)

Jutila's proof of Theorem 1 treats `4/5 <= alpha <= 1-delta` by the
Huxley--Jutila density theorem cited as [6], and proves the remaining collar
`1-delta <= alpha <= 1` with Lemmas 4--8 and the page-53 correlation
argument.  This module records that source-faithful split at the sole loss
needed by MAP.

The split point is the internal loss selected by
`MAPJutilaTheoremOneFiniteClosure.internalDelta (1/10)`, namely `1/560`.
No zero-density estimate is proved here.  The theorem below only verifies
that the two disjoint analytic branches have exactly the quantifiers and
uniform constants needed to inhabit
`JutilaEquation17OneTenthEventually`.
-/

namespace MAPJutilaEquation17RangeSplit

open MAPAPRegularNearLogSaving
open MAPAPZeroDensityCert
noncomputable section

/-- The fixed internal loss used by the MAP specialization of Jutila's
near-one proof. -/
def splitDelta : ℝ := 1 / 560

theorem splitDelta_eq : splitDelta = (1 / 560 : ℝ) := by
  rfl

theorem splitDelta_pos : 0 < splitDelta := by
  rw [splitDelta_eq]
  norm_num

/-- The older Huxley--Jutila branch quoted in the first sentence of
Section 3, restricted to the fixed loss and eventual scale needed by MAP. -/
abbrev BulkEquation17OneTenthEventually : Prop :=
  ∃ C R₀ : ℝ, 0 < C ∧ 0 ≤ R₀ ∧
    ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
      1 ≤ T → 4 / 5 ≤ sigma → sigma ≤ 1 - splitDelta →
      R₀ ≤ (q : ℝ) * T →
        (ambientZeroCountAtLevel q sigma T : ℝ) ≤
          C * Real.rpow ((q : ℝ) * T)
            ((21 / 10) * (1 - sigma))

/-- Jutila's own Lemmas 4--8 and page-53 branch, again only in the fixed
collar and at eventual scale. -/
abbrev CollarEquation17OneTenthEventually : Prop :=
  ∃ C R₀ : ℝ, 0 < C ∧ 0 ≤ R₀ ∧
    ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
      1 ≤ T → 1 - splitDelta ≤ sigma → sigma ≤ 1 →
      R₀ ≤ (q : ℝ) * T →
        (ambientZeroCountAtLevel q sigma T : ℝ) ≤
          C * Real.rpow ((q : ℝ) * T)
            ((21 / 10) * (1 - sigma))

/-- Exact reconstruction of the MAP-facing eventual equation (1.7) from
the two analytic ranges in Jutila's published proof.  Constants and starting
scales are combined by maxima, preserving uniformity in `q`, `T`, and
`sigma`. -/
theorem oneTenthEventually_of_bulk_and_collar
    (hBulk : BulkEquation17OneTenthEventually)
    (hCollar : CollarEquation17OneTenthEventually) :
    JutilaEquation17OneTenthEventually := by
  obtain ⟨C₁, R₁, hC₁, hR₁, hBulk⟩ := hBulk
  obtain ⟨C₂, R₂, hC₂, hR₂, hCollar⟩ := hCollar
  refine ⟨max C₁ C₂, max R₁ R₂, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le hC₁ (le_max_left _ _)
  · exact le_trans hR₁ (le_max_left _ _)
  · intro q _inst T sigma hT hsigmaLow hsigmaHigh hscale
    have hscale₁ : R₁ ≤ (q : ℝ) * T :=
      (le_max_left R₁ R₂).trans hscale
    have hscale₂ : R₂ ≤ (q : ℝ) * T :=
      (le_max_right R₁ R₂).trans hscale
    by_cases hsigma : sigma ≤ 1 - splitDelta
    · have h := hBulk q T sigma hT hsigmaLow hsigma hscale₁
      exact h.trans (mul_le_mul_of_nonneg_right
        (le_max_left C₁ C₂)
        (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg q) (by linarith)) _))
    · have hsigma' : 1 - splitDelta ≤ sigma := le_of_not_ge hsigma
      have h := hCollar q T sigma hT hsigma' hsigmaHigh hscale₂
      exact h.trans (mul_le_mul_of_nonneg_right
        (le_max_right C₁ C₂)
        (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg q) (by linarith)) _))

end

end MAPJutilaEquation17RangeSplit

#print axioms MAPJutilaEquation17RangeSplit.splitDelta_eq
#print axioms MAPJutilaEquation17RangeSplit.oneTenthEventually_of_bulk_and_collar
