import FixedCharacterPoweredBridge
import ZeroDensityArithmetic

/-!
# Budgeted fixed-character powered large-value bridge

The original staging target used the same epsilon before and after taking a
power.  That target is not source-faithful: a threshold `T^{-eta}` becomes
`T^{-k*eta}`, and the quadratic and quartic large-value terms therefore spend
`2*k*eta` and `4*k*eta`.  This module records that obstruction and replaces
the target by a contract with an explicit input-loss budget.

No density theorem is asserted.  `BudgetedFixedCharacterPoweredLargeValueBridge`
is the corrected target proposition to be inhabited from the two published
large-value inequalities.  All budget, bounded-power, and detector-adapter
deductions below are locally proved.
-/

namespace CGLProofDAG

open scoped BigOperators
open AppendixTypeIPower FixedCharacterPoweredBridge

noncomputable section

/-- A sigma-independent power cap.  On `7/10 <= sigma`, the upper endpoint
`15/(6+10*sigma)` is at most `15/13`. -/
def powerCap (κ : ℝ) : ℕ := ⌈(15 / 13 : ℝ) / κ⌉₊

/-- The loss supplied by the detector to a powered large-value argument.

The factor `64` leaves half of the requested output loss untouched even after
charging a deliberately conservative `32*(k+1)` copies of this loss.  This
covers the threshold power, coefficient normalization, common-block loss, and
the logarithmic length collar without relying on an equality endpoint. -/
def inputLoss (κ η : ℝ) : ℝ :=
  η / (64 * ((powerCap κ : ℝ) + 1))

theorem poweredLengthUpper_le_global
    {σ : ℝ} (hσ : 7 / 10 ≤ σ) :
    poweredLengthUpper σ ≤ 15 / 13 := by
  have hden : 0 < 6 + 10 * σ := by nlinarith
  rw [poweredLengthUpper, div_le_iff₀ hden]
  nlinarith

theorem powerCap_pos {κ : ℝ} (hκ : 0 < κ) : 0 < powerCap κ := by
  apply Nat.ceil_pos.mpr
  exact div_pos (by norm_num) hκ

/-- The bounded power produced by the exact GM window is controlled by the
single cap used in `inputLoss`. -/
theorem exists_power_bounded_by_powerCap
    {σ lam κ : ℝ}
    (hσlow : 7 / 10 ≤ σ) (hσhigh : σ ≤ 4 / 5)
    (hκ : 0 < κ) (hκlam : κ ≤ lam) (hlamHigh : lam ≤ 1 / 2) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ powerCap κ ∧
      poweredLengthLower σ ≤ k * lam ∧
      k * lam ≤ poweredLengthUpper σ := by
  obtain ⟨k, hk, hkcap, hlow, hhigh⟩ :=
    exists_bounded_power_in_guthMaynard_window
      hσlow hσhigh hκ hκlam hlamHigh
  refine ⟨k, hk, hkcap.trans ?_, hlow, hhigh⟩
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_right
    (poweredLengthUpper_le_global hσlow) hκ.le

theorem inputLoss_pos {κ η : ℝ} (_hκ : 0 < κ) (hη : 0 < η) :
    0 < inputLoss κ η := by
  unfold inputLoss
  positivity

/-- The full conservative local budget: for every selected `k`, thirty-two
copies of the powered input loss use at most half of the output epsilon. -/
theorem thirtyTwo_powered_inputLoss_le_half
    {κ η : ℝ} {k : ℕ} (hη : 0 ≤ η) (hk : k ≤ powerCap κ) :
    32 * ((k : ℝ) + 1) * inputLoss κ η ≤ η / 2 := by
  unfold inputLoss
  have hcap : (k : ℝ) ≤ powerCap κ := by exact_mod_cast hk
  have hden : 0 < 64 * ((powerCap κ : ℝ) + 1) := by positivity
  calc
    32 * ((k : ℝ) + 1) *
          (η / (64 * ((powerCap κ : ℝ) + 1))) =
        η * ((32 * ((k : ℝ) + 1)) /
          (64 * ((powerCap κ : ℝ) + 1))) := by ring
    _ ≤ η * (1 / 2 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hη
      rw [div_le_iff₀ hden]
      nlinarith
    _ = η / 2 := by ring

/-- In particular, the quartic source terms spend at most one quarter of the
requested output loss on the powered threshold. -/
theorem four_powered_inputLoss_le_quarter
    {κ η : ℝ} {k : ℕ} (hη : 0 ≤ η) (hk : k ≤ powerCap κ) :
    4 * (k : ℝ) * inputLoss κ η ≤ η / 4 := by
  have hmain := thirtyTwo_powered_inputLoss_le_half hη hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hloss0 : 0 ≤ inputLoss κ η := by
    unfold inputLoss
    positivity
  nlinarith [mul_nonneg hk0 hloss0]

/-- Formal death test for the old same-eta target.  At the exact upper
powered-length endpoint, even the quadratic GM term has exponent
`gmExponent sigma + 2*k*eta`, strictly larger than the advertised
`gmExponent sigma + eta` for every positive power. -/
theorem same_eta_budget_fails_at_first_term
    {σ η : ℝ} {k : ℕ}
    (hσlow : 7 / 10 ≤ σ) (hη : 0 < η) (hk : 1 ≤ k) :
    gmExponent σ + η <
      2 * poweredLengthUpper σ * (1 - σ) + 2 * (k : ℝ) * η := by
  rw [first_term_at_powered_upper hσlow]
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- Corrected, source-faithful target for Appendix (A.13).  The detector must
supply the polynomial at the smaller loss `inputLoss kappa eta`; the powered
argument may then spend at most the requested final `+eta`.

This is proposition-valued source-boundary data, not an axiom and not a claim
that the two analytic source inequalities have already been proved in Lean. -/
def BudgetedFixedCharacterPoweredLargeValueBridge : Prop :=
  ∀ κ η : ℝ, 0 < κ → 0 < η →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T σ : ℝ) (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 7 / 10 ≤ σ → σ ≤ 4 / 5 →
        Real.rpow T κ ≤ N →
        (N : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 →
        (∀ n, ‖b n‖ ≤ 1) →
        OneSeparated W →
        (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
        (∀ t ∈ W,
          Real.rpow N σ * Real.rpow T (-inputLoss κ η) ≤
            ‖dirichletPolynomial b N t‖) →
        (W.card : ℝ) ≤
          C * Real.rpow T (gmExponent σ + η)

/-- Stable bundle for the exact common dyadic polynomial that the quantitative
post-A.5 detector endpoint must return.  It deliberately excludes the
zero-set-to-fiber cardinal comparison, which belongs to the detector theorem
and can be composed after this large-value estimate. -/
def PostA5CommonDyadicThreshold
    (κ δ T σ : ℝ) (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ) : Prop :=
  Real.rpow T κ ≤ N ∧
  (N : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 ∧
  (∀ n, ‖b n‖ ≤ 1) ∧
  OneSeparated W ∧
  (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
  (∀ t ∈ W,
    Real.rpow N σ * Real.rpow T (-δ) ≤
      ‖dirichletPolynomial b N t‖)

/-- Exact adapter from the planned post-A.5 common-block output to the
corrected powered bridge.  The quantitative detector is instantiated at the
reserved loss, so no same-eta identification occurs. -/
theorem budgetedBridge_of_postA5_commonBlock
    (hbridge : BudgetedFixedCharacterPoweredLargeValueBridge) :
    ∀ κ η : ℝ, 0 < κ → 0 < η →
      ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
        ∀ (T σ : ℝ) (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ),
          T₀ ≤ T → 7 / 10 ≤ σ → σ ≤ 4 / 5 →
          PostA5CommonDyadicThreshold
            κ (inputLoss κ η) T σ N b W →
          (W.card : ℝ) ≤ C * Real.rpow T (gmExponent σ + η) := by
  intro κ η hκ hη
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ := hbridge κ η hκ hη
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T σ N b W hT hσlow hσhigh hdet
  rcases hdet with ⟨hNlow, hNhigh, hb, hsep, hheight, hlarge⟩
  exact hbound T σ N b W hT hσlow hσhigh hNlow hNhigh hb hsep
    hheight hlarge

end

end CGLProofDAG

#print axioms CGLProofDAG.poweredLengthUpper_le_global
#print axioms CGLProofDAG.powerCap_pos
#print axioms CGLProofDAG.exists_power_bounded_by_powerCap
#print axioms CGLProofDAG.thirtyTwo_powered_inputLoss_le_half
#print axioms CGLProofDAG.four_powered_inputLoss_le_quarter
#print axioms CGLProofDAG.same_eta_budget_fails_at_first_term
#print axioms CGLProofDAG.budgetedBridge_of_postA5_commonBlock
