import BudgetedFixedCharacterPoweredLargeValueBridge
import AppendixTypeIPowerAlgebra

/-!
# Narrow 30/13 transfer after the powered-polynomial theorem

This file deliberately does not assert the missing powered large-value theorem.
It proves that its literal conclusion is already sufficient for the uniform
`30/13` bound on the full MAP Type-I strip.
-/

namespace CGLPoweredToUniformDensity

open scoped BigOperators

noncomputable section

open CGLProofDAG AppendixTypeIPower

/-- The exact `15/(3+5σ)` output of the powered argument is bounded by the
uniform `30/13` exponent, with half of the requested loss retained as reserve. -/
theorem powered_exponent_add_half_loss_le_uniform
    {σ η : ℝ} (hσlow : 7 / 10 ≤ σ) (hσhigh : σ ≤ 4 / 5)
    (hη : 0 < η) :
    15 * (1 - σ) / (3 + 5 * σ) + η / 2 ≤
      (30 / 13) * (1 - σ) + η := by
  have hden : 3 + 5 * σ ≠ 0 := by nlinarith
  have hsource :
      15 * (1 - σ) / (3 + 5 * σ) = gmExponent σ := by
    rw [gmExponent, gmCoefficient]
    field_simp
  rw [hsource]
  have hgm := gmExponent_le_uniformExponent hσlow hσhigh
  linarith

/-- Once the actual fixed-character powered-polynomial estimate is supplied,
this theorem produces the uniform `30/13` large-value bound needed in the MAP
sigma range.  All hypotheses on the literal polynomial and ordinate set are
preserved verbatim. -/
@[deprecated "The same-eta premise is not stable under powering; use uniformThirtyThirteen_of_budgetedFixedCharacterPoweredBridge." (since := "2026-08-29")]
theorem uniformThirtyThirteen_of_fixedCharacterPoweredBridge
    (hpowered : FixedCharacterPoweredLargeValueBridge) :
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
            Real.rpow N σ * Real.rpow T (-(η / 2)) ≤
              ‖dirichletPolynomial b N t‖) →
          (W.card : ℝ) ≤
            C * Real.rpow T ((30 / 13) * (1 - σ) + η) := by
  intro κ η hκ hη
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ :=
    hpowered κ (η / 2) hκ (half_pos hη)
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T σ N b W hT hσlow hσhigh hNlow hNhigh hb hsep hheight hlarge
  have hraw := hbound T σ N b W hT hσlow hσhigh hNlow hNhigh hb
    hsep hheight hlarge
  have hT1 : 1 ≤ T := (by norm_num : (1 : ℝ) ≤ 2).trans (hT₀.trans hT)
  have hexp := powered_exponent_add_half_loss_le_uniform hσlow hσhigh hη
  exact hraw.trans <| mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT1 hexp) (le_of_lt hC)

/-- The exact `gmExponent` output of the corrected powered argument is bounded
by the uniform `30/13` exponent, with half of the requested loss retained. -/
theorem budgeted_powered_exponent_add_half_loss_le_uniform
    {σ η : ℝ} (hσlow : 7 / 10 ≤ σ) (hσhigh : σ ≤ 4 / 5)
    (hη : 0 < η) :
    gmExponent σ + η / 2 ≤ (30 / 13) * (1 - σ) + η := by
  have hgm := gmExponent_le_uniformExponent hσlow hσhigh
  linarith

/-- Correct downstream consumer of the powered theorem.  Invoking the bridge
with output loss `eta/2` asks the post-A.5 detector for the explicitly smaller
threshold loss `inputLoss kappa (eta/2)`; no same-eta identification occurs. -/
theorem uniformThirtyThirteen_of_budgetedFixedCharacterPoweredBridge
    (hpowered : BudgetedFixedCharacterPoweredLargeValueBridge) :
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
            Real.rpow N σ *
                Real.rpow T (-inputLoss κ (η / 2)) ≤
              ‖dirichletPolynomial b N t‖) →
          (W.card : ℝ) ≤
            C * Real.rpow T ((30 / 13) * (1 - σ) + η) := by
  intro κ η hκ hη
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ :=
    hpowered κ (η / 2) hκ (half_pos hη)
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T σ N b W hT hσlow hσhigh hNlow hNhigh hb hsep hheight hlarge
  have hraw := hbound T σ N b W hT hσlow hσhigh hNlow hNhigh hb
    hsep hheight hlarge
  have hT1 : 1 ≤ T := (by norm_num : (1 : ℝ) ≤ 2).trans (hT₀.trans hT)
  have hexp := budgeted_powered_exponent_add_half_loss_le_uniform
    hσlow hσhigh hη
  exact hraw.trans <| mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT1 hexp) (le_of_lt hC)

end
end CGLPoweredToUniformDensity

#print axioms CGLPoweredToUniformDensity.powered_exponent_add_half_loss_le_uniform
#print axioms CGLPoweredToUniformDensity.uniformThirtyThirteen_of_fixedCharacterPoweredBridge
#print axioms CGLPoweredToUniformDensity.budgeted_powered_exponent_add_half_loss_le_uniform
#print axioms CGLPoweredToUniformDensity.uniformThirtyThirteen_of_budgetedFixedCharacterPoweredBridge
