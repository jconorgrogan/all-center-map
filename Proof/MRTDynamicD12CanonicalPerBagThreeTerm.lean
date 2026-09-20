import MRTDynamicD12ActiveCanonicalLedger

/-! Final algebraic weld for the canonical per-bag producer.

The source theorem supplies the literal `max 0 (max rawLedger₁ rawLedger₂)`
bound.  The scalar theorem supplies one three-term estimate for each raw
ledger.  This lemma combines them after synchronizing constants and log
exponents; it contains no source mass or envelope premise.
-/
namespace MRTDynamicD12CanonicalPerBagThreeTerm

noncomputable section

set_option maxHeartbeats 800000

theorem normalized_active_component_of_scalar_bounds
    {N I R₁ R₂ C₁ C₂ L W : ℝ} {E₁ E₂ : ℕ}
    (hN : 0 ≤ N) (hI : I ≤ max 0 (max R₁ R₂))
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : N * R₁ ≤ C₁ * L ^ E₁ * W)
    (h₂ : N * R₂ ≤ C₂ * L ^ E₂ * W) :
    N * I ≤ max C₁ C₂ * L ^ (max E₁ E₂) * W := by
  have hE₁ : L ^ E₁ ≤ L ^ (max E₁ E₂) :=
    pow_le_pow_right₀ hL (by omega)
  have hE₂ : L ^ E₂ ≤ L ^ (max E₁ E₂) :=
    pow_le_pow_right₀ hL (by omega)
  have hC₁' : C₁ * L ^ E₁ * W ≤
      max C₁ C₂ * L ^ (max E₁ E₂) * W := by
    gcongr
    · exact le_max_left _ _
  have hC₂' : C₂ * L ^ E₂ * W ≤
      max C₁ C₂ * L ^ (max E₁ E₂) * W := by
    gcongr
    · exact le_max_right _ _
  have htarget : 0 ≤ max C₁ C₂ * L ^ (max E₁ E₂) * W := by positivity
  have hmax : N * max R₁ R₂ ≤
      max C₁ C₂ * L ^ (max E₁ E₂) * W := by
    rcases le_total R₁ R₂ with h12 | h21
    · rw [max_eq_right h12]
      exact (h₂.trans hC₂')
    · rw [max_eq_left h21]
      exact (h₁.trans hC₁')
  calc
    N * I ≤ N * max 0 (max R₁ R₂) :=
      mul_le_mul_of_nonneg_left hI hN
    _ = max (N * 0) (N * max R₁ R₂) := by
      exact mul_max_of_nonneg _ _ hN
    _ ≤ max 0 (max C₁ C₂ * L ^ (max E₁ E₂) * W) := by
      simp only [mul_zero]
      exact max_le_max le_rfl hmax
    _ = max C₁ C₂ * L ^ (max E₁ E₂) * W := max_eq_right htarget

end
end MRTDynamicD12CanonicalPerBagThreeTerm

#print axioms MRTDynamicD12CanonicalPerBagThreeTerm.normalized_active_component_of_scalar_bounds
