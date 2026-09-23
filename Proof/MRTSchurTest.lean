import Mathlib.MeasureTheory.Integral.Prod

/-! A first-principles Schur bilinear estimate used in MRT equation (81). -/

namespace MAPMRTSchurTest

open MeasureTheory

noncomputable section

/-- A nonnegative, unweighted Schur estimate on one sigma-finite measure space.
This is the exact `p=q=1` case needed in equation (81), proved by Tonelli and
`2ab ≤ a²+b²`; it does not use the external Halmos--Sunder theorem.  The factor
`2` is harmless and makes the proof valid in `ENNReal` without division. -/
theorem lintegral_bilinear_le_two_mul_of_schur
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {A : α → NNReal} {K : α → α → ENNReal} {M : ENNReal}
    (hA : Measurable fun x ↦ (A x : ENNReal))
    (hK : Measurable fun z : α × α ↦ K z.1 z.2)
    (hM : M ≠ ⊤)
    (hrow : ∀ x, (∫⁻ y, K x y ∂μ) ≤ M)
    (hcol : ∀ y, (∫⁻ x, K x y ∂μ) ≤ M) :
    (∫⁻ z : α × α,
        (A z.1 : ENNReal) * (A z.2 : ENNReal) * K z.1 z.2 ∂μ.prod μ) ≤
      2 * M * (∫⁻ x, (A x : ENNReal) ^ 2 ∂μ) := by
  let F : α × α → ENNReal := fun z ↦
    (A z.1 : ENNReal) * (A z.2 : ENNReal) * K z.1 z.2
  let G₁ : α × α → ENNReal := fun z ↦
    (A z.1 : ENNReal) ^ 2 * K z.1 z.2
  let G₂ : α × α → ENNReal := fun z ↦
    (A z.2 : ENNReal) ^ 2 * K z.1 z.2
  have hF : Measurable F := by
    unfold F
    exact ((hA.comp measurable_fst).mul (hA.comp measurable_snd)).mul hK
  have hG₁ : Measurable G₁ := by
    unfold G₁
    exact (hA.comp measurable_fst).pow_const 2 |>.mul hK
  have hG₂ : Measurable G₂ := by
    unfold G₂
    exact (hA.comp measurable_snd).pow_const 2 |>.mul hK
  have hpoint : ∀ z, F z ≤ G₁ z + G₂ z := by
    intro z
    have hab : (A z.1 : ENNReal) * (A z.2 : ENNReal) ≤
        (A z.1 : ENNReal) ^ 2 + (A z.2 : ENNReal) ^ 2 := by
      exact_mod_cast (show (A z.1 : ℝ) * (A z.2 : ℝ) ≤
          (A z.1 : ℝ) ^ 2 + (A z.2 : ℝ) ^ 2 by
        nlinarith [sq_nonneg ((A z.1 : ℝ) - (A z.2 : ℝ))])
    calc
      F z ≤ ((A z.1 : ENNReal) ^ 2 + (A z.2 : ENNReal) ^ 2) * K z.1 z.2 := by
        unfold F
        exact mul_le_mul_left hab _
      _ = G₁ z + G₂ z := by unfold G₁ G₂; ring
  have hI₁ : (∫⁻ z : α × α, G₁ z ∂μ.prod μ) ≤
      (∫⁻ x, (A x : ENNReal) ^ 2 ∂μ) * M := by
    rw [lintegral_prod G₁ hG₁.aemeasurable]
    calc
      (∫⁻ x, ∫⁻ y, G₁ (x, y) ∂μ ∂μ) ≤
          ∫⁻ x, (A x : ENNReal) ^ 2 * M ∂μ := by
        apply lintegral_mono
        intro x
        change (∫⁻ y, G₁ (x, y) ∂μ) ≤ (A x : ENNReal) ^ 2 * M
        rw [show (∫⁻ y, G₁ (x, y) ∂μ) =
            (A x : ENNReal) ^ 2 * (∫⁻ y, K x y ∂μ) by
          unfold G₁
          exact lintegral_const_mul' ((A x : ENNReal) ^ 2)
            (fun y ↦ K x y) (by simp)]
        exact mul_le_mul_right (hrow x) _
      _ = (∫⁻ x, (A x : ENNReal) ^ 2 ∂μ) * M := by
        exact lintegral_mul_const' M _ hM
  have hswap : (∫⁻ z : α × α, G₂ z ∂μ.prod μ) =
      ∫⁻ z : α × α, G₂ z.swap ∂μ.prod μ := by
    symm
    exact (Measure.measurePreserving_swap (μ := μ) (ν := μ)).lintegral_comp hG₂
  have hI₂ : (∫⁻ z : α × α, G₂ z ∂μ.prod μ) ≤
      (∫⁻ x, (A x : ENNReal) ^ 2 ∂μ) * M := by
    rw [hswap]
    have hG₂swap : Measurable (fun z : α × α ↦ G₂ z.swap) :=
      hG₂.comp measurable_swap
    rw [lintegral_prod (fun z : α × α ↦ G₂ z.swap) hG₂swap.aemeasurable]
    calc
      (∫⁻ x, ∫⁻ y, G₂ (x, y).swap ∂μ ∂μ) ≤
          ∫⁻ x, (A x : ENNReal) ^ 2 * M ∂μ := by
        apply lintegral_mono
        intro x
        change (∫⁻ y, G₂ (x, y).swap ∂μ) ≤ (A x : ENNReal) ^ 2 * M
        rw [show (∫⁻ y, G₂ (x, y).swap ∂μ) =
            (A x : ENNReal) ^ 2 * (∫⁻ y, K y x ∂μ) by
          unfold G₂
          exact lintegral_const_mul' ((A x : ENNReal) ^ 2)
            (fun y ↦ K y x) (by simp)]
        exact mul_le_mul_right (hcol x) _
      _ = (∫⁻ x, (A x : ENNReal) ^ 2 ∂μ) * M := by
        exact lintegral_mul_const' M _ hM
  calc
    (∫⁻ z : α × α, F z ∂μ.prod μ) ≤
        ∫⁻ z : α × α, (G₁ z + G₂ z) ∂μ.prod μ :=
      lintegral_mono hpoint
    _ = (∫⁻ z : α × α, G₁ z ∂μ.prod μ) +
        ∫⁻ z : α × α, G₂ z ∂μ.prod μ :=
      lintegral_add_left hG₁ _
    _ ≤ ((∫⁻ x, (A x : ENNReal) ^ 2 ∂μ) * M) +
        ((∫⁻ x, (A x : ENNReal) ^ 2 ∂μ) * M) := add_le_add hI₁ hI₂
    _ = 2 * M * (∫⁻ x, (A x : ENNReal) ^ 2 ∂μ) := by ring

#print axioms lintegral_bilinear_le_two_mul_of_schur

end
end MAPMRTSchurTest
