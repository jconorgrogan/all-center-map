import GuthMaynardSectorFactorization

/-! # Literal S2 reduction to the complete Fourier pair moment
The zero-frequency leg is bounded by its separated row and column sums.
No absolute values are moved inside the nonzero Fourier sum, so the pair
moment is the one to which Lemma 6.2 and Heath--Brown apply.
-/

namespace GuthMaynardS2LiteralReduction

open scoped BigOperators
open GuthMaynardSectorFactorization GuthMaynardEquation55Infinite
open GuthMaynardS1Source GuthMaynardS1Tail
open GuthMaynardSectionThreeCutoffDerivativeBudget

noncomputable section

/-- The literal pair moment before reflection or dyadic decomposition. -/
def sourceNonzeroFourierPairMoment (N : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ a ∈ W, ∑ b ∈ W, ‖sourceNonzeroFourier N (a - b)‖ ^ 2

private theorem weighted_cycle_le_pairMoment
    {ι : Type*} [DecidableEq ι] (W : Finset ι)
    (A f : ι → ι → ℝ) {C : ℝ}
    (hA : ∀ a ∈ W, ∀ b ∈ W, 0 ≤ A a b)
    (hrow : ∀ a ∈ W, ∑ b ∈ W, A a b ≤ C)
    (hcol : ∀ b ∈ W, ∑ a ∈ W, A a b ≤ C) :
    (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, A a b * (f b c * f c a)) ≤
      C * ∑ a ∈ W, ∑ b ∈ W, f a b ^ 2 := by
  have hleft :
      (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, A a b * f b c ^ 2) ≤
        C * ∑ b ∈ W, ∑ c ∈ W, f b c ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c hc
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hcol b hb) (sq_nonneg _)
  have hright :
      (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, A a b * f c a ^ 2) ≤
        C * ∑ a ∈ W, ∑ c ∈ W, f c a ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c hc
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow a ha) (sq_nonneg _)
  rw [Finset.sum_comm (f := fun a c => f c a ^ 2)] at hright
  have hpoint :
      (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, 2 * (A a b * (f b c * f c a))) ≤
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
        (A a b * f b c ^ 2 + A a b * f c a ^ 2) := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    apply Finset.sum_le_sum
    intro c hc
    have h := mul_nonneg (hA a ha b hb) (sq_nonneg (f b c - f c a))
    nlinarith
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hpoint
  simp only [← Finset.mul_sum] at hleft hright ⊢
  linarith

private theorem norm_sum3_le {ι : Type*} [DecidableEq ι]
    (W : Finset ι) (f : ι → ι → ι → ℂ) :
    ‖∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, f a b c‖ ≤
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ‖f a b c‖ := by
  calc
    _ ≤ ∑ a ∈ W, ‖∑ b ∈ W, ∑ c ∈ W, f a b c‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ W, ∑ b ∈ W, ‖∑ c ∈ W, f a b c‖ := by
      apply Finset.sum_le_sum
      intro a ha
      exact norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact norm_sum_le _ _

private theorem zeroLeg_le
    {a b R : ℝ} (hR : 0 < R) (hsep : a ≠ b → R ≤ |a - b|) (j : ℕ) :
    ‖sourceHhat (a - b) 0‖ ≤
      (if a = b then lemma43DerivativeConstant 0 else 0) +
        s1VerticalConstant j / (R / (2 * Real.pi)) ^ j := by
  have hC : 0 ≤ s1VerticalConstant j / (R / (2 * Real.pi)) ^ j := by
    exact div_nonneg (s1VerticalConstant_nonneg j) (by positivity)
  by_cases hab : a = b
  · simpa [hab] using (norm_sourceHhat_le_fixed (a - b) 0).trans
      (le_add_of_nonneg_right hC)
  · simp only [hab, if_false, zero_add]
    have h := norm_sourceHhat_zero_le_div (a - b) j (sub_ne_zero.mpr hab)
    change ‖sourceHhat (a - b) 0‖ ≤ _
    apply h.trans
    change s1VerticalConstant j / |(a - b) / (2 * Real.pi)| ^ j ≤ _
    apply div_le_div_of_nonneg_left (s1VerticalConstant_nonneg j) (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact div_le_div_of_nonneg_right (hsep hab) (by positivity)

/-- The zero-frequency leg has an explicit uniform Schur budget. -/
theorem sourceZeroFourier_row_le
    {W : Finset ℝ} {R : ℝ} (hR : 0 < R)
    (hsep : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → R ≤ |a - b|)
    {a : ℝ} (ha : a ∈ W) (j : ℕ) :
    (∑ b ∈ W, ‖sourceHhat (a - b) 0‖) ≤
      lemma43DerivativeConstant 0 + (W.card : ℝ) *
        (s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) := by
  calc
    _ ≤ ∑ b ∈ W, ((if a = b then lemma43DerivativeConstant 0 else 0) +
        s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) :=
      Finset.sum_le_sum fun b hb => zeroLeg_le hR (hsep a ha b hb) j
    _ = _ := by simp [Finset.sum_add_distrib, ha]

/-- Exact Section-6 starting estimate, retaining the full Fourier pair moment.
The only hypotheses are positivity and the literal ordinate separation. -/
theorem norm_sourceS2_le_pairMoment
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) {R : ℝ} (hR : 0 < R)
    (hsep : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → R ≤ |a - b|) (j : ℕ) :
    ‖sourceS2 N W‖ ≤
      3 * (N : ℝ) ^ 3 *
        (lemma43DerivativeConstant 0 + (W.card : ℝ) *
          (s1VerticalConstant j / (R / (2 * Real.pi)) ^ j)) *
        sourceNonzeroFourierPairMoment N W := by
  rw [sourceS2_eq_three_nonzeroFourier_plane hN W, norm_mul]
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  rw [show ‖(3 : ℂ)‖ = (3 : ℝ) by norm_num]
  rw [mul_assoc (3 * (N : ℝ) ^ 3)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum3_le W _).trans
  simp only [norm_mul, mul_assoc]
  apply weighted_cycle_le_pairMoment W
    (fun a b => ‖sourceHhat (a - b) 0‖)
    (fun a b => ‖sourceNonzeroFourier N (a - b)‖)
  · intro a ha b hb
    exact norm_nonneg _
  · intro a ha
    exact sourceZeroFourier_row_le hR hsep ha j
  · intro b hb
    calc
      _ ≤ ∑ a ∈ W, ((if a = b then lemma43DerivativeConstant 0 else 0) +
          s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) :=
        Finset.sum_le_sum fun a ha => zeroLeg_le hR (hsep a ha b hb) j
      _ = _ := by simp [Finset.sum_add_distrib, hb]

end
end GuthMaynardS2LiteralReduction

#print axioms GuthMaynardS2LiteralReduction.norm_sourceS2_le_pairMoment
