import CGLProofDAG

/-!
# Exact source leaf for the discrete Dirichlet-polynomial mean value theorem

This staging file separates the classical analytic mean-square estimate from
the elementary large-value deduction used in Guth--Maynard Section 13.1.
It does not assert the source estimate.
-/

namespace DiscreteMeanValueSourceLeaf

open scoped BigOperators
open CGLProofDAG

noncomputable section

/-- Coefficient energy on the literal dyadic interval used by
`CGLProofDAG.dirichletPolynomial`. -/
def coefficientEnergy (b : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ^ 2

/-- The source-facing, epsilon-form discrete mean-square theorem.  This is the
analytic theorem behind the words "the usual Mean Value Theorem" in
Guth--Maynard Section 13.1.  It is defined as data and is not asserted here. -/
def DiscreteDirichletMeanSquare : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ N →
        OneSeparated W →
        (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
        (∑ t ∈ W, ‖dirichletPolynomial b N t‖ ^ 2) ≤
          C * Real.rpow T η * ((N : ℝ) + T) * coefficientEnergy b N

/-- Bounded coefficients have energy at most the exact cardinality of the
dyadic interval, hence at most `N`. -/
theorem coefficientEnergy_le
    {b : ℕ → ℂ} {N : ℕ} (hb : ∀ n, ‖b n‖ ≤ 1) :
    coefficientEnergy b N ≤ N := by
  unfold coefficientEnergy
  calc
    (∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ^ 2) ≤
        ∑ _n ∈ Finset.Ioc N (2 * N), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa using (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hb n)
    _ = (Finset.Ioc N (2 * N)).card := by simp
    _ = N := by simp <;> omega

/-- Chebyshev on the finite ordinate set.  This is the exact deterministic
deduction from a discrete mean-square estimate to a large-value count. -/
theorem card_mul_sq_le_sum
    {V : ℝ} {N : ℕ} {b : ℕ → ℂ} {W : Finset ℝ}
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖)
    (hV : 0 ≤ V) :
    (W.card : ℝ) * V ^ 2 ≤
      ∑ t ∈ W, ‖dirichletPolynomial b N t‖ ^ 2 := by
  calc
    (W.card : ℝ) * V ^ 2 = ∑ _t ∈ W, V ^ 2 := by simp
    _ ≤ ∑ t ∈ W, ‖dirichletPolynomial b N t‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      exact (sq_le_sq₀ hV (norm_nonneg _)).2 (hlarge t ht)

/-- The exact source theorem `DiscreteDirichletMeanSquare` implies the
large-value form used in the complementary branch of GM Section 13.1. -/
theorem discreteLargeValue_of_meanSquare
    (hmean : DiscreteDirichletMeanSquare) :
    ∀ η : ℝ, 0 < η →
      ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
        ∀ (T V : ℝ) (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ),
          T₀ ≤ T → 1 ≤ N → 0 < V →
          (∀ n, ‖b n‖ ≤ 1) →
          OneSeparated W →
          (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
          (∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖) →
          (W.card : ℝ) ≤
            C * Real.rpow T η * (((N : ℝ) ^ 2 + T * N) / V ^ 2) := by
  intro η hη
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ := hmean η hη
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T V N b W hT hN hV hb hsep hheight hlarge
  have hV2 : 0 < V ^ 2 := sq_pos_of_pos hV
  have hcard := card_mul_sq_le_sum hlarge hV.le
  have henergy := coefficientEnergy_le (N := N) hb
  have hmeanBound := hbound T N b W hT hN hsep hheight
  have hTnonneg : 0 ≤ T := by linarith
  have hTN : 0 ≤ (N : ℝ) + T := by positivity
  have hCpow : 0 ≤ C * Real.rpow T η :=
    mul_nonneg hC.le (Real.rpow_nonneg hTnonneg _)
  have hcombined :
      (W.card : ℝ) * V ^ 2 ≤
        C * Real.rpow T η * ((N : ℝ) + T) * N := by
    exact hcard.trans <| hmeanBound.trans <|
      mul_le_mul_of_nonneg_left henergy (mul_nonneg hCpow hTN)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hV2).2
  calc
    (W.card : ℝ) * V ^ 2 ≤
        C * Real.rpow T η * ((N : ℝ) + T) * N := hcombined
    _ = C * Real.rpow T η * ((N : ℝ) ^ 2 + T * N) := by ring

end
end DiscreteMeanValueSourceLeaf

#print axioms DiscreteMeanValueSourceLeaf.coefficientEnergy_le
#print axioms DiscreteMeanValueSourceLeaf.card_mul_sq_le_sum
#print axioms DiscreteMeanValueSourceLeaf.discreteLargeValue_of_meanSquare
