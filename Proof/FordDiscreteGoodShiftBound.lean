import FordDiscreteVdC

open scoped BigOperators ComplexConjugate
noncomputable section

namespace FordDiscreteGoodShiftBound

open FordDiscretePairCount FordDiscreteCorrelationDiagonal FordDiscreteVdC

/-- Conditional finite good/bad shift bound.  The supplied good-shift bound is
kept separate from the finite algebra: no estimate for `B` is assumed here. -/
theorem normalized_norm_sum_sq_le_good_bad
    {N H Q : ℕ} (hH : H ≤ N) (hQ : 1 ≤ Q) (hQN : Q ≤ N)
    (f : ℕ → ℂ) (hf : ∀ n ∈ Finset.range H, ‖f n‖ ≤ 1)
    (G : Finset ℕ) (hG : G ⊆ positiveRange Q)
    (B : ℝ) (hB : 0 ≤ B)
    (hgood : ∀ h ∈ G, ‖correlation H h f‖ ≤ B) :
    ‖∑ n ∈ Finset.range H, f n‖ ^ 2 / (N : ℝ) ^ 2 ≤
      2 / (Q : ℝ) +
        4 * (((positiveRange Q \ G).card : ℕ) : ℝ) / (Q : ℝ) +
        4 * B / (N : ℝ) := by
  let P : Finset ℕ := positiveRange Q
  let bad : Finset ℕ := P \ G
  have hQr : 0 < (Q : ℝ) := by
    exact_mod_cast (show 0 < Q by omega)
  have hNr : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hHr : (H : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hH
  have hcardP : P.card ≤ Q := by
    dsimp [P]
    calc
      (positiveRange Q).card ≤ (Finset.range Q).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = Q := Finset.card_range Q
  have hcardG : (G.card : ℝ) ≤ (Q : ℝ) := by
    have hn : G.card ≤ Q := (Finset.card_le_card hG).trans hcardP
    exact_mod_cast hn
  have hgood_sum :
      (∑ h ∈ G, ‖correlation H h f‖) ≤ (G.card : ℝ) * B := by
    calc
      (∑ h ∈ G, ‖correlation H h f‖) ≤ ∑ _h ∈ G, B := by
        apply Finset.sum_le_sum
        intro h hh
        exact hgood h hh
      _ = (G.card : ℝ) * B := by simp
  have hcorr_le (h : ℕ) : ‖correlation H h f‖ ≤ (H : ℝ) := by
    calc
      ‖correlation H h f‖ ≤ ((H - h : ℕ) : ℝ) :=
        correlation_norm_le f hf
      _ ≤ (H : ℝ) := by
        exact_mod_cast (Nat.sub_le H h)
  have hbad_sum :
      (∑ h ∈ bad, ‖correlation H h f‖) ≤ (bad.card : ℝ) * (H : ℝ) := by
    calc
      (∑ h ∈ bad, ‖correlation H h f‖) ≤ ∑ _h ∈ bad, (H : ℝ) := by
        apply Finset.sum_le_sum
        intro h hh
        exact hcorr_le h
      _ = (bad.card : ℝ) * (H : ℝ) := by simp
  have hdecomp :
      (∑ h ∈ P, ‖correlation H h f‖) =
        (∑ h ∈ G, ‖correlation H h f‖) +
          ∑ h ∈ bad, ‖correlation H h f‖ := by
    have hs := Finset.sum_sdiff hG (f := fun h => ‖correlation H h f‖)
    dsimp [P, bad] at hs ⊢
    linarith
  have hcorr_sum :
      (∑ h ∈ P, ‖correlation H h f‖) ≤
        (Q : ℝ) * B + (bad.card : ℝ) * (H : ℝ) := by
    rw [hdecomp]
    have hGB : (G.card : ℝ) * B ≤ (Q : ℝ) * B :=
      mul_le_mul_of_nonneg_right hcardG hB
    exact (add_le_add hgood_sum hbad_sum).trans (by
      linarith [hGB])
  have hv := vdc_bound hH hQ hQN f hf
  have hv' :
      ‖∑ n ∈ Finset.range H, f n‖ ^ 2 ≤
        2 * (N : ℝ) ^ 2 / (Q : ℝ) +
          4 * (N : ℝ) / (Q : ℝ) *
            ((Q : ℝ) * B + (bad.card : ℝ) * (H : ℝ)) := by
    calc
      ‖∑ n ∈ Finset.range H, f n‖ ^ 2 ≤
          2 * (N : ℝ) ^ 2 / (Q : ℝ) +
            4 * (N : ℝ) / (Q : ℝ) *
              ∑ h ∈ P, ‖correlation H h f‖ := by
        simpa [P] using hv
      _ ≤ 2 * (N : ℝ) ^ 2 / (Q : ℝ) +
          4 * (N : ℝ) / (Q : ℝ) *
            ((Q : ℝ) * B + (bad.card : ℝ) * (H : ℝ)) := by
        have hc : 0 ≤ 4 * (N : ℝ) / (Q : ℝ) := by positivity
        have hm := mul_le_mul_of_nonneg_left hcorr_sum hc
        linarith
  have hinner :
      (Q : ℝ) * B + (bad.card : ℝ) * (H : ℝ) ≤
        (Q : ℝ) * B + (bad.card : ℝ) * (N : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hHr (Nat.cast_nonneg bad.card)
    linarith
  have hE :
      ‖∑ n ∈ Finset.range H, f n‖ ^ 2 ≤
        2 * (N : ℝ) ^ 2 / (Q : ℝ) +
          4 * (N : ℝ) / (Q : ℝ) *
            ((Q : ℝ) * B + (bad.card : ℝ) * (N : ℝ)) := by
    have hc : 0 ≤ 4 * (N : ℝ) / (Q : ℝ) := by positivity
    have hm := mul_le_mul_of_nonneg_left hinner hc
    linarith
  apply (div_le_iff₀ (sq_pos_of_pos hNr)).2
  calc
    ‖∑ n ∈ Finset.range H, f n‖ ^ 2 ≤
        2 * (N : ℝ) ^ 2 / (Q : ℝ) +
          4 * (N : ℝ) / (Q : ℝ) *
            ((Q : ℝ) * B + (bad.card : ℝ) * (N : ℝ)) := hE
    _ = (2 / (Q : ℝ) + 4 * (bad.card : ℝ) / (Q : ℝ) +
        4 * B / (N : ℝ)) * (N : ℝ) ^ 2 := by
      field_simp [ne_of_gt hQr, ne_of_gt hNr]
      ring

end FordDiscreteGoodShiftBound

#print axioms FordDiscreteGoodShiftBound.normalized_norm_sum_sq_le_good_bad
