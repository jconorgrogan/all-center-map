import GuthMaynardGMPointwiseKernel

noncomputable section
namespace GuthMaynardDiscreteBandCount

/-- Literal finite packing bound for a decreasing phase in one resonance band. -/
theorem card_le_one_add_two_width_div_gap
    (s : Finset ℕ) (f : ℕ → ℝ) (c δ g : ℝ)
    (hg : 0 < g) (hδ : 0 ≤ δ)
    (hband : ∀ n ∈ s, |f n - c| ≤ δ)
    (hgap : ∀ a ∈ s, ∀ b ∈ s, a ≤ b →
      g * ((b : ℝ) - a) ≤ f a - f b) :
    (s.card : ℝ) ≤ 1 + 2 * δ / g := by
  classical
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    let b := s.max' hs
    have ha : a ∈ s := s.min'_mem hs
    have hb : b ∈ s := s.max'_mem hs
    have hab : a ≤ b := s.le_max' a ha
    have hsub : s ⊆ Finset.Icc a b := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨s.min'_le n hn, s.le_max' n hn⟩
    have hcard : s.card ≤ b + 1 - a := by
      simpa [Nat.card_Icc] using Finset.card_le_card hsub
    have hcardR : (s.card : ℝ) ≤ (b : ℝ) + 1 - a := by
      have hcast : (s.card : ℝ) ≤ ((b + 1 - a : ℕ) : ℝ) := by
        exact_mod_cast hcard
      simpa only [Nat.cast_sub (by omega : a ≤ b + 1), Nat.cast_add,
        Nat.cast_one] using hcast
    have hba := hgap a ha b hb hab
    have hfa := (abs_le.mp (hband a ha)).2
    have hfb := (abs_le.mp (hband b hb)).1
    have hspan : (b : ℝ) - a ≤ 2 * δ / g := by
      apply (le_div_iff₀ hg).2
      nlinarith
    linarith
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

end GuthMaynardDiscreteBandCount
#print axioms GuthMaynardDiscreteBandCount.card_le_one_add_two_width_div_gap
