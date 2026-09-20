import GuthMaynardS3Assembly
import GuthMaynardLemma118IntervalPacking

/-!
# Rational-window packing for Guth--Maynard Lemma 11.8

This weld combines the already certified determinant separation of two natural
fractions with the exact one-dimensional interval-packing theorem.  The
cross-product hypothesis is the reduced-fraction distinctness condition used
in the source.
-/

namespace GuthMaynardLemma118

open GuthMaynardS3Source

/-- Fractions with denominators at most `B`, lying in one interval of length
`L`, and with distinct cross-products have cardinality at most
`⌊L B²⌋₊ + 1`. -/
theorem fraction_card_le_natFloor_length_mul_sq_add_one
    (P : Finset (ℕ × ℕ)) (a L B : ℝ)
    (hB : 0 < B) (hL : 0 ≤ L)
    (hden : ∀ p ∈ P, 0 < p.2 ∧ (p.2 : ℝ) ≤ B)
    (hwindow : ∀ p ∈ P,
      a ≤ (p.1 : ℝ) / (p.2 : ℝ) ∧
        (p.1 : ℝ) / (p.2 : ℝ) ≤ a + L)
    (hcross : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      p.1 * q.2 ≠ q.1 * p.2) :
    P.card ≤ ⌊L * B ^ 2⌋₊ + 1 := by
  let frac : ℕ × ℕ → ℝ := fun p => (p.1 : ℝ) / (p.2 : ℝ)
  let δ : ℝ := 1 / B ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → δ ≤ |frac p - frac q| := by
    intro p hp q hq hpq
    exact distinct_nat_fraction_separation_of_denominator_le
      (hden p hp).1 (hden q hq).1 hB
      (hden p hp).2 (hden q hq).2 (hcross p hp q hq hpq)
  have hinj : Set.InjOn frac (↑P : Set (ℕ × ℕ)) := by
    intro p hp q hq heq
    have hpP : p ∈ P := by simpa using hp
    have hqP : q ∈ P := by simpa using hq
    by_contra hpq
    have hs := hsep p hpP q hqP hpq
    rw [heq, sub_self, abs_zero] at hs
    exact (not_le_of_gt hδ) hs
  have hpack := card_le_natFloor_div_add_one_of_injective_map
    P frac a L δ hδ hL hinj (by
      intro p hp
      simpa [frac] using hwindow p hp) hsep
  have hscale : L / δ = L * B ^ 2 := by
    dsimp [δ]
    field_simp
  simpa [hscale] using hpack

/-- Literal `1/T`-collar count from Lemma 11.8.  The harmless factor `2`
records that `|v-r| ≤ 1/T` is an interval of total length `2/T`. -/
theorem fraction_card_in_inverse_time_collar_le
    (P : Finset (ℕ × ℕ)) (v N d T : ℝ)
    (hN : 0 < N) (hd : 0 < d) (hT : 0 < T)
    (hden : ∀ p ∈ P, 0 < p.2 ∧ (p.2 : ℝ) ≤ N / d)
    (hcollar : ∀ p ∈ P,
      |(p.1 : ℝ) / (p.2 : ℝ) - v| ≤ 1 / T)
    (hcross : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      p.1 * q.2 ≠ q.1 * p.2) :
    P.card ≤ ⌊(2 / T) * (N / d) ^ 2⌋₊ + 1 := by
  apply fraction_card_le_natFloor_length_mul_sq_add_one
    P (v - 1 / T) (2 / T) (N / d)
    (div_pos hN hd) (by positivity) hden
  · intro p hp
    have hc := (abs_le.mp (hcollar p hp))
    have hright : v - 1 / T + 2 / T = v + 1 / T := by ring
    constructor
    · linarith
    · rw [hright]
      linarith
  · exact hcross

#print axioms GuthMaynardLemma118.fraction_card_le_natFloor_length_mul_sq_add_one
#print axioms GuthMaynardLemma118.fraction_card_in_inverse_time_collar_le

end GuthMaynardLemma118
