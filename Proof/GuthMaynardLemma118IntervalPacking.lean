import Mathlib

/-!
# The one-dimensional packing step behind Guth--Maynard Lemma 11.8

This file isolates the deterministic geometry used after rational fractions have
been shown to be separated.  It contains no analytic-number-theory premise.
-/

open scoped BigOperators

namespace GuthMaynardLemma118

/-- A finite `δ`-separated subset of `[a,a+L]` occupies distinct integer
`δ`-bins and hence has at most `⌊L/δ⌋₊+1` elements. -/
theorem card_le_natFloor_div_add_one
    (S : Finset ℝ) (a L δ : ℝ)
    (hδ : 0 < δ) (hL : 0 ≤ L)
    (hmem : ∀ x ∈ S, a ≤ x ∧ x ≤ a + L)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    S.card ≤ ⌊L / δ⌋₊ + 1 := by
  let bin : ℝ → ℕ := fun x => ⌊(x - a) / δ⌋₊
  have hbin_inj : Set.InjOn bin (↑S : Set ℝ) := by
    intro x hx y hy heq
    have hxS : x ∈ S := by simpa using hx
    have hyS : y ∈ S := by simpa using hy
    have hxu0 : 0 ≤ (x - a) / δ := div_nonneg (sub_nonneg.mpr (hmem x hxS).1) hδ.le
    have hyu0 : 0 ≤ (y - a) / δ := div_nonneg (sub_nonneg.mpr (hmem y hyS).1) hδ.le
    have hxl : (bin x : ℝ) ≤ (x - a) / δ := by
      simpa [bin] using (Nat.floor_le hxu0)
    have hyl : (bin y : ℝ) ≤ (y - a) / δ := by
      simpa [bin] using (Nat.floor_le hyu0)
    have hxu : (x - a) / δ < (bin x : ℝ) + 1 := by
      simpa [bin] using (Nat.lt_floor_add_one ((x - a) / δ))
    have hyu : (y - a) / δ < (bin y : ℝ) + 1 := by
      simpa [bin] using (Nat.lt_floor_add_one ((y - a) / δ))
    have hxy_div : (x - y) / δ < 1 := by
      rw [heq] at hxu
      have : (x - a) / δ - (y - a) / δ < 1 := by linarith
      convert this using 1 <;> ring
    have hyx_div : (y - x) / δ < 1 := by
      rw [← heq] at hyu
      have : (y - a) / δ - (x - a) / δ < 1 := by linarith
      convert this using 1 <;> ring
    have hxy : x - y < δ := (div_lt_one hδ).mp hxy_div
    have hyx : y - x < δ := (div_lt_one hδ).mp hyx_div
    by_contra hne
    have := hsep x hxS y hyS hne
    have habs : |x - y| < δ := abs_lt.mpr ⟨by linarith, hxy⟩
    exact (not_lt_of_ge this) habs
  have himage_card : (S.image bin).card = S.card :=
    Finset.card_image_iff.mpr hbin_inj
  have himage_subset : S.image bin ⊆ Finset.range (⌊L / δ⌋₊ + 1) := by
    rw [Finset.image_subset_iff]
    intro x hx
    have hx_upper : (x - a) / δ ≤ L / δ := by
      apply (div_le_div_iff_of_pos_right hδ).2
      linarith [(hmem x hx).2]
    have hfloor : bin x ≤ ⌊L / δ⌋₊ := by
      simpa [bin] using Nat.floor_mono hx_upper
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hfloor)
  rw [← himage_card, ← Finset.card_range (⌊L / δ⌋₊ + 1)]
  exact Finset.card_le_card himage_subset

/-- Real-valued form of the same packing bound. -/
theorem card_cast_le_one_add_div
    (S : Finset ℝ) (a L δ : ℝ)
    (hδ : 0 < δ) (hL : 0 ≤ L)
    (hmem : ∀ x ∈ S, a ≤ x ∧ x ≤ a + L)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (S.card : ℝ) ≤ 1 + L / δ := by
  have hn := card_le_natFloor_div_add_one S a L δ hδ hL hmem hsep
  have hq0 : 0 ≤ L / δ := div_nonneg hL hδ.le
  have hfloor : (⌊L / δ⌋₊ : ℝ) ≤ L / δ := Nat.floor_le hq0
  have hnR : (S.card : ℝ) ≤ (⌊L / δ⌋₊ : ℝ) + 1 := by exact_mod_cast hn
  linarith

/-- Indexed form used for the rational fractions in Lemma 11.8.  Once the
fraction map is injective and its values have the arithmetic separation, the
packing loss is exactly `⌊L/δ⌋₊+1`. -/
theorem card_le_natFloor_div_add_one_of_injective_map
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ) (a L δ : ℝ)
    (hδ : 0 < δ) (hL : 0 ≤ L)
    (hinj : Set.InjOn f (↑S : Set ι))
    (hmem : ∀ i ∈ S, a ≤ f i ∧ f i ≤ a + L)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |f i - f j|) :
    S.card ≤ ⌊L / δ⌋₊ + 1 := by
  have hcard : (S.image f).card = S.card := Finset.card_image_iff.mpr hinj
  rw [← hcard]
  apply card_le_natFloor_div_add_one (S.image f) a L δ hδ hL
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i hi
  · intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact hsep i hi j hj (fun hij => hxy (congrArg f hij))

#print axioms GuthMaynardLemma118.card_le_natFloor_div_add_one
#print axioms GuthMaynardLemma118.card_le_natFloor_div_add_one_of_injective_map

end GuthMaynardLemma118
