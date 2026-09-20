import Mathlib

/-!
# Finite algebra behind Appendix A.7--A.13

This file deliberately does **not** assert a large-values estimate.  It certifies
the premise-free algebra used before invoking Guth--Maynard: character twists
survive taking a bounded power, product support remains in the advertised
multiplicative interval, normalization preserves the coefficient bound, and the
two rational exponent comparisons at the end of the Type-I argument are exact.
-/

namespace AppendixTypeIPower

open scoped BigOperators

noncomputable section

/-! ## The character twist survives a bounded power -/

/-- Complete multiplicativity is exactly the identity needed when the
coefficient of a product tuple is regrouped by its product. -/
theorem character_twist_of_tuple
    {k : ℕ} (χ : ℕ →* ℂ) (x : Fin k → ℕ) :
    ∏ i, χ (x i) = χ (∏ i, x i) := by
  simpa using (χ.map_prod x Finset.univ)

/-- The coefficient part and the character part of a product tuple separate
without any positivity or reality hypothesis on the coefficients. -/
theorem coefficient_character_factorization
    {k : ℕ} (χ : ℕ →* ℂ) (a : ℕ → ℂ) (x : Fin k → ℕ) :
    ∏ i, (a (x i) * χ (x i)) =
      (∏ i, a (x i)) * χ (∏ i, x i) := by
  rw [Finset.prod_mul_distrib, character_twist_of_tuple]

/-! ## Support after taking a power -/

/-- If every factor lies in `(N,2N]`, the product tuple lies in
`(N^k,(2N)^k]`.  The strict lower endpoint needs `k > 0`, exactly as in the
power argument. -/
theorem product_tuple_mem_power_interval
    {k N : ℕ} (hk : 0 < k) (hN : 0 < N) (x : Fin k → ℕ)
    (hlow : ∀ i, N < x i) (hhigh : ∀ i, x i ≤ 2 * N) :
    N ^ k < ∏ i, x i ∧ ∏ i, x i ≤ (2 * N) ^ k := by
  have huniv : (Finset.univ : Finset (Fin k)).Nonempty := by
    simpa using (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hk))
  constructor
  · simpa using Finset.prod_lt_prod_of_nonempty
      (s := (Finset.univ : Finset (Fin k)))
      (fun _ _ ↦ hN) (fun i _ ↦ hlow i) huniv
  · simpa using Finset.prod_le_prod'
      (s := (Finset.univ : Finset (Fin k))) (fun i _ ↦ hhigh i)

/-! ## Coefficient normalization -/

/-- Dividing by a positive uniform coefficient majorant and multiplying by a
weight of norm at most one leaves coefficients in the unit ball. -/
theorem normalized_coefficient_norm_le_one
    (c w : ℂ) (C : ℝ) (hC : 0 < C)
    (hc : ‖c‖ ≤ C) (hw : ‖w‖ ≤ 1) :
    ‖c * w / (C : ℂ)‖ ≤ 1 := by
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
  have hmul : ‖c‖ * ‖w‖ ≤ C * 1 :=
    mul_le_mul hc hw (norm_nonneg w) (le_of_lt hC)
  exact (div_le_iff₀' hC).2 (by simpa using hmul)

/-! ## Triangle/pigeonhole step for the powered polynomial -/

/-- If a sum of `k` dyadic block values is large, one block carries at least
the `1/k` share used in the appendix's triangle-and-pigeonhole argument. -/
theorem exists_block_with_large_norm
    {k : ℕ} (hk : 0 < k) (f : Fin k → ℂ) :
    ∃ i, ‖∑ j, f j‖ ≤ (k : ℝ) * ‖f i‖ := by
  have huniv : (Finset.univ : Finset (Fin k)).Nonempty := by
    simpa using (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hk))
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have htriangle :
      ‖∑ j, f j‖ ≤ ∑ j, ‖f j‖ := by
    simpa using norm_sum_le (Finset.univ : Finset (Fin k)) f
  have hconstant :
      (∑ _j : Fin k, ‖∑ j, f j‖ / (k : ℝ)) = ‖∑ j, f j‖ := by
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp
  have hsum :
      (∑ _j : Fin k, ‖∑ j, f j‖ / (k : ℝ)) ≤ ∑ j, ‖f j‖ := by
    simpa [hconstant] using htriangle
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le huniv hsum
  refine ⟨i, ?_⟩
  have := mul_le_mul_of_nonneg_left hi (le_of_lt hkreal)
  field_simp at this ⊢
  exact this

/-! ## Exact exponent arithmetic -/

def gmCoefficient (σ : ℝ) : ℝ := 15 / (3 + 5 * σ)

def gmExponent (σ : ℝ) : ℝ := gmCoefficient σ * (1 - σ)

def poweredLengthLower (σ : ℝ) : ℝ := 10 / (6 + 10 * σ)

def poweredLengthUpper (σ : ℝ) : ℝ := 15 / (6 + 10 * σ)

def gmSwitchExponent (σ : ℝ) : ℝ :=
  15 * (1 - σ) / ((3 + 5 * σ) * (18 / 5 - 4 * σ))

/-! The next identities are the exponent bookkeeping in Guth--Maynard
Section 13.1.  They make explicit why the interval (13.1) and the switch at
`N^k = T^α` give the advertised exponent. -/

theorem first_term_at_powered_upper
    {σ : ℝ} (hσlow : 7 / 10 ≤ σ) :
    2 * poweredLengthUpper σ * (1 - σ) = gmExponent σ := by
  have hden₁ : 6 + 10 * σ ≠ 0 := by nlinarith
  have hden₂ : 3 + 5 * σ ≠ 0 := by nlinarith
  rw [poweredLengthUpper, gmExponent, gmCoefficient]
  field_simp
  ring

theorem third_term_at_powered_lower
    {σ : ℝ} (hσlow : 7 / 10 ≤ σ) :
    1 + (12 / 5 - 4 * σ) * poweredLengthLower σ = gmExponent σ := by
  have hden₁ : 6 + 10 * σ ≠ 0 := by nlinarith
  have hden₂ : 3 + 5 * σ ≠ 0 := by nlinarith
  rw [poweredLengthLower, gmExponent, gmCoefficient]
  field_simp
  ring

theorem middle_term_at_switch
    {σ : ℝ} (hσlow : 7 / 10 ≤ σ) (hσhigh : σ ≤ 4 / 5) :
    (18 / 5 - 4 * σ) * gmSwitchExponent σ = gmExponent σ := by
  have hden₁ : 3 + 5 * σ ≠ 0 := by nlinarith
  have hfactor : 18 / 5 - 4 * σ ≠ 0 := by nlinarith
  have hfactor' : 18 - 20 * σ ≠ 0 := by nlinarith
  have hrewrite : 18 / 5 - 4 * σ = (18 - 20 * σ) / 5 := by ring
  rw [gmSwitchExponent, gmExponent, gmCoefficient, hrewrite]
  field_simp [hden₁, hfactor, hfactor']

theorem mean_value_switch_le_gm
    {σ : ℝ} (hσlow : 7 / 10 ≤ σ) (hσhigh : σ ≤ 4 / 5) :
    1 + (1 - 2 * σ) * gmSwitchExponent σ ≤ gmExponent σ := by
  have hden₁ : 0 < 3 + 5 * σ := by nlinarith
  have hden₂ : 0 < 9 - 10 * σ := by nlinarith
  have hfactor : 18 / 5 - 4 * σ ≠ 0 := by nlinarith
  have hfactor' : 18 - 20 * σ ≠ 0 := by nlinarith
  have hfactor'' : 18 - σ * 20 ≠ 0 := by nlinarith
  have hden₂' : 9 - σ * 10 ≠ 0 := by nlinarith
  have hrewrite : 18 / 5 - 4 * σ = (18 - 20 * σ) / 5 := by ring
  have hid :
      gmExponent σ - (1 + (1 - 2 * σ) * gmSwitchExponent σ) =
        (250 * (σ - 3 / 4) ^ 2 + 3 / 8) /
          (2 * (3 + 5 * σ) * (9 - 10 * σ)) := by
    rw [gmSwitchExponent, gmExponent, gmCoefficient, hrewrite]
    field_simp [ne_of_gt hden₁, ne_of_gt hden₂, hfactor, hfactor', hfactor'', hden₂']
    ring
  rw [← sub_nonneg, hid]
  positivity

/-- On the Type-I strip, the Guth--Maynard coefficient is no larger than
`30/13`. -/
theorem gmCoefficient_le_uniformCoeff
    {σ : ℝ} (hσ : 7 / 10 ≤ σ) :
    gmCoefficient σ ≤ 30 / 13 := by
  have hden : 0 < 3 + 5 * σ := by nlinarith
  rw [gmCoefficient, div_le_iff₀ hden]
  nlinarith

/-- Hence the Type-I exponent is bounded by the desired uniform exponent. -/
theorem gmExponent_le_uniformExponent
    {σ : ℝ} (hσlow : 7 / 10 ≤ σ) (hσhigh : σ ≤ 4 / 5) :
    gmExponent σ ≤ (30 / 13) * (1 - σ) := by
  have hone : 0 ≤ 1 - σ := by nlinarith
  exact mul_le_mul_of_nonneg_right (gmCoefficient_le_uniformCoeff hσlow) hone

/-- The gap between the Type-II exponent coefficient `2` and the sharper
Type-I exponent is uniformly at least `1/35` on `[7/10,4/5]`.

This certifies the exact numerical claim following (A.13). -/
theorem gm_minus_two_margin
    {σ : ℝ} (hσlow : 7 / 10 ≤ σ) (hσhigh : σ ≤ 4 / 5) :
    (gmCoefficient σ - 2) * (1 - σ) ≥ 1 / 35 := by
  have hden : 0 < 3 + 5 * σ := by nlinarith
  have hleft : 5 * σ - 4 ≤ 0 := by nlinarith
  have hright : 35 * σ - 39 ≤ 0 := by nlinarith
  have hprod : 0 ≤ (5 * σ - 4) * (35 * σ - 39) :=
    mul_nonneg_of_nonpos_of_nonpos hleft hright
  have hid :
      (15 / (3 + 5 * σ) - 2) * (1 - σ) - 1 / 35 =
        2 * ((5 * σ - 4) * (35 * σ - 39)) / (35 * (3 + 5 * σ)) := by
    field_simp
    <;> ring
  rw [ge_iff_le, ← sub_nonneg, gmCoefficient, hid]
  positivity

end

end AppendixTypeIPower

#print axioms AppendixTypeIPower.character_twist_of_tuple
#print axioms AppendixTypeIPower.coefficient_character_factorization
#print axioms AppendixTypeIPower.product_tuple_mem_power_interval
#print axioms AppendixTypeIPower.normalized_coefficient_norm_le_one
#print axioms AppendixTypeIPower.exists_block_with_large_norm
#print axioms AppendixTypeIPower.first_term_at_powered_upper
#print axioms AppendixTypeIPower.third_term_at_powered_lower
#print axioms AppendixTypeIPower.middle_term_at_switch
#print axioms AppendixTypeIPower.mean_value_switch_le_gm
#print axioms AppendixTypeIPower.gmExponent_le_uniformExponent
#print axioms AppendixTypeIPower.gm_minus_two_margin
