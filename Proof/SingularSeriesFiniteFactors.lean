import FullMAP

/-!
# Finite local-factor part of the Hardy--Littlewood singular series

For a nonzero shift, only primes dividing its absolute value contribute to the
second Euler product in `PrimePairEndpoints.singularSeries`.  The product is
therefore a genuine finite product; this file proves that fact and identifies
the `tprod` with the literal divisor product.
-/

namespace PrimePairEndpoints

open scoped BigOperators

noncomputable section

def twinPrimeFactor (p : ℕ) : ℝ :=
  if p.Prime ∧ 2 < p then
    ((p : ℝ) * ((p : ℝ) - 2)) / ((p : ℝ) - 1) ^ 2
  else 1

def twinPrimeDeviation (p : ℕ) : ℝ := twinPrimeFactor p - 1

theorem twinPrimeFactor_eq_one_sub_inv_sq
    {p : ℕ} (hp : 2 < p) :
    ((p : ℝ) * ((p : ℝ) - 2)) / ((p : ℝ) - 1) ^ 2 =
      1 - (((p : ℝ) - 1) ^ 2)⁻¹ := by
  have hne : (p : ℝ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (ne_of_gt (lt_trans (by omega : 1 < (2 : ℕ)) hp))
  field_simp [hne]
  ring

theorem norm_twinPrimeDeviation_le (p : ℕ) :
    ‖twinPrimeDeviation p‖ ≤ 4 * (((p : ℝ) + 1) ^ 2)⁻¹ := by
  by_cases hp : p.Prime ∧ 2 < p
  · rw [twinPrimeDeviation, twinPrimeFactor, if_pos hp,
      twinPrimeFactor_eq_one_sub_inv_sq hp.2]
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
    have hden : 0 < (p : ℝ) - 1 := by linarith
    have hsum : 0 < (p : ℝ) + 1 := by linarith
    have hdev :
        (1 : ℝ) - (((p : ℝ) - 1) ^ 2)⁻¹ - 1 =
          -(((p : ℝ) - 1) ^ 2)⁻¹ := by ring
    rw [hdev, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    have hquot : 1 / (((p : ℝ) - 1) ^ 2) ≤
        4 / (((p : ℝ) + 1) ^ 2) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hden) (sq_pos_of_pos hsum)]
      nlinarith [sq_nonneg ((p : ℝ) - 3)]
    simpa only [one_div, div_eq_mul_inv, one_mul] using hquot
  · simp only [twinPrimeDeviation, twinPrimeFactor, if_neg hp, sub_self, norm_zero]
    positivity

theorem summable_norm_twinPrimeDeviation :
    Summable (fun p : ℕ => ‖twinPrimeDeviation p‖) := by
  have hs0 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr
        (Real.summable_nat_pow_inv.mpr (by omega : 1 < (2 : ℕ)))
  exact (hs0.mul_left (4 : ℝ)).of_norm_bounded (fun p => by
    simpa only [norm_norm] using
      norm_twinPrimeDeviation_le p)

theorem twinPrimeFactor_multipliable : Multipliable twinPrimeFactor := by
  have hmul : Multipliable (fun p : ℕ => 1 + twinPrimeDeviation p) :=
    multipliable_one_add_of_summable summable_norm_twinPrimeDeviation
  simpa [twinPrimeDeviation] using hmul

theorem twinPrimeEulerProduct_hasProd :
    HasProd twinPrimeFactor twinPrimeConstant := by
  have hdef : twinPrimeConstant = ∏' p : ℕ, twinPrimeFactor p := by
    rfl
  rw [hdef]
  exact twinPrimeFactor_multipliable.hasProd

theorem twinPrimeFactor_pos (p : ℕ) : 0 < twinPrimeFactor p := by
  by_cases hp : p.Prime ∧ 2 < p
  · rw [twinPrimeFactor, if_pos hp]
    have hpR : (2 : ℝ) < p := by exact_mod_cast hp.2
    exact div_pos (mul_pos (by positivity) (sub_pos.mpr hpR))
      (sq_pos_of_pos (by linarith))
  · simp [twinPrimeFactor, hp]

theorem twinPrimeConstant_ne_zero : twinPrimeConstant ≠ 0 := by
  have hfactor : ∀ p : ℕ, 1 + twinPrimeDeviation p ≠ 0 := by
    intro p
    have hpos := twinPrimeFactor_pos p
    simpa [twinPrimeDeviation] using ne_of_gt hpos
  have hprod := tprod_one_add_ne_zero_of_summable hfactor
    summable_norm_twinPrimeDeviation
  simpa [twinPrimeConstant, twinPrimeFactor, twinPrimeDeviation] using hprod

theorem twinPrimeConstant_pos : 0 < twinPrimeConstant := by
  have hnonneg : 0 ≤ twinPrimeConstant := by
    apply ge_of_tendsto twinPrimeEulerProduct_hasProd
    exact Filter.Eventually.of_forall (fun s =>
      Finset.prod_nonneg (fun p _ => (twinPrimeFactor_pos p).le))
  exact lt_of_le_of_ne hnonneg (Ne.symm twinPrimeConstant_ne_zero)

def singularLocalFactor (h : {z : ℤ // z ≠ 0}) (p : ℕ) : ℝ :=
  if p.Prime ∧ 2 < p ∧ (p : ℤ) ∣ h.1 then
    ((p : ℝ) - 1) / ((p : ℝ) - 2)
  else 1

theorem singularLocalFactor_pos
    (h : {z : ℤ // z ≠ 0}) (p : ℕ) :
    0 < singularLocalFactor h p := by
  by_cases hp : p.Prime ∧ 2 < p ∧ (p : ℤ) ∣ h.1
  · rw [singularLocalFactor, if_pos hp]
    have hpR : (2 : ℝ) < p := by exact_mod_cast hp.2.1
    exact div_pos (by linarith) (by linarith)
  · simp [singularLocalFactor, hp]

theorem singularLocalFactor_eq_one_of_not_mem_divisors
    (h : {z : ℤ // z ≠ 0}) (p : ℕ)
    (hp : p ∉ h.1.natAbs.divisors) :
    singularLocalFactor h p = 1 := by
  rw [singularLocalFactor]
  split_ifs with hfactor
  · have hdivNat : p ∣ h.1.natAbs := Int.natCast_dvd.mp hfactor.2.2
    exact (hp (Nat.mem_divisors.mpr ⟨hdivNat, Int.natAbs_ne_zero.mpr h.2⟩)).elim
  · rfl

theorem singularLocalFactor_multipliable
    (h : {z : ℤ // z ≠ 0}) :
    Multipliable (singularLocalFactor h) := by
  exact multipliable_of_ne_finset_one
    (s := h.1.natAbs.divisors)
    (singularLocalFactor_eq_one_of_not_mem_divisors h)

theorem singularLocalFactor_tprod_eq_divisors_prod
    (h : {z : ℤ // z ≠ 0}) :
    (∏' p : ℕ, singularLocalFactor h p) =
      ∏ p ∈ h.1.natAbs.divisors, singularLocalFactor h p := by
  exact tprod_eq_prod
    (s := h.1.natAbs.divisors)
    (singularLocalFactor_eq_one_of_not_mem_divisors h)

theorem singularSeries_eq_finite_divisor_product
    (h : {z : ℤ // z ≠ 0}) :
    singularSeries h =
      if (2 : ℤ) ∣ h.1 then
        2 * twinPrimeConstant *
          ∏ p ∈ h.1.natAbs.divisors, singularLocalFactor h p
      else 0 := by
  rw [singularSeries]
  split_ifs
  · congr 1
    exact singularLocalFactor_tprod_eq_divisors_prod h
  · rfl

theorem singularSeries_pos_of_even
    (h : {z : ℤ // z ≠ 0}) (heven : (2 : ℤ) ∣ h.1) :
    0 < singularSeries h := by
  rw [singularSeries_eq_finite_divisor_product, if_pos heven]
  exact mul_pos (mul_pos (by norm_num) twinPrimeConstant_pos)
    (Finset.prod_pos fun p _ => singularLocalFactor_pos h p)

end

end PrimePairEndpoints
