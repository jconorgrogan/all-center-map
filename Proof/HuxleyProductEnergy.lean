import HuxleyHalaszFront

/-!
# Huxley 1975 Lemma 3: product-polynomial energy

This file proves the finite convolution-energy estimate used in equations
(3.8)--(3.10) of Huxley's proof of Theorem 1.  It is independent of the
reflection estimate and zero-density machinery.
-/

namespace MAPHuxleyProductEnergy

open scoped BigOperators

noncomputable section

/-- The collected coefficient of a product of two finite Dirichlet
polynomials. -/
def productCoefficient
    (A B : Finset ℕ) (a b : ℕ → ℂ) (r : ℕ) : ℂ :=
  ∑ p ∈ (A.product B).filter (fun p => p.1 * p.2 = r), a p.1 * b p.2

/-- The finite set of products on which the collected coefficient can be
nonzero. -/
def productSupport (A B : Finset ℕ) : Finset ℕ :=
  (A.product B).image (fun p => p.1 * p.2)

/-- Cauchy's inequality on one multiplicative fiber. -/
theorem norm_productCoefficient_sq_le
    (A B : Finset ℕ) (a b : ℕ → ℂ) (r : ℕ) :
    ‖productCoefficient A B a b r‖ ^ 2 ≤
      (((A.product B).filter (fun p => p.1 * p.2 = r)).card : ℝ) *
        ∑ p ∈ (A.product B).filter (fun p => p.1 * p.2 = r),
          ‖a p.1 * b p.2‖ ^ 2 := by
  let fiber := (A.product B).filter (fun p => p.1 * p.2 = r)
  have htriangle :
      ‖productCoefficient A B a b r‖ ≤ ∑ p ∈ fiber, ‖a p.1 * b p.2‖ := by
    simpa [productCoefficient, fiber] using
      norm_sum_le fiber (fun p => a p.1 * b p.2)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := fiber) (f := fun p => ‖a p.1 * b p.2‖)
  exact hsq.trans (by simpa [fiber] using hCS)

/-- Huxley's Lemma 3 for a product of two polynomials: if every product
fiber has at most `Delta` representations, the energy of the collected
coefficients is at most `Delta` times the product of the two input energies.
-/
theorem sum_norm_productCoefficient_sq_le
    (A B : Finset ℕ) (a b : ℕ → ℂ) (Delta : ℕ)
    (hDelta : ∀ r ∈ productSupport A B,
      ((A.product B).filter (fun p => p.1 * p.2 = r)).card ≤ Delta) :
    ∑ r ∈ productSupport A B, ‖productCoefficient A B a b r‖ ^ 2 ≤
      (Delta : ℝ) *
        (∑ m ∈ A, ‖a m‖ ^ 2) * (∑ n ∈ B, ‖b n‖ ^ 2) := by
  let pairs := A.product B
  let prodMap : ℕ × ℕ → ℕ := fun p => p.1 * p.2
  have hfiber (r : ℕ) (hr : r ∈ productSupport A B) :
      ‖productCoefficient A B a b r‖ ^ 2 ≤
        (Delta : ℝ) *
          ∑ p ∈ pairs.filter (fun p => prodMap p = r),
            ‖a p.1 * b p.2‖ ^ 2 := by
    have hbase := norm_productCoefficient_sq_le A B a b r
    have hcard :
        ((((A.product B).filter (fun p => p.1 * p.2 = r)).card : ℕ) : ℝ) ≤
          (Delta : ℝ) := by
      exact_mod_cast hDelta r hr
    have hsum : 0 ≤
        ∑ p ∈ pairs.filter (fun p => prodMap p = r),
          ‖a p.1 * b p.2‖ ^ 2 := by positivity
    apply hbase.trans
    simpa [pairs, prodMap] using
      (mul_le_mul_of_nonneg_right hcard hsum)
  calc
    ∑ r ∈ productSupport A B, ‖productCoefficient A B a b r‖ ^ 2 ≤
        ∑ r ∈ productSupport A B,
          (Delta : ℝ) *
            ∑ p ∈ pairs.filter (fun p => prodMap p = r),
              ‖a p.1 * b p.2‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      exact hfiber r hr
    _ = (Delta : ℝ) *
        ∑ r ∈ productSupport A B,
          ∑ p ∈ pairs.filter (fun p => prodMap p = r),
            ‖a p.1 * b p.2‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ = (Delta : ℝ) *
        ∑ p ∈ pairs, ‖a p.1 * b p.2‖ ^ 2 := by
      congr 1
      exact Finset.sum_fiberwise_of_maps_to
        (s := pairs) (t := productSupport A B) (g := prodMap)
        (fun p hp => by
          simp only [productSupport, prodMap, Finset.mem_image]
          exact ⟨p, hp, rfl⟩)
        (fun p => ‖a p.1 * b p.2‖ ^ 2)
    _ = (Delta : ℝ) *
        (∑ m ∈ A, ‖a m‖ ^ 2) * (∑ n ∈ B, ‖b n‖ ^ 2) := by
      dsimp [pairs]
      rw [Finset.sum_product]
      simp_rw [norm_mul, mul_pow]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

end


end MAPHuxleyProductEnergy

#print axioms MAPHuxleyProductEnergy.norm_productCoefficient_sq_le
#print axioms MAPHuxleyProductEnergy.sum_norm_productCoefficient_sq_le
