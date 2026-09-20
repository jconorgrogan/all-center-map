import FordBoundaryWeightedHolder

open scoped BigOperators

noncomputable section
namespace FordBilinearWeightedHolder

/-- Exact finite weighted Hölder bound for a complex bilinear phase. The
weights are natural multiplicities; replication by `Fin (n c)` keeps the
outer moment factor exact. -/
theorem weighted_complex_sum_holder
    {α : Type*} [Fintype α]
    (n : α → ℕ) (F : α → ℂ) {s : ℕ} (hs : 1 ≤ s) :
    ‖∑ c, (n c : ℂ) * F c‖ ^ (2 * s) ≤
      (∑ c, (n c : ℝ)) ^ (2 * s - 2) *
        (∑ c, (n c : ℝ) ^ 2) *
        ∑ c, ‖F c‖ ^ (2 * s) := by
  classical
  let A := Σ c, Fin (n c)
  let g : A → ℝ := fun a => ‖F a.1‖
  have hnorm : ‖∑ c, (n c : ℂ) * F c‖ ≤
      ∑ c, (n c : ℝ) * ‖F c‖ := by
    calc
      ‖∑ c, (n c : ℂ) * F c‖ ≤ ∑ c, ‖(n c : ℂ) * F c‖ := norm_sum_le _ _
      _ = ∑ c, (n c : ℝ) * ‖F c‖ := by
        apply Finset.sum_congr rfl
        intro c hc
        simp
  have hmass : Fintype.card A = ∑ c, n c := by
    dsimp [A]
    simp [Fintype.card_sigma]
  have hsum : (∑ a : A, g a) = ∑ c, (n c : ℝ) * ‖F c‖ := by
    dsimp [g]
    rw [Fintype.sum_sigma]
    simp
  have hsumPow : (∑ a : A, g a ^ s) =
      ∑ c, (n c : ℝ) * ‖F c‖ ^ s := by
    dsimp [g]
    rw [Fintype.sum_sigma]
    simp
  have hpow := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := (Finset.univ : Finset A)) (f := g) (p := (s : ℝ))
    (by exact_mod_cast hs) (fun a _ => norm_nonneg _)
  have hpow' : (∑ c, (n c : ℝ) * ‖F c‖) ^ s ≤
      (∑ c, (n c : ℝ)) ^ (s - 1) *
        ∑ c, (n c : ℝ) * ‖F c‖ ^ s := by
    have hexp : (s : ℝ) - 1 = ((s - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hs]
      norm_num
    simp only [hexp, Real.rpow_natCast, Finset.card_univ] at hpow
    rw [hsum, hsumPow, hmass] at hpow
    simpa only [Nat.cast_sum] using hpow
  have hsumNonneg : 0 ≤ ∑ c, (n c : ℝ) * ‖F c‖ :=
    Finset.sum_nonneg (fun c _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  have hpowSq : (∑ c, (n c : ℝ) * ‖F c‖) ^ (2 * s) ≤
      ((∑ c, (n c : ℝ)) ^ (s - 1) *
        ∑ c, (n c : ℝ) * ‖F c‖ ^ s) ^ 2 := by
    have := pow_le_pow_left₀ (pow_nonneg hsumNonneg s) hpow' 2
    simpa only [← pow_mul, Nat.mul_comm s 2] using this
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq
    (s := (Finset.univ : Finset α))
    (fun c => (n c : ℝ)) (fun c => ‖F c‖ ^ s)
  have hCauchy' :
      (∑ c, (n c : ℝ) * ‖F c‖ ^ s) ^ 2 ≤
        (∑ c, (n c : ℝ) ^ 2) * ∑ c, ‖F c‖ ^ (2 * s) := by
    simpa only [← pow_two, ← pow_mul, Nat.mul_comm s 2] using hCauchy
  calc
    ‖∑ c, (n c : ℂ) * F c‖ ^ (2 * s) ≤
        (∑ c, (n c : ℝ) * ‖F c‖) ^ (2 * s) :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm _
    _ ≤ ((∑ c, (n c : ℝ)) ^ (s - 1) *
        ∑ c, (n c : ℝ) * ‖F c‖ ^ s) ^ 2 := hpowSq
    _ ≤ (∑ c, (n c : ℝ)) ^ (2 * s - 2) *
        (∑ c, (n c : ℝ) ^ 2) * ∑ c, ‖F c‖ ^ (2 * s) := by
      have hmul := mul_le_mul_of_nonneg_left hCauchy'
        (show 0 ≤ (∑ c, (n c : ℝ)) ^ (2 * (s - 1)) from
          pow_nonneg (Finset.sum_nonneg (fun c _ => Nat.cast_nonneg (n c))) _)
      calc
        ((∑ c, (n c : ℝ)) ^ (s - 1) *
            ∑ c, (n c : ℝ) * ‖F c‖ ^ s) ^ 2 =
            (∑ c, (n c : ℝ)) ^ (2 * s - 2) *
              (∑ c, (n c : ℝ) * ‖F c‖ ^ s) ^ 2 := by
                rw [mul_pow, ← pow_mul]
                rw [show (s - 1) * 2 = 2 * s - 2 by omega]
        _ ≤ _ := by
          simpa only [show 2 * (s - 1) = 2 * s - 2 by omega, mul_assoc] using hmul

end FordBilinearWeightedHolder
#print axioms FordBilinearWeightedHolder.weighted_complex_sum_holder
