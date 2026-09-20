import FordBoundaryWeightedHolder

open scoped BigOperators

namespace FordLemma33WeightedHolder

open FordBoundaryWeightedHolder

noncomputable section

theorem weighted_moment_interpolation
    {α : Type*} [Fintype α] [Nonempty α]
    (w a : α → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hw : ∀ x, 0 ≤ w x) (ha : ∀ x, 0 ≤ a x) :
    (fordAvg (fun x => w x * a x ^ (k - 1))) ^ k ≤
      (fordAvg (fun x => w x * a x ^ k)) ^ (k - 1) * fordAvg w := by
  by_cases hk1 : k = 1
  · subst k
    simp
  have hk2 : 2 ≤ k := by omega
  let n : ℝ := k
  let p : ℝ := n / (n - 1)
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast (show 0 < k by omega)
  have hnmpos : 0 < n - 1 := by
    dsimp [n]
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    linarith
  have hp : 1 ≤ p := by
    dsimp [p]
    apply (le_div_iff₀ hnmpos).2
    linarith
  have hmul : ((k - 1 : ℕ) : ℝ) * p = n := by
    dsimp [n, p]
    rw [Nat.cast_sub (by omega)]
    norm_num
    have hden : (k : ℝ) - 1 ≠ 0 := by linarith
    rw [div_eq_mul_inv]
    calc
      ((k : ℝ) - 1) * ((k : ℝ) * ((k : ℝ) - 1)⁻¹) =
          (k : ℝ) * (((k : ℝ) - 1) * ((k : ℝ) - 1)⁻¹) := by ring
      _ = (k : ℝ) := by rw [mul_inv_cancel₀ hden, mul_one]
  have hcompact := Real.compact_inner_le_weight_mul_Lp_of_nonneg
    (s := (Finset.univ : Finset α)) (p := p) hp
    (w := w) (f := fun x => a x ^ (k - 1)) hw
    (fun x => pow_nonneg (ha x) _)
  have hpow (x : α) :
      (a x ^ (k - 1)) ^ p = a x ^ k := by
    calc
      (a x ^ (k - 1)) ^ p =
          (a x ^ ((k - 1 : ℕ) : ℝ)) ^ p := by
            rw [Real.rpow_natCast]
      _ = a x ^ (((k - 1 : ℕ) : ℝ) * p) := by
            rw [← Real.rpow_mul (ha x)]
      _ = a x ^ n := by rw [hmul]
      _ = a x ^ k := by
        dsimp [n]
        rw [Real.rpow_natCast]
  simp_rw [hpow] at hcompact
  change fordAvg (fun x => w x * a x ^ (k - 1)) ≤
    fordAvg w ^ (1 - p⁻¹) *
      fordAvg (fun x => w x * a x ^ k) ^ p⁻¹ at hcompact
  have hLam : 1 - p⁻¹ = 1 / (k : ℝ) := by
    dsimp [p, n]
    have hden : (k : ℝ) - 1 ≠ 0 := by linarith
    field_simp [hden]
    ring
  have hMu : p⁻¹ = ((k - 1 : ℕ) : ℝ) / k := by
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    dsimp [p, n]
    rw [hcast]
    field_simp
  rw [hLam, hMu] at hcompact
  have hlow : 0 ≤ fordAvg (fun x => w x * a x ^ (k - 1)) := by
    exact Finset.expect_nonneg (fun x _ => mul_nonneg (hw x) (pow_nonneg (ha x) _))
  have hpow_le := Real.rpow_le_rpow hlow hcompact (show 0 ≤ (k : ℝ) by positivity)
  have hleft :
      (fordAvg (fun x => w x * a x ^ (k - 1))) ^ (k : ℝ) =
        (fordAvg (fun x => w x * a x ^ (k - 1))) ^ k := by
    rw [Real.rpow_natCast]
  have hright :
      (fordAvg w ^ (1 / (k : ℝ)) *
        fordAvg (fun x => w x * a x ^ k) ^ (((k - 1 : ℕ) : ℝ) / k)) ^ (k : ℝ) =
      (fordAvg (fun x => w x * a x ^ k)) ^ (k - 1) * fordAvg w := by
    have hB : 0 ≤ fordAvg w := Finset.expect_nonneg (fun x _ => hw x)
    have hH : 0 ≤ fordAvg (fun x => w x * a x ^ k) :=
      Finset.expect_nonneg (fun x _ => mul_nonneg (hw x) (pow_nonneg (ha x) _))
    calc
      _ = (fordAvg w ^ (1 / (k : ℝ))) ^ (k : ℝ) *
          (fordAvg (fun x => w x * a x ^ k) ^ (((k - 1 : ℕ) : ℝ) / k)) ^ (k : ℝ) := by
        exact Real.mul_rpow (Real.rpow_nonneg hB _) (Real.rpow_nonneg hH _)
      _ = fordAvg w ^ ((1 / (k : ℝ)) * (k : ℝ)) *
          fordAvg (fun x => w x * a x ^ k) ^
            ((((k - 1 : ℕ) : ℝ) / k) * (k : ℝ)) := by
        rw [← Real.rpow_mul hB, ← Real.rpow_mul hH]
      _ = (fordAvg (fun x => w x * a x ^ k)) ^ (k - 1) * fordAvg w := by
        have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
        have hfirst : (1 / (k : ℝ)) * (k : ℝ) = 1 := by field_simp
        have hsecond : (((k - 1 : ℕ) : ℝ) / k) * (k : ℝ) = (k - 1 : ℕ) := by
          rw [Nat.cast_sub (by omega)]
          field_simp
        rw [hfirst, hsecond, Real.rpow_one, Real.rpow_natCast]
        ring
  rw [hleft, hright] at hpow_le
  exact hpow_le

theorem scalar_moment_absorption
    {k : ℕ} (hk : 1 ≤ k) {L P J C : ℝ}
    (hL : 0 ≤ L) (hJ : 0 ≤ J) (hC : 0 ≤ C)
    (hlin : L ≤ C * P)
    (hmom : P ^ k ≤ L ^ (k - 1) * J) :
    L ≤ C ^ k * J := by
  by_cases hL0 : L = 0
  · rw [hL0]
    positivity
  have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
  have hpow : L ^ k ≤ (C * P) ^ k := pow_le_pow_left₀ hL hlin k
  have hmul : L ^ k ≤ C ^ k * (L ^ (k - 1) * J) := by
    calc
      L ^ k ≤ (C * P) ^ k := hpow
      _ = C ^ k * P ^ k := by rw [mul_pow]
      _ ≤ C ^ k * (L ^ (k - 1) * J) :=
        mul_le_mul_of_nonneg_left hmom (pow_nonneg hC _)
  have hfac : 0 < L ^ (k - 1) := pow_pos hLpos _
  have hcancel : L ^ (k - 1) * L ≤ L ^ (k - 1) * (C ^ k * J) := by
    calc
      L ^ (k - 1) * L = L ^ k := by
        calc
          L ^ (k - 1) * L = L ^ ((k - 1) + 1) := (pow_succ L (k - 1)).symm
          _ = L ^ k := by congr 1 <;> omega
      _ ≤ C ^ k * (L ^ (k - 1) * J) := hmul
      _ = L ^ (k - 1) * (C ^ k * J) := by ring
  exact le_of_mul_le_mul_left hcancel hfac

end
end FordLemma33WeightedHolder

#print axioms FordLemma33WeightedHolder.weighted_moment_interpolation
#print axioms FordLemma33WeightedHolder.scalar_moment_absorption
