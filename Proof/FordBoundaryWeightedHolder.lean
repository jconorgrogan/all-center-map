import Mathlib.Analysis.MeanInequalities

open scoped BigOperators

namespace FordBoundaryWeightedHolder

noncomputable section

def fordAvg {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (Finset.univ : Finset α).expect f

def fordA {α : Type*} [Fintype α] (w g : α → ℝ) (s : ℕ) : ℝ :=
  fordAvg (fun a => w a * g a ^ (2 * s))

def fordB {α : Type*} [Fintype α] (w : α → ℝ) : ℝ :=
  fordAvg w

def fordH {α : Type*} [Fintype α] (w g : α → ℝ) (s : ℕ) : ℝ :=
  fordAvg (fun a => w a * g a ^ (2 * s - 1))

theorem weighted_holder_normalized
    {α : Type*} [Fintype α] [Nonempty α]
    (w g : α → ℝ) (s : ℕ) (hs : 1 ≤ s)
    (hw : ∀ a, 0 ≤ w a) (hg : ∀ a, 0 ≤ g a) :
    fordH w g s ≤
      fordA w g s ^ ((1 : ℝ) - 1 / (2 * s : ℝ)) *
        fordB w ^ (1 / (2 * s : ℝ)) := by
  let n : ℝ := (2 * s : ℕ)
  let p : ℝ := n / (n - 1)
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast (show 0 < 2 * s by omega)
  have hnmpos : 0 < n - 1 := by
    dsimp [n]
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    norm_num [Nat.cast_mul]
    nlinarith
  have hp : 1 ≤ p := by
    dsimp [p]
    apply (le_div_iff₀ hnmpos).2
    linarith
  have hexp : ((2 * s - 1 : ℕ) : ℝ) = n - 1 := by
    dsimp [n]
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hmul : ((2 * s - 1 : ℕ) : ℝ) * p = n := by
    rw [hexp]
    dsimp [p]
    field_simp
  have hpinv : p⁻¹ = 1 - n⁻¹ := by
    dsimp [p]
    field_simp
  have hpow (a : α) :
      ((g a) ^ (2 * s - 1) : ℝ) ^ p = (g a) ^ (2 * s) := by
    calc
      ((g a) ^ (2 * s - 1) : ℝ) ^ p =
          ((g a) ^ ((2 * s - 1 : ℕ) : ℝ)) ^ p := by
            rw [Real.rpow_natCast]
      _ = (g a) ^ (((2 * s - 1 : ℕ) : ℝ) * p) := by
            rw [← Real.rpow_mul (hg a)]
      _ = (g a) ^ n := by rw [hmul]
      _ = (g a) ^ (2 * s) := by rw [Real.rpow_natCast]
  have hh := Real.compact_inner_le_weight_mul_Lp_of_nonneg
    (s := (Finset.univ : Finset α)) (p := p) hp
    (w := w) (f := fun a => (g a) ^ (2 * s - 1)) hw
    (fun a => pow_nonneg (hg a) _)
  simp_rw [hpow] at hh
  change fordH w g s ≤ fordB w ^ (1 - p⁻¹) * fordA w g s ^ p⁻¹ at hh
  rw [hpinv] at hh
  have hfirst : 1 - (1 - n⁻¹) = 1 / (2 * s : ℝ) := by
    dsimp [n]
    norm_num [Nat.cast_mul]
  have hsecond : 1 - n⁻¹ = 1 - 1 / (2 * s : ℝ) := by
    dsimp [n]
    norm_num [Nat.cast_mul]
  rw [hfirst, hsecond] at hh
  nlinarith [hh]

theorem scalar_absorption
    {s : ℕ} (hs : 1 ≤ s) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : A ≤ 4 * (s : ℝ) *
      A ^ ((1 : ℝ) - 1 / (2 * s : ℝ)) *
      B ^ (1 / (2 * s : ℝ))) :
    A ≤ (4 * (s : ℝ)) ^ (2 * s) * B := by
  by_cases hAz : A = 0
  · subst A
    positivity
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  let n : ℝ := (2 * s : ℕ)
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast (show 0 < 2 * s by omega)
  have hnmpos : 0 < n - 1 := by
    dsimp [n]
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    norm_num [Nat.cast_mul]
    nlinarith
  have hpowA :
      A ^ ((1 : ℝ) - 1 / n) * A ^ (1 / n) = A := by
    rw [← Real.rpow_add hApos]
    norm_num
    
  have hmul :
      A ^ ((1 : ℝ) - 1 / n) * A ^ (1 / n) ≤
        A ^ ((1 : ℝ) - 1 / n) *
          ((4 * (s : ℝ)) * B ^ (1 / n)) := by
    rw [hpowA]
    have hscale :
        (1 : ℝ) - 1 / (2 * s : ℝ) = 1 - 1 / n := by
      dsimp [n]
      norm_num [Nat.cast_mul]
    have hscale' : (1 / (2 * s : ℝ)) = 1 / n := by
      dsimp [n]
      norm_num [Nat.cast_mul]
    rw [hscale, hscale'] at h
    convert h using 1 <;> ring
  have hAexp : 0 < A ^ ((1 : ℝ) - 1 / n) := by
    apply Real.rpow_pos_of_pos hApos
  have hcancel : A ^ (1 / n) ≤ (4 * (s : ℝ)) * B ^ (1 / n) :=
    le_of_mul_le_mul_left hmul hAexp
  have hnnonneg : 0 ≤ n := hnpos.le
  have hraised := Real.rpow_le_rpow
    (Real.rpow_nonneg (le_of_lt hApos) _) hcancel hnnonneg
  have hK : 0 ≤ 4 * (s : ℝ) := by positivity
  have hleft : (A ^ (1 / n)) ^ n = A := by
    rw [← Real.rpow_mul (le_of_lt hApos)]
    rw [div_mul_cancel₀ (1 : ℝ) (ne_of_gt hnpos), Real.rpow_one]
  have hright :
      ((4 * (s : ℝ)) * B ^ (1 / n)) ^ n =
        (4 * (s : ℝ)) ^ n * B := by
    rw [Real.mul_rpow hK (Real.rpow_nonneg hB _)]
    have hBpow : (B ^ (1 / n)) ^ n = B := by
      rw [← Real.rpow_mul hB]
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hnpos), Real.rpow_one]
    rw [hBpow]
  rw [hleft, hright] at hraised
  have hncast : (4 * (s : ℝ)) ^ n = (4 * (s : ℝ)) ^ (2 * s) := by
    dsimp [n]
    rw [Real.rpow_natCast]
  rw [hncast] at hraised
  exact hraised

end
end FordBoundaryWeightedHolder

#print axioms FordBoundaryWeightedHolder.weighted_holder_normalized
#print axioms FordBoundaryWeightedHolder.scalar_absorption
