import Mathlib

noncomputable section
namespace FordCompactEventualThreshold

open Filter

/-- For each fixed finite order, all polynomial losses below the quarter-power
scale are eventually absorbed. -/
theorem compact_eventual_threshold
    {r : ℕ} (hr : 2 ≤ r) :
    ∃ N0 : ℝ, ∀ N : ℝ, N0 ≤ N →
      N ≥ 2 ∧
      (r : ℝ) * N ^ ((3 : ℝ) / 4) ≤ N ∧
      16 * N ^ (-(1 / (4 * (r : ℝ)))) ≤ 1 ∧
      (r.factorial : ℝ) * N ^ (-(1 : ℝ) / 2) ≤ 1 ∧
      (12 * Real.pi * (8 : ℝ) ^ r) * N ^ (-(1 : ℝ) / 4) ≤
        N ^ (-(1 / (4 * (r : ℝ)))) := by
  let eps : ℝ := 1 / (4 * (r : ℝ))
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : 0 < (r : ℝ) := by linarith
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have hepsle : eps ≤ (1 : ℝ) / 8 := by
    dsimp [eps]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (r : ℝ))).2
    nlinarith
  have halpha : 0 < (1 : ℝ) / 4 - eps := by linarith
  have hN2 : ∀ᶠ N : ℝ in atTop, 2 ≤ N :=
    eventually_ge_atTop 2
  have hquarter : ∀ᶠ N : ℝ in atTop,
      (r : ℝ) ≤ N ^ ((1 : ℝ) / 4) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 4)).eventually
      (eventually_ge_atTop (r : ℝ))
  have hscale : ∀ᶠ N : ℝ in atTop,
      (r : ℝ) * N ^ ((3 : ℝ) / 4) ≤ N := by
    filter_upwards [hN2, hquarter] with N hN hq
    have hNpos : 0 < N := by linarith
    have hmul := mul_le_mul_of_nonneg_right hq
      (Real.rpow_nonneg hNpos.le ((3 : ℝ) / 4))
    calc
      (r : ℝ) * N ^ ((3 : ℝ) / 4) ≤
          N ^ ((1 : ℝ) / 4) * N ^ ((3 : ℝ) / 4) := hmul
      _ = N := by
        rw [← Real.rpow_add hNpos]
        norm_num
  have hsmall : ∀ᶠ N : ℝ in atTop,
      16 * N ^ (-eps) ≤ 1 := by
    have hz := (tendsto_rpow_neg_atTop heps)
    have hz' := (tendsto_order.mp hz).2 (1 / 16 : ℝ) (by norm_num)
    filter_upwards [hz'] with N hN
    nlinarith
  have hfac : ∀ᶠ N : ℝ in atTop,
      (r.factorial : ℝ) * N ^ (-(1 : ℝ) / 2) ≤ 1 := by
    have hfacpos : 0 < (r.factorial : ℝ) := by positivity
    have hz := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 2))
    have hz' := (tendsto_order.mp hz).2
      (1 / (r.factorial : ℝ)) (by positivity)
    filter_upwards [hz'] with N hN
    have := (mul_le_mul_of_nonneg_left (le_of_lt hN) (le_of_lt hfacpos))
    calc
      (r.factorial : ℝ) * N ^ (-(1 : ℝ) / 2) ≤
          (r.factorial : ℝ) * (1 / (r.factorial : ℝ)) := by
            convert this using 1 <;> ring
      _ = 1 := by field_simp
  have hlast : ∀ᶠ N : ℝ in atTop,
      (12 * Real.pi * (8 : ℝ) ^ r) * N ^ (-(1 : ℝ) / 4) ≤ N ^ (-eps) := by
    have hCpos : 0 < 12 * Real.pi * (8 : ℝ) ^ r := by positivity
    have hz := (tendsto_rpow_neg_atTop halpha)
    have hz' := (tendsto_order.mp hz).2
      (1 / (12 * Real.pi * (8 : ℝ) ^ r)) (by positivity)
    filter_upwards [hN2, hz'] with N hN hsmallN
    have hNpos : 0 < N := by linarith
    have hident : N ^ (-(1 : ℝ) / 4) =
        N ^ (-eps) * N ^ (-(1 / 4 - eps)) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    rw [hident]
    calc
      (12 * Real.pi * (8 : ℝ) ^ r) *
          (N ^ (-eps) * N ^ (-(1 / 4 - eps))) =
          (12 * Real.pi * (8 : ℝ) ^ r) *
            N ^ (-(1 / 4 - eps)) * N ^ (-eps) := by ring
      _ ≤ N ^ (-eps) := by
        have hC : (12 * Real.pi * (8 : ℝ) ^ r) *
            N ^ (-(1 / 4 - eps)) ≤ 1 := by
          calc
            _ ≤ (12 * Real.pi * (8 : ℝ) ^ r) *
                (1 / (12 * Real.pi * (8 : ℝ) ^ r)) :=
              mul_le_mul_of_nonneg_left (le_of_lt hsmallN) (le_of_lt hCpos)
            _ = 1 := by field_simp
        simpa using
          (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hNpos.le (-eps)))
  have hall : ∀ᶠ N : ℝ in atTop,
      N ≥ 2 ∧
      (r : ℝ) * N ^ ((3 : ℝ) / 4) ≤ N ∧
      16 * N ^ (-eps) ≤ 1 ∧
      (r.factorial : ℝ) * N ^ (-(1 : ℝ) / 2) ≤ 1 ∧
      (12 * Real.pi * (8 : ℝ) ^ r) * N ^ (-(1 : ℝ) / 4) ≤ N ^ (-eps) := by
    filter_upwards [hN2, hscale, hsmall, hfac, hlast] with
      N hN hs hsm hf hl
    exact ⟨hN, hs, hsm, hf, hl⟩
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hall
  refine ⟨N0, ?_⟩
  intro N hN
  have h := hN0 N hN
  simpa [eps] using h

end FordCompactEventualThreshold

#print axioms FordCompactEventualThreshold.compact_eventual_threshold
