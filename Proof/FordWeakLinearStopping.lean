import Mathlib
import FordWeakPolicyIntegerBridge

namespace MAPFordWeakPolicy
noncomputable section
set_option maxHeartbeats 900000

theorem policy_step_coarse_decrement
    {k Delta : ℝ} (hk : 200 ≤ k) (hk0 : 0 < k)
    (hD0 : k ^ 2 / 100 ≤ Delta)
    (hD1 : Delta ≤ (k ^ 2 - k) / 2) :
    let A : ℝ := max 1 (Nat.ceil (Delta / k - 1) : ℝ)
    7 * k / 1000 ≤ Delta - fordDeltaNext k Delta A := by
  dsimp
  let A : ℝ := max 1 (Nat.ceil (Delta / k - 1) : ℝ)
  by_cases hhigh : k ^ 2 / 10 ≤ Delta
  · have hh := policy_high_contraction hk hk0 hhigh hD1
    dsimp at hh
    have hh' := (le_div_iff₀ hk0).1 hh
    have hscale : (7 * (Delta / k ^ 2) / 5) * k = (7 * (Delta / k) / 5) := by
      field_simp
    rw [hscale] at hh'
    have hhigh' : k / 10 ≤ Delta / k := by
      apply (le_div_iff₀ hk0).2
      field_simp
      nlinarith [hhigh]
    nlinarith [hh', hhigh']
  · have hlow : Delta ≤ k ^ 2 / 10 := le_of_not_ge hhigh
    have hl := policy_low_contraction hk hk0 hD0 hlow
    dsimp at hl
    have hl' := (le_div_iff₀ hk0).1 hl
    have hrel : ((3 * (Delta / k ^ 2) / 2 - 1 / 125) * k) =
        3 * Delta / (2 * k) - k / 125 := by field_simp
    rw [hrel] at hl'
    have hscale2 : 3 * Delta / (2 * k) = 3 * (Delta / k) / 2 := by ring
    rw [hscale2] at hl'
    have hlow' : k / 100 ≤ Delta / k := by
      apply (le_div_iff₀ hk0).2
      field_simp
      nlinarith [hD0]
    nlinarith [hl', hlow']

theorem finite_linear_stopping
    {D : ℕ → ℝ} {N : ℕ} {floor D0 c : ℝ}
    (hD0 : D 0 ≤ D0) (hc : 0 < c)
    (hstep : ∀ n, floor ≤ D n → D (n + 1) ≤ D n - c)
    (hbudget : D0 - (N : ℝ) * c < floor) :
    ∃ n ≤ N, D n < floor := by
  by_contra hbad
  push_neg at hbad
  have hbound : ∀ n ≤ N, D n ≤ D0 - (n : ℝ) * c := by
    intro n hn
    induction n with
    | zero => simpa using hD0
    | succ n ih =>
        have hDn : floor ≤ D n := hbad n (Nat.le_trans (Nat.le_succ n) hn)
        have hs := hstep n hDn
        have hi := ih (Nat.le_trans (Nat.le_succ n) hn)
        norm_num at hs ⊢
        nlinarith
  have hN := hbound N (le_refl N)
  have hfloor := hbad N (le_refl N)
  nlinarith

theorem coarse_linear_stopping
    {k : ℝ} {D : ℕ → ℝ} (hk : 200 ≤ k) (hD0 : D 0 ≤ (k ^ 2 - k) / 2)
    (hstep : ∀ n, k ^ 2 / 100 ≤ D n →
      D (n + 1) ≤ D n - 7 * k / 1000) :
    ∃ n ≤ Nat.ceil (500 * k / 7) + 1, D n < k ^ 2 / 100 := by
  let N : ℕ := Nat.ceil (500 * k / 7) + 1
  have hk0 : 0 < k := by linarith
  have hNceil : (500 * k / 7 : ℝ) ≤ (Nat.ceil (500 * k / 7) : ℝ) :=
    Nat.le_ceil _
  have hbudget : (k ^ 2 - k) / 2 - (N : ℝ) * (7 * k / 1000) < k ^ 2 / 100 := by
    dsimp [N]
    norm_num at hNceil ⊢
    nlinarith [hNceil]
  exact finite_linear_stopping hD0 (by positivity) hstep hbudget

end
end MAPFordWeakPolicy

#print axioms MAPFordWeakPolicy.finite_linear_stopping
#print axioms MAPFordWeakPolicy.coarse_linear_stopping
