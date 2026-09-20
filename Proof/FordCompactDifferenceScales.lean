import Mathlib

noncomputable section
namespace FordCompactDifferenceScales

def shiftExponent (r : ℕ) (lam : ℝ) : ℝ :=
  ((r : ℝ) + 1 / 2 - lam) / r

def cutoffExponent (r : ℕ) : ℝ := 1 / (4 * (r : ℝ))

/-- Exact exponent ledger for the proposed compact-lambda differencing step.
This is scalar algebra, not an exponential-sum estimate. -/
theorem scale_ledger {r : ℕ} {lam : ℝ}
    (hr : 1 ≤ r) (hlam : 1 ≤ lam)
    (hlo : (r : ℝ) - 1 ≤ lam) (hhi : lam ≤ r) :
    0 < cutoffExponent r ∧
    cutoffExponent r ≤ shiftExponent r lam ∧
    shiftExponent r lam ≤ 3 / 4 ∧
    lam + (r : ℝ) * shiftExponent r lam - (r + 1) = -(1 / 2) ∧
    lam + (r : ℝ) * (shiftExponent r lam - cutoffExponent r) -
      (r + 1) = -(3 / 4) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrpos
  have heps : 0 < cutoffExponent r := by unfold cutoffExponent; positivity
  have hq : cutoffExponent r ≤ shiftExponent r lam := by
    unfold cutoffExponent shiftExponent
    apply (le_div_iff₀ hrpos).2
    have he : (1 / (4 * (r : ℝ))) * r = 1 / 4 := by field_simp
    rw [he]
    linarith
  have hqu : shiftExponent r lam ≤ 3 / 4 := by
    unfold shiftExponent
    apply (div_le_iff₀ hrpos).2
    by_cases hr1 : r = 1
    · subst r
      norm_num at *
      linarith
    · have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast (show 2 ≤ r by omega)
      linarith
  refine ⟨heps, hq, hqu, ?_, ?_⟩
  · unfold shiftExponent
    field_simp
    <;> ring
  · unfold shiftExponent cutoffExponent
    field_simp
    <;> ring

end FordCompactDifferenceScales
#print axioms FordCompactDifferenceScales.scale_ledger
