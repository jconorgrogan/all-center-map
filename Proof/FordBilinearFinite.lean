import FordBilinearBox
import FordSubsetBoxBound

open scoped BigOperators
noncomputable section
namespace FordBilinearFinite
open FordPolynomialPhase FordSubsetMoment

def kernelFactor (L K q : ℕ) (gamma : ℝ) : ℝ :=
  (L : ℝ) * min (2 * (K : ℝ))
    (6 + (4 * (q : ℝ) + 2) * (K : ℝ) / L +
      6 * (K : ℝ) * |gamma| + (4 * (q : ℝ) + 2) / ((L : ℝ) * |gamma|))

/-- Complete finite bilinear estimate with both actual complete moments and
all literal capped Dirichlet factors. -/
theorem bilinear_bound (B : Finset ℕ) (r s k M1 M2 : ℕ)
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M2)
    (q : Fin k → ℕ) (gamma : Fin k → ℝ)
    (hq : ∀ j, r * M1 ^ (j.val + 1) < 2 ^ q j)
    (hg : ∀ j, gamma j ≠ 0) :
    ‖∑ b : BoundedNat B, ∑ a : Fin M1,
      e (∑ j : Fin k, gamma j * (b.val : ℝ) ^ (j.val + 1) *
        ((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1))‖ ^ (r * (2 * s)) ≤
    (B.card : ℝ) ^ ((r - 1) * (2 * s)) *
      ((M1 : ℝ) ^ (r * (2 * s - 2)) *
        (MAPFordCompleteSystemMoment.completeMoment r k M1 : ℝ) *
          ((MAPFordCompleteSystemMoment.completeMoment s k M2 : ℝ) *
            ∏ j : Fin k, kernelFactor (r * M1 ^ (j.val + 1))
              (s * M2 ^ (j.val + 1)) (q j) (gamma j))) := by
  classical
  obtain ⟨eps, heps, hfirst⟩ := FordBilinearBox.polynomial_bilinear_box
    (B := BoundedNat B) r k M1 s (by omega) (by omega) gamma (fun b => (b.val : ℝ))
  have hL (j : Fin k) : 2 ≤ r * M1 ^ (j.val + 1) := by
    have hp : 1 ≤ M1 ^ (j.val + 1) :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    exact hr.trans (by simpa using Nat.mul_le_mul_left r hp)
  have hK (j : Fin k) : 2 ≤ s * M2 ^ (j.val + 1) := by
    have hp : 1 ≤ M2 ^ (j.val + 1) :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    exact hs.trans (by simpa using Nat.mul_le_mul_left s hp)
  have hsecond := FordSubsetBoxBound.subset_box_moment_bound B s k M2 (by omega) hB
    (fun j => r * M1 ^ (j.val + 1)) q gamma hL hK hq hg eps heps
  have hmul := mul_le_mul_of_nonneg_left hsecond
    (show 0 ≤ (M1 : ℝ) ^ (r * (2 * s - 2)) *
      (MAPFordCompleteSystemMoment.completeMoment r k M1 : ℝ) by positivity)
  have hmul' := mul_le_mul_of_nonneg_left hmul
    (show 0 ≤ (Fintype.card (BoundedNat B) : ℝ) ^ ((r - 1) * (2 * s)) by positivity)
  simpa only [kernelFactor, Fintype.card_coe] using hfirst.trans hmul'

end FordBilinearFinite
#print axioms FordBilinearFinite.bilinear_bound
