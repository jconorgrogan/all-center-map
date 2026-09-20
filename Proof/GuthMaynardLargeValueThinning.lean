import GuthMaynardJutilaSpacingPartition

/-!
# One-spacing to strong-spacing large-value count

The source passage from Theorem 1.1 to Proposition 3.1 first colors a
one-separated set by the already-proved `powerSpacingColor`.  Each color fiber
is `T^delta`-separated, and the exact number of colors is bounded by
`3 * T^delta`.  This module applies a local large-value bound uniformly to
those fibers and sums their cardinalities.

The coefficient sequence, threshold, interval `[0,T]`, and every local
large-value hypothesis are passed unchanged.  The only loss is the explicit
color count.  No new floor coloring, global Guth--Maynard theorem, or analytic
large-value estimate is introduced here.
-/

namespace GuthMaynardLargeValueThinning

open scoped BigOperators
open CGLProofDAG
open GuthMaynardJutilaSpacingPartition
open GuthMaynardJutilaReflection2941

noncomputable section

set_option maxHeartbeats 500000
set_option linter.unusedVariables false

/-- Exact cardinal partition by the existing `powerSpacingColor`. -/
theorem card_eq_sum_powerSpacingColorFiber
    {W : Finset ℝ} {T delta : ℝ}
    (hT : 1 ≤ T) (hdelta : 0 ≤ delta) (hsep : OneSeparated W) :
    W.card =
      ∑ i : Fin (powerSpacingColorCount T delta),
        (colorFiber (powerSpacingColor T delta) W i).card := by
  let c := powerSpacingColor T delta
  have hfiber := Finset.sum_fiberwise W c
    (fun _ : ℝ => (1 : ℕ))
  have hsum :
      ∑ i : Fin (powerSpacingColorCount T delta),
          (colorFiber c W i).card = W.card := by
    calc
      ∑ i : Fin (powerSpacingColorCount T delta),
          (colorFiber c W i).card =
          ∑ i : Fin (powerSpacingColorCount T delta),
            ∑ t ∈ W with c t = i, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.card_eq_sum_ones]
        rfl
      _ = ∑ t ∈ W, (1 : ℕ) := hfiber
      _ = W.card := by simp
  simpa [c] using hsum.symm

/-- Convert a uniform local bound for `T^delta`-separated finite sets into a
one-separated count.  The local sequence remains the original `b`; no
coefficient phase or threshold is altered by coloring. -/
theorem card_le_three_powerSpacing_mul_of_local_bound
    (b : ℕ → ℂ) (N : ℕ) (W : Finset ℝ) {T delta V K : ℝ}
    (hT : 1 ≤ T) (hdelta : 0 ≤ delta)
    (hb : ∀ n, ‖b n‖ ≤ 1)
    (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T)
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖)
    (hK : 0 ≤ K)
    (hlocal : ∀ (a : ℕ → ℂ) (U : Finset ℝ),
      (∀ n, ‖a n‖ ≤ 1) →
      TPowerSeparated U T delta →
      (∀ u ∈ U, 0 ≤ u ∧ u ≤ T) →
      (∀ u ∈ U, V ≤ ‖dirichletPolynomial a N u‖) →
      (U.card : ℝ) ≤ K) :
    (W.card : ℝ) ≤ 3 * Real.rpow T delta * K := by
  have hcard := card_eq_sum_powerSpacingColorFiber hT hdelta hsep
  have hfiber : ∀ i : Fin (powerSpacingColorCount T delta),
      ((colorFiber (powerSpacingColor T delta) W i).card : ℝ) ≤ K := by
    intro i
    have hstrong := powerSpacingColorFiber_TPowerSeparated
      hsep (T := T) (delta := delta) i
    have hsub : colorFiber (powerSpacingColor T delta) W i ⊆ W := by
      exact Finset.filter_subset _ _
    have hheight' : ∀ u ∈ colorFiber (powerSpacingColor T delta) W i,
        0 ≤ u ∧ u ≤ T := by
      intro u hu
      exact hheight u (hsub hu)
    have hlarge' : ∀ u ∈ colorFiber (powerSpacingColor T delta) W i,
        V ≤ ‖dirichletPolynomial b N u‖ := by
      intro u hu
      exact hlarge u (hsub hu)
    exact hlocal b _ hb hstrong hheight' hlarge'
  have hsumle :
      ∑ i : Fin (powerSpacingColorCount T delta),
          ((colorFiber (powerSpacingColor T delta) W i).card : ℝ) ≤
        ∑ _i : Fin (powerSpacingColorCount T delta), K := by
    apply Finset.sum_le_sum
    intro i hi
    exact hfiber i
  have hW : (W.card : ℝ) =
      ∑ i : Fin (powerSpacingColorCount T delta),
        ((colorFiber (powerSpacingColor T delta) W i).card : ℝ) := by
    exact_mod_cast hcard
  rw [hW]
  calc
    ∑ i : Fin (powerSpacingColorCount T delta),
        ((colorFiber (powerSpacingColor T delta) W i).card : ℝ) ≤
        ∑ _i : Fin (powerSpacingColorCount T delta), K := hsumle
    _ = (powerSpacingColorCount T delta : ℝ) * K := by simp
    _ ≤ 3 * Real.rpow T delta * K := by
      have hm := powerSpacingColorCount_cast_le hT hdelta
      exact mul_le_mul_of_nonneg_right hm hK

end
end GuthMaynardLargeValueThinning

#print axioms GuthMaynardLargeValueThinning.card_eq_sum_powerSpacingColorFiber
#print axioms GuthMaynardLargeValueThinning.card_le_three_powerSpacing_mul_of_local_bound
