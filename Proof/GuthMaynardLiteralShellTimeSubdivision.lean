import GuthMaynardLargeValueIntervalSubdivision
import GuthMaynardGMPointwiseKernel

/-!
# Exact time subdivision for the literal GM shell polynomial

This adapter is purely finite.  It rewrites the literal shell polynomial with
the source phase, applies the existing floor-index time subdivision, and keeps
the local cardinal premise uniform under the exact translated coefficient.
No plateau decomposition or analytic estimate is introduced.
-/

namespace GuthMaynardLiteralShellTimeSubdivision

open scoped BigOperators
open CGLProofDAG
open GuthMaynardSectionFourTrace
open GuthMaynardLargeValueIntervalSubdivision

noncomputable section

def gmShellPolynomial (a : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N), a n * sourcePhase n t

theorem gmShellPolynomial_eq_dirichletPolynomial
    (a : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    gmShellPolynomial a N t = dirichletPolynomial a N t := by
  simp [gmShellPolynomial, dirichletPolynomial, sourcePhase]

theorem card_le_floor_intervals_mul_of_literal_local_bound
    (b : ℕ → ℂ) (N : ℕ) (W : Finset ℝ) {T L V K : ℝ}
    (hL : 0 < L) (hT : 0 ≤ T)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ 1) (hsep : OneSeparated W)
    (hlarge : ∀ t ∈ W, V ≤ ‖gmShellPolynomial b N t‖)
    (hlocal : ∀ (a : ℕ → ℂ) (U : Finset ℝ),
      (∀ n, ‖a n‖ ≤ 1) → OneSeparated U →
      (∀ u ∈ U, 0 ≤ u ∧ u ≤ L) →
      (∀ u ∈ U, V ≤ ‖gmShellPolynomial a N u‖) →
      (U.card : ℝ) ≤ K) :
    (W.card : ℝ) ≤ (⌊T / L⌋₊ + 1 : ℕ) * K := by
  apply card_le_floor_intervals_mul_of_local_bound b N W hL hT hheight hb hsep
    (fun t ht => by
      simpa [gmShellPolynomial_eq_dirichletPolynomial] using hlarge t ht)
  intro a U ha hUsep hUheight hUlarge
  apply hlocal a U ha hUsep hUheight
  intro u hu
  simpa [gmShellPolynomial_eq_dirichletPolynomial] using hUlarge u hu

theorem card_le_time_ratio_plus_one_of_literal_local_bound
    (b : ℕ → ℂ) (N : ℕ) (W : Finset ℝ) {T L V K : ℝ}
    (hL : 0 < L) (hT : 0 ≤ T)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T)
    (hb : ∀ n, ‖b n‖ ≤ 1) (hsep : OneSeparated W)
    (hlarge : ∀ t ∈ W, V ≤ ‖gmShellPolynomial b N t‖)
    (hK : 0 ≤ K)
    (hlocal : ∀ (a : ℕ → ℂ) (U : Finset ℝ),
      (∀ n, ‖a n‖ ≤ 1) → OneSeparated U →
      (∀ u ∈ U, 0 ≤ u ∧ u ≤ L) →
      (∀ u ∈ U, V ≤ ‖gmShellPolynomial a N u‖) →
      (U.card : ℝ) ≤ K) :
    (W.card : ℝ) ≤ (T / L + 1) * K := by
  have hfloor := card_le_floor_intervals_mul_of_literal_local_bound
    b N W hL hT hheight hb hsep hlarge hlocal
  have hratio : (⌊T / L⌋₊ : ℝ) + 1 ≤ T / L + 1 := by
    have hq : 0 ≤ T / L := div_nonneg hT hL.le
    have hf : (⌊T / L⌋₊ : ℝ) ≤ T / L := by
      apply Nat.floor_le
      exact hq
    linarith
  have hmul := mul_le_mul_of_nonneg_right hratio hK
  exact hfloor.trans (by
    simpa only [Nat.cast_add, Nat.cast_one] using hmul)

end
end GuthMaynardLiteralShellTimeSubdivision

#print axioms GuthMaynardLiteralShellTimeSubdivision.card_le_floor_intervals_mul_of_literal_local_bound
#print axioms GuthMaynardLiteralShellTimeSubdivision.card_le_time_ratio_plus_one_of_literal_local_bound
