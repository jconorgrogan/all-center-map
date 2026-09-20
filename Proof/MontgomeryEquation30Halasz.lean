import MontgomeryEquation30Majorant
import MontgomeryTheorem83SmoothHalasz

/-!
# Source-faithful pairwise Halasz corollary for equation (30)

Montgomery's 1969 argument first enlarges the coefficient interval with the
positive equation-(30) weight and then uses the *maximum of the distinct
pair kernels* in Lemma 1.  It does not require an absolute row-sum estimate
at unit spacing.  This file proves that exact deterministic implication.

The only source-facing analytic input left by the final theorem is a bound
for each distinct smooth pair kernel after the published long-spacing
thinning.  This is precisely the output of Lemma 3.
-/

namespace MAPMontgomeryEquation30Halasz

open scoped BigOperators ComplexConjugate
open Complex
open MAPJutilaDeterministicCore
open MAPHuxleyHalaszFront
open MAPMontgomeryTheorem83SmoothHalasz
open MAPMontgomeryEquation30Majorant

noncomputable section

/-- A diagonal mass bound plus a maximum bound for each distinct pair gives
the exact `F + J*K` row estimate in Montgomery Lemma 1. -/
theorem weighted_rowKernel_le_of_mass_and_pairwise
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rows : Finset I) (cols : Finset J) (b : J → ℝ)
    (v : I → J → ℂ) {F K : ℝ}
    (hK : 0 ≤ K)
    (hb : ∀ k ∈ cols, 0 ≤ b k)
    (hdiag : ∀ i ∈ rows,
      ‖∑ k ∈ cols, (b k : ℂ) * conj (v i k) * v i k‖ ≤ F)
    (hoff : ∀ i ∈ rows, ∀ j ∈ rows, i ≠ j →
      ‖∑ k ∈ cols, (b k : ℂ) * conj (v i k) * v j k‖ ≤ K) :
    ∀ i ∈ rows,
      ∑ j ∈ rows,
          ‖∑ k ∈ cols, (b k : ℂ) * conj (v i k) * v j k‖ ≤
        F + (rows.card : ℝ) * K := by
  intro i hi
  let B : I → ℝ := fun j =>
    ‖∑ k ∈ cols, (b k : ℂ) * conj (v i k) * v j k‖
  have hsplit :
      (∑ j ∈ rows, B j) = B i + ∑ j ∈ rows.erase i, B j := by
    rw [add_comm]
    exact (Finset.sum_erase_add rows B hi).symm
  rw [hsplit]
  have hoffsum : (∑ j ∈ rows.erase i, B j) ≤
      ((rows.erase i).card : ℝ) * K := by
    calc
      (∑ j ∈ rows.erase i, B j) ≤
          ∑ _j ∈ rows.erase i, K := by
        apply Finset.sum_le_sum
        intro j hj
        have hjRows := (Finset.mem_erase.mp hj).2
        have hij : i ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
        exact hoff i hi j hjRows hij
      _ = ((rows.erase i).card : ℝ) * K := by simp
  have hcard : ((rows.erase i).card : ℝ) ≤ rows.card := by
    exact_mod_cast (Finset.card_erase_le : (rows.erase i).card ≤ rows.card)
  have hoffsum' : (∑ j ∈ rows.erase i, B j) ≤
      (rows.card : ℝ) * K :=
    hoffsum.trans (mul_le_mul_of_nonneg_right hcard hK)
  exact add_le_add (hdiag i hi) hoffsum'

/-- Exact finite form of Montgomery's corollary to Lemma 1.  Compare source
equations (24)--(26). -/
theorem finite_weighted_halasz_absorbed_of_pairwise
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rows : Finset I) (cols : Finset J)
    (a : J → ℂ) (b : J → ℝ) (v : I → J → ℂ)
    {V E F K : ℝ}
    (hV : 0 ≤ V) (hE : 0 ≤ E) (hF : 0 ≤ F) (hK : 0 ≤ K)
    (hb : ∀ k ∈ cols, 0 < b k)
    (hlarge : ∀ i ∈ rows, V ≤ ‖finitePolynomial cols a v i‖)
    (hcoeff : (∑ k ∈ cols, ‖a k‖ ^ 2 / b k) ≤ E)
    (hdiag : ∀ i ∈ rows,
      ‖∑ k ∈ cols, (b k : ℂ) * conj (v i k) * v i k‖ ≤ F)
    (hoff : ∀ i ∈ rows, ∀ j ∈ rows, i ≠ j →
      ‖∑ k ∈ cols, (b k : ℂ) * conj (v i k) * v j k‖ ≤ K)
    (hthreshold : 2 * E * K ≤ V ^ 2) :
    (rows.card : ℝ) * V ^ 2 ≤ 2 * E * F := by
  have hrow := weighted_rowKernel_le_of_mass_and_pairwise
    rows cols b v hK (fun k hk => (hb k hk).le) hdiag hoff
  have h := finite_weighted_halasz_absorbed
    rows cols a b v hV hE (by norm_num : (0 : ℝ) ≤ 1) hF hK
    hb hlarge hcoeff
    (by
      intro i hi
      simpa using hrow i hi)
    (by simpa using hthreshold)
  simpa using h

/-- Equation-(30) diagonal mass on any finite natural-number carrier.  The
extra `+1` is only the harmless zeroth term introduced by embedding the
finite carrier in all of `ℕ`. -/
theorem equation30_finite_diagonal_mass_le
    {q : ℕ} {N : ℝ} (hN : 0 < N)
    (cols : Finset ℕ)
    (row : (chi : DirichletCharacter ℂ q) × ℝ) :
    ‖∑ n ∈ cols, (equation30Weight N n : ℂ) *
        conj (MAPMontgomeryTheorem83Halasz.characterRowVector row n) *
        MAPMontgomeryTheorem83Halasz.characterRowVector row n‖ ≤
      Real.exp 1 * (N + 1) := by
  have hdiag := weighted_characterRow_diagonal_le_mass
    cols (equation30Weight N)
    (fun n hn => (equation30Weight_pos N n).le) row
  have hsummable : Summable (fun n : ℕ => equation30Weight N n) := by
    let r : ℝ := Real.exp (-(1 / N))
    have hr : r < 1 := by
      dsimp [r]
      rw [show (1 : ℝ) = Real.exp 0 by simp]
      exact Real.exp_lt_exp.mpr (by
        have : -(1 / N) < 0 := neg_lt_zero.mpr (one_div_pos.mpr hN)
        simpa using this)
    simpa only [equation30Weight_eq_geometric hN] using
      (summable_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left
        (Real.exp 1)
  have hfinite : (∑ n ∈ cols, equation30Weight N n) ≤
      ∑' n : ℕ, equation30Weight N n := by
    exact hsummable.sum_le_tsum cols (fun n hn => (equation30Weight_pos N n).le)
  exact hdiag.trans (hfinite.trans (equation30_full_mass_lt hN).le)

end
end MAPMontgomeryEquation30Halasz

#print axioms MAPMontgomeryEquation30Halasz.weighted_rowKernel_le_of_mass_and_pairwise
#print axioms MAPMontgomeryEquation30Halasz.finite_weighted_halasz_absorbed_of_pairwise
#print axioms MAPMontgomeryEquation30Halasz.equation30_finite_diagonal_mass_le
