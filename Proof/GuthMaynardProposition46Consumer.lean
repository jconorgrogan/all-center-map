import GuthMaynardLemma41Spectral
import GuthMaynardLemma44TraceOne
import GuthMaynardProposition46Algebra

/-!
# Literal deterministic consumer for Guth--Maynard Proposition 4.6

This file closes the matrix/operator/spectral part of Proposition 4.6 on the
actual Section 4 objects.  No analytic sector estimate is assumed here.
-/

namespace GuthMaynardProposition46Consumer

open scoped BigOperators
open GuthMaynardSectionFourTrace GuthMaynardLemma41Operator
open GuthMaynardLemma41Spectral GuthMaynardLemma42Gram
open GuthMaynardProposition46Algebra

noncomputable section

theorem source_trace_defect_nonneg
    (W : Finset ℝ) (N : ℕ) (hW : W.Nonempty) :
    0 ≤ (sourceTraceCube W N).re -
      (sourceTraceOne W N).re ^ 3 / (W.card : ℝ) ^ 2 := by
  letI : Nonempty (SourceRow W) := by
    rcases hW with ⟨t, ht⟩
    exact ⟨⟨t, ht⟩⟩
  let x : SourceRow W → ℝ := fun i =>
    Real.sqrt ((sourceGram_posSemidef W N).1.eigenvalues i) ^ 2
  have hx : ∀ i, 0 ≤ x i := fun i => sq_nonneg _
  have hj := pow_sum_div_card_le_sum_pow
    (s := (Finset.univ : Finset (SourceRow W))) (f := x)
    (fun i hi => hx i) 2
  have hcard : Fintype.card (SourceRow W) = W.card := by simp [SourceRow]
  have hsum2 := sourceGram_sqrtEigen_sq_sum_eq_trace_re W N
  have hsum6 := sourceGram_sqrtEigen_six_sum_eq_cube_sum W N
  have hcube := sourceGram_cube_sum_eq_traceCube_re W N
  rw [show (∑ i : SourceRow W, x i) = (sourceTraceOne W N).re by
      simpa [x] using hsum2] at hj
  rw [Finset.card_univ, hcard] at hj
  have hrhs : (∑ i : SourceRow W, x i ^ 3) =
      (sourceTraceCube W N).re := by
    calc
      (∑ i : SourceRow W, x i ^ 3) =
          ∑ i : SourceRow W,
            Real.sqrt ((sourceGram_posSemidef W N).1.eigenvalues i) ^ 6 := by
              apply Finset.sum_congr rfl
              intro i hi
              simp only [x]
              ring
      _ = ∑ i : SourceRow W,
          ((sourceGram_posSemidef W N).1.eigenvalues i) ^ 3 := hsum6
      _ = (sourceTraceCube W N).re := hcube
  rw [hrhs] at hj
  norm_num at hj
  exact sub_nonneg.mpr hj

theorem source_trace_average_nonneg
    (W : Finset ℝ) (N : ℕ) (hW : W.Nonempty) :
    0 ≤ (sourceTraceOne W N).re / (W.card : ℝ) := by
  have hcard : 0 < (W.card : ℝ) := by exact_mod_cast hW.card_pos
  have htrace : 0 ≤ (sourceTraceOne W N).re := by
    rw [← sourceGram_sqrtEigen_sq_sum_eq_trace_re W N]
    exact Finset.sum_nonneg fun i hi => sq_nonneg _
  exact div_nonneg htrace hcard.le

/-- The exact matrix-theoretic content of Proposition 4.6.  The right side is
still written using the literal cubic trace defect and average trace, ready for
the Poisson/S1/S2/S3 estimates. -/
theorem source_proposition46_trace_form
    (W : Finset ℝ) (N : ℕ) (b : ℕ → ℂ) (L : ℝ)
    (hW : W.Nonempty) (hL : 0 ≤ L)
    (hb : ∀ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ≤ 1)
    (hlarge : ∀ t : SourceRow W, L ≤ ‖sourceDN b N t‖) :
    (W.card : ℝ) * L ^ 2 ≤
      8 * (N : ℝ) *
        (((sourceTraceCube W N).re -
            (sourceTraceOne W N).re ^ 3 / (W.card : ℝ) ^ 2) ^
              (1 / 3 : ℝ) +
          (sourceTraceOne W N).re / (W.card : ℝ)) := by
  obtain ⟨i₀, hi₀⟩ :=
    exists_sourceGram_eigenvalue_eq_operator_norm_sq W N hW
  let D : ℝ := (sourceTraceCube W N).re -
    (sourceTraceOne W N).re ^ 3 / (W.card : ℝ) ^ 2
  let A : ℝ := (sourceTraceOne W N).re / (W.card : ℝ)
  let s : ℝ := ‖sourceMatrixOperator W N‖
  have hD : 0 ≤ D := source_trace_defect_nonneg W N hW
  have hA : 0 ≤ A := source_trace_average_nonneg W N hW
  have hs : 0 ≤ s := norm_nonneg _
  have henergy : (W.card : ℝ) * L ^ 2 ≤ (N : ℝ) * s ^ 2 := by
    have h := source_large_value_cardinality_mul_le W N b L hL hb hlarge
    simpa [s, mul_comm] using h
  have hlemma42 := sourceGram_eigenvalue_le_trace_defect W N i₀
  rw [hi₀, Real.sqrt_sq_eq_abs, abs_of_nonneg hs] at hlemma42
  change s ≤ 2 * D ^ (1 / 6 : ℝ) + 2 * Real.sqrt A at hlemma42
  have hout := largeValue_of_singular_trace_defect
    (R := (W.card : ℝ) * L ^ 2) (N := (N : ℝ))
    (s := s) (D := D) (A := A)
    (Nat.cast_nonneg N) hs hD hA henergy hlemma42
  simpa [D, A] using hout

end
end GuthMaynardProposition46Consumer

#print axioms GuthMaynardProposition46Consumer.source_proposition46_trace_form
#print axioms GuthMaynardProposition46Consumer.source_trace_defect_nonneg
#print axioms GuthMaynardProposition46Consumer.source_trace_average_nonneg
