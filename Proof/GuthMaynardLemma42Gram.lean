import GuthMaynardLemma42Scalar
import Mathlib.Analysis.Matrix.PosDef

/-! # Lemma 4.2 on the literal Guth--Maynard Gram matrix -/

namespace GuthMaynardLemma42Gram

open scoped BigOperators ComplexOrder
open GuthMaynardSectionFourTrace GuthMaynardLemma42Scalar

noncomputable section

theorem sourceGram_posSemidef (W : Finset ℝ) (N : ℕ) :
    (sourceGram W N).PosSemidef := by
  simpa [sourceGram] using
    (Matrix.posSemidef_self_mul_conjTranspose (sourceMatrix W N))

theorem sourceTraceOne_eq_sum_eigenvalues
    (W : Finset ℝ) (N : ℕ) :
    sourceTraceOne W N =
      ∑ i : SourceRow W,
        ((sourceGram_posSemidef W N).1.eigenvalues i : ℂ) := by
  exact (sourceGram_posSemidef W N).1.trace_eq_sum_eigenvalues

/-- The existing scalar Lemma 4.2 specialized to the square roots of the
eigenvalues of the literal positive semidefinite matrix `M_W M_W*`.  This is
the exact matrix spectral step; no abstract singular-value premise remains. -/
theorem sourceGram_eigenvalue_lemma42
    (W : Finset ℝ) (N : ℕ) (i₀ : SourceRow W) :
    Real.sqrt ((sourceGram_posSemidef W N).1.eigenvalues i₀) ≤
      2 * ((∑ i : SourceRow W,
          Real.sqrt ((sourceGram_posSemidef W N).1.eigenvalues i) ^ 6) -
        (∑ i : SourceRow W,
          Real.sqrt ((sourceGram_posSemidef W N).1.eigenvalues i) ^ 2) ^ 3 /
            (W.card : ℝ) ^ 2) ^ (1 / 6 : ℝ) +
      2 * Real.sqrt
        ((∑ i : SourceRow W,
          Real.sqrt ((sourceGram_posSemidef W N).1.eigenvalues i) ^ 2) /
            (W.card : ℝ)) := by
  letI : Nonempty (SourceRow W) := ⟨i₀⟩
  have h := lemma42_equation4_3
    (fun i : SourceRow W =>
      Real.sqrt ((sourceGram_posSemidef W N).1.eigenvalues i))
    (fun i => Real.sqrt_nonneg _) i₀
  simpa using h

/-- The quadratic spectral moment in the preceding theorem is exactly the
real trace. -/
theorem sourceGram_sqrtEigen_sq_sum_eq_trace_re
    (W : Finset ℝ) (N : ℕ) :
    (∑ i : SourceRow W,
        Real.sqrt ((sourceGram_posSemidef W N).1.eigenvalues i) ^ 2) =
      (sourceTraceOne W N).re := by
  have htrace := sourceTraceOne_eq_sum_eigenvalues W N
  rw [htrace]
  change _ = Complex.reCLM (∑ i : SourceRow W,
    ((sourceGram_posSemidef W N).1.eigenvalues i : ℂ))
  rw [map_sum]
  simp only [Complex.reCLM_apply, Complex.ofReal_re]
  apply Finset.sum_congr rfl
  intro i hi
  exact Real.sq_sqrt ((sourceGram_posSemidef W N).eigenvalues_nonneg i)

/-- The sixth spectral moment is the sum of cubes of the Gram eigenvalues,
the real quantity represented by the cubic trace. -/
theorem sourceGram_sqrtEigen_six_sum_eq_cube_sum
    (W : Finset ℝ) (N : ℕ) :
    (∑ i : SourceRow W,
        Real.sqrt ((sourceGram_posSemidef W N).1.eigenvalues i) ^ 6) =
      ∑ i : SourceRow W,
        ((sourceGram_posSemidef W N).1.eigenvalues i) ^ 3 := by
  apply Finset.sum_congr rfl
  intro i hi
  have hs := Real.sq_sqrt ((sourceGram_posSemidef W N).eigenvalues_nonneg i)
  calc
    Real.sqrt ((sourceGram_posSemidef W N).1.eigenvalues i) ^ 6 =
        (Real.sqrt ((sourceGram_posSemidef W N).1.eigenvalues i) ^ 2) ^ 3 := by ring
    _ = ((sourceGram_posSemidef W N).1.eigenvalues i) ^ 3 := by rw [hs]

/-- The cubic eigenvalue moment is exactly the literal cubic matrix trace. -/
theorem sourceTraceCube_eq_sum_eigenvalues_cube
    (W : Finset ℝ) (N : ℕ) :
    sourceTraceCube W N =
      ∑ i : SourceRow W,
        (((sourceGram_posSemidef W N).1.eigenvalues i : ℂ) ^ 3) := by
  let A := sourceGram W N
  let hA : A.IsHermitian := (sourceGram_posSemidef W N).1
  let ev : SourceRow W → ℝ := hA.eigenvalues
  let D : Matrix (SourceRow W) (SourceRow W) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ ev)
  let φ := Unitary.conjStarAlgAut ℂ
    (Matrix (SourceRow W) (SourceRow W) ℂ) hA.eigenvectorUnitary
  change (A ^ 3).trace = ∑ i, ((ev i : ℂ) ^ 3)
  have hs : A = φ D := hA.spectral_theorem
  rw [hs]
  rw [← map_pow]
  change (((hA.eigenvectorUnitary :
      Matrix (SourceRow W) (SourceRow W) ℂ) * D ^ 3 *
      star (hA.eigenvectorUnitary :
        Matrix (SourceRow W) (SourceRow W) ℂ))).trace = _
  rw [Matrix.trace_mul_cycle]
  rw [Unitary.coe_star_mul_self, one_mul]
  have hD : D ^ 3 = Matrix.diagonal (fun i => ((ev i : ℂ) ^ 3)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, pow_succ]
    · simp [D, pow_succ, hij]
  rw [hD, Matrix.trace_diagonal]

theorem sourceGram_cube_sum_eq_traceCube_re
    (W : Finset ℝ) (N : ℕ) :
    (∑ i : SourceRow W,
        ((sourceGram_posSemidef W N).1.eigenvalues i) ^ 3) =
      (sourceTraceCube W N).re := by
  have h := congrArg Complex.re
    (sourceTraceCube_eq_sum_eigenvalues_cube W N)
  have hp (x : ℝ) : ((x : ℂ) ^ 3).re = x ^ 3 := by
    rw [← Complex.ofReal_pow]
    exact Complex.ofReal_re _
  simpa only [Complex.re_sum, hp] using h.symm

/-- Trace form of source Lemma 4.2 for the literal Gram matrix. -/
theorem sourceGram_eigenvalue_le_trace_defect
    (W : Finset ℝ) (N : ℕ) (i₀ : SourceRow W) :
    Real.sqrt ((sourceGram_posSemidef W N).1.eigenvalues i₀) ≤
      2 * ((sourceTraceCube W N).re -
        (sourceTraceOne W N).re ^ 3 / (W.card : ℝ) ^ 2) ^
          (1 / 6 : ℝ) +
      2 * Real.sqrt ((sourceTraceOne W N).re / (W.card : ℝ)) := by
  have h := sourceGram_eigenvalue_lemma42 W N i₀
  rw [sourceGram_sqrtEigen_sq_sum_eq_trace_re,
    sourceGram_sqrtEigen_six_sum_eq_cube_sum,
    sourceGram_cube_sum_eq_traceCube_re] at h
  exact h

end
end GuthMaynardLemma42Gram

#print axioms GuthMaynardLemma42Gram.sourceGram_posSemidef
#print axioms GuthMaynardLemma42Gram.sourceGram_eigenvalue_lemma42
#print axioms GuthMaynardLemma42Gram.sourceGram_sqrtEigen_sq_sum_eq_trace_re
#print axioms GuthMaynardLemma42Gram.sourceGram_sqrtEigen_six_sum_eq_cube_sum
#print axioms GuthMaynardLemma42Gram.sourceTraceCube_eq_sum_eigenvalues_cube
#print axioms GuthMaynardLemma42Gram.sourceGram_eigenvalue_le_trace_defect
