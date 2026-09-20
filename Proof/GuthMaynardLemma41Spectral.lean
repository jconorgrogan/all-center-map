import GuthMaynardLemma41Operator
import GuthMaynardLemma42Gram
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! # The top singular value of the literal Guth--Maynard matrix -/

namespace GuthMaynardLemma41Spectral

open scoped Matrix.Norms.L2Operator
open GuthMaynardSectionFourTrace GuthMaynardLemma41Operator
open GuthMaynardLemma42Gram

noncomputable section

/-- The operator norm squared of the literal rectangular matrix is the
operator norm of its row Gram matrix. -/
theorem sourceMatrixOperator_norm_sq_eq_sourceGram_norm
    (W : Finset ℝ) (N : ℕ) :
    ‖sourceMatrixOperator W N‖ ^ 2 = ‖sourceGram W N‖ := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self
    (Matrix.conjTranspose (sourceMatrix W N))
  simp only [Matrix.conjTranspose_conjTranspose] at h
  have hop : ‖sourceMatrix W N‖ = ‖sourceMatrixOperator W N‖ := by
    simpa [sourceMatrixOperator] using
      (Matrix.l2_opNorm_def (sourceMatrix W N))
  rw [sourceGram, h, Matrix.l2_opNorm_conjTranspose, hop]
  ring

/-- On a nonempty row set, the operator norm squared is attained by one of
 the nonnegative eigenvalues of the literal Gram matrix. -/
theorem exists_sourceGram_eigenvalue_eq_operator_norm_sq
    (W : Finset ℝ) (N : ℕ) (hW : W.Nonempty) :
    ∃ i₀ : SourceRow W,
      ((sourceGram_posSemidef W N).1.eigenvalues i₀) =
        ‖sourceMatrixOperator W N‖ ^ 2 := by
  let hA : (sourceGram W N).IsHermitian := (sourceGram_posSemidef W N).1
  let ev : SourceRow W → ℝ := hA.eigenvalues
  have hrow : Nonempty (SourceRow W) := by
    rcases hW with ⟨t, ht⟩
    exact ⟨⟨t, ht⟩⟩
  letI : Nonempty (SourceRow W) := hrow
  obtain ⟨i₀, hi₀mem, hi₀max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (SourceRow W)) ev Finset.univ_nonempty
  refine ⟨i₀, ?_⟩
  have hev0 : 0 ≤ ev i₀ := (sourceGram_posSemidef W N).eigenvalues_nonneg i₀
  have hdiag : ‖(Matrix.diagonal (RCLike.ofReal ∘ ev) :
      Matrix (SourceRow W) (SourceRow W) ℂ)‖ = ev i₀ := by
    rw [Matrix.l2_opNorm_diagonal]
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg hev0]
      intro i
      change ‖(ev i : ℂ)‖ ≤ ev i₀
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ((sourceGram_posSemidef W N).eigenvalues_nonneg i)]
      exact hi₀max i (Finset.mem_univ i)
    · have hle := norm_le_pi_norm (RCLike.ofReal ∘ ev : SourceRow W → ℂ) i₀
      change ‖(ev i₀ : ℂ)‖ ≤ _ at hle
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hev0] at hle
      exact hle
  have hspec := hA.spectral_theorem
  have hgram : ‖sourceGram W N‖ = ev i₀ := by
    calc
      ‖sourceGram W N‖ =
          ‖(Unitary.conjStarAlgAut ℂ
              (Matrix (SourceRow W) (SourceRow W) ℂ)
              hA.eigenvectorUnitary)
            (Matrix.diagonal (RCLike.ofReal ∘ ev))‖ := congrArg norm hspec
      _ = ‖(Matrix.diagonal (RCLike.ofReal ∘ ev) :
          Matrix (SourceRow W) (SourceRow W) ℂ)‖ := by
            rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
              CStarRing.norm_mul_coe_unitary,
              CStarRing.norm_coe_unitary_mul]
      _ = ev i₀ := hdiag
  change ev i₀ = ‖sourceMatrixOperator W N‖ ^ 2
  rw [sourceMatrixOperator_norm_sq_eq_sourceGram_norm, hgram]

end
end GuthMaynardLemma41Spectral

#print axioms GuthMaynardLemma41Spectral.sourceMatrixOperator_norm_sq_eq_sourceGram_norm
#print axioms GuthMaynardLemma41Spectral.exists_sourceGram_eigenvalue_eq_operator_norm_sq
