import GuthMaynardS1Proposition51Endpoint

/-!
# Guth--Maynard Section 4 finite trace objects

This file introduces the literal finite matrix used in (4.2), rather than an
asymptotic surrogate.  The row and column types are the actual finite sets
`W` and `(N,2N]`.  The first identities below are the algebraic part of
Lemmas 4.1, 4.4, and 4.5, before Poisson summation and analytic error bounds.
-/

namespace GuthMaynardSectionFourTrace

open scoped BigOperators
open GuthMaynardSectionThreeCutoff

noncomputable section

abbrev SourceRow (W : Finset ℝ) := {t : ℝ // t ∈ W}
abbrev SourceColumn (N : ℕ) := {n : ℕ // n ∈ Finset.Ioc N (2 * N)}

def sourcePhase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t * Real.log n))

def sourceMatrix (W : Finset ℝ) (N : ℕ) :
    Matrix (SourceRow W) (SourceColumn N) ℂ :=
  fun t n =>
    (sectionThreeCutoffReal ((n : ℝ) / (N : ℝ)) : ℂ) *
      sourcePhase n t

def sourceCoefficientVector (b : ℕ → ℂ) (N : ℕ) : SourceColumn N → ℂ :=
  fun n => b n

/-- Literal smoothed polynomial (4.1), with the project's open-left dyadic
convention. -/
def sourceDN (b : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N),
    (sectionThreeCutoffReal ((n : ℝ) / (N : ℝ)) : ℂ) * b n *
      sourcePhase n t

/-- Matrix-vector multiplication is exactly the smoothed Dirichlet
polynomial, not merely an estimate for it. -/
theorem sourceMatrix_mulVec_eq_sourceDN
    (W : Finset ℝ) (N : ℕ) (b : ℕ → ℂ) (t : SourceRow W) :
    (sourceMatrix W N).mulVec (sourceCoefficientVector b N) t =
      sourceDN b N t := by
  unfold Matrix.mulVec dotProduct sourceMatrix sourceCoefficientVector sourceDN
  change (∑ n : SourceColumn N,
      (sectionThreeCutoffReal ((n : ℝ) / (N : ℝ)) : ℂ) *
        sourcePhase n t * b n) = _
  calc
    _ = ∑ n ∈ Finset.Ioc N (2 * N),
        (sectionThreeCutoffReal ((n : ℝ) / (N : ℝ)) : ℂ) *
          sourcePhase n t * b n :=
      (Finset.sum_subtype (s := Finset.Ioc N (2 * N)) (by simp)
        (fun n =>
          (sectionThreeCutoffReal ((n : ℝ) / (N : ℝ)) : ℂ) *
            sourcePhase n t * b n)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      ring

/-- The literal Gram matrix `M_W M_W*`. -/
def sourceGram (W : Finset ℝ) (N : ℕ) : Matrix (SourceRow W) (SourceRow W) ℂ :=
  sourceMatrix W N * Matrix.conjTranspose (sourceMatrix W N)

theorem sourceGram_apply (W : Finset ℝ) (N : ℕ)
    (t u : SourceRow W) :
    sourceGram W N t u =
      ∑ n : SourceColumn N,
        sourceMatrix W N t n * star (sourceMatrix W N u n) := by
  simp [sourceGram, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The two traces used in Lemmas 4.2--4.5. -/
def sourceTraceOne (W : Finset ℝ) (N : ℕ) : ℂ :=
  Matrix.trace (sourceGram W N)

def sourceTraceCube (W : Finset ℝ) (N : ℕ) : ℂ :=
  Matrix.trace ((sourceGram W N) ^ 3)

theorem sourceTraceOne_expand (W : Finset ℝ) (N : ℕ) :
    sourceTraceOne W N =
      ∑ t : SourceRow W, ∑ n : SourceColumn N,
        sourceMatrix W N t n * star (sourceMatrix W N t n) := by
  simp [sourceTraceOne, Matrix.trace, sourceGram_apply]

/-- Exact finite cubic closed-walk expansion.  This is the algebraic first
line of Lemma 4.5, before the three Poisson summations. -/
theorem sourceTraceCube_expand (W : Finset ℝ) (N : ℕ) :
    sourceTraceCube W N =
      ∑ t₁ : SourceRow W, ∑ t₂ : SourceRow W, ∑ t₃ : SourceRow W,
        sourceGram W N t₁ t₂ * sourceGram W N t₂ t₃ *
          sourceGram W N t₃ t₁ := by
  unfold sourceTraceCube Matrix.trace
  rw [show sourceGram W N ^ 3 =
      sourceGram W N * (sourceGram W N * sourceGram W N) by
        noncomm_ring]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro t₁ ht₁
  apply Finset.sum_congr rfl
  intro t₂ ht₂
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t₃ ht₃
  ring

end
end GuthMaynardSectionFourTrace

#print axioms GuthMaynardSectionFourTrace.sourceMatrix_mulVec_eq_sourceDN
#print axioms GuthMaynardSectionFourTrace.sourceGram_apply
#print axioms GuthMaynardSectionFourTrace.sourceTraceOne_expand
#print axioms GuthMaynardSectionFourTrace.sourceTraceCube_expand
