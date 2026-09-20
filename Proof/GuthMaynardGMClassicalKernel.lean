import GuthMaynardGMHighValueComplement
import RecenteredSampling

open scoped BigOperators ComplexConjugate
open CGLProofDAG
open GuthMaynardSectionFourTrace

noncomputable section
namespace GuthMaynardGMHighValueComplement

/-- The unsmoothed dyadic kernel used by the classical Montgomery--Halasz
route.  It is independent of the coefficients and of the large-value level. -/
def gmDyadicKernel (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N), sourcePhase n t

/-- Exact pointwise source leaf needed for the classical route.  The two
regimes are written literally so a future proof cannot silently introduce a
`V`-dependent estimate. -/
def gmDyadicKernelPointwiseBound : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ,
    ‖gmDyadicKernel N t‖ ≤
      4 * ((N : ℝ) / (1 + |t|) + Real.sqrt |t| + Real.sqrt (N : ℝ))

/-- The independent spacing/shell leaf needed after the pointwise kernel
bound.  It is a finite combinatorial estimate, stated before any Halasz
absorption and with the literal interval length `L`. -/
def gmDyadicKernelShellBound : Prop :=
  ∀ C : ℝ, 0 < C →
    ∀ (L : ℝ) (N : ℕ) (W : Finset ℝ),
      1 ≤ N → 1 ≤ L → OneSeparated W →
      (∀ t ∈ W, 0 ≤ t ∧ t ≤ L) →
      ∀ t ∈ W,
        (∑ u ∈ W,
          ((N : ℝ) / (1 + |u - t|) + Real.sqrt |u - t| +
            Real.sqrt (N : ℝ))) ≤
          C * ((N : ℝ) * Real.log (2 * L) +
            (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ)))

/-- From the literal pointwise kernel leaf and the independent shell leaf,
obtain the exact double-correlation bound consumed by the Halasz front.  No
large-value level occurs in this reduction. -/
theorem gm_kernel_correlation_bound_of_pointwise_shell
    (hK : gmDyadicKernelPointwiseBound)
    (hShell : gmDyadicKernelShellBound)
    {L : ℝ} {N : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L)
    (W : Finset ℝ) (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ L)
    (eta : ℝ → ℂ) (heta : ∀ t ∈ W, ‖eta t‖ = 1) :
    ‖∑ t ∈ W, ∑ u ∈ W,
        conj (eta t) * eta u * gmDyadicKernel N (u - t)‖ ≤
      4 * (W.card : ℝ) *
        (Real.sqrt (N : ℝ) +
          (N : ℝ) * Real.log (2 * L) +
          (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ))) := by
  have hpoint : ∀ t ∈ W, ∀ u ∈ W,
      ‖gmDyadicKernel N (u - t)‖ ≤
        4 * ((N : ℝ) / (1 + |u - t|) + Real.sqrt |u - t| +
          Real.sqrt (N : ℝ)) := by
    intro t ht u hu
    exact hK N hN (u - t)
  have hsum : ∀ t ∈ W,
      ∑ u ∈ W, ‖gmDyadicKernel N (u - t)‖ ≤
        4 * (N : ℝ) * Real.log (2 * L) +
        4 * (W.card : ℝ) *
          (Real.sqrt L + Real.sqrt (N : ℝ)) := by
    intro t ht
    have hs := hShell 1 (by norm_num) L N W hN hL hsep hheight t ht
    calc
      ∑ u ∈ W, ‖gmDyadicKernel N (u - t)‖ ≤
          ∑ u ∈ W, 4 *
            ((N : ℝ) / (1 + |u - t|) + Real.sqrt |u - t| +
              Real.sqrt (N : ℝ)) := by
        apply Finset.sum_le_sum
        intro u hu
        exact hpoint t ht u hu
      _ = 4 * ∑ u ∈ W,
            ((N : ℝ) / (1 + |u - t|) + Real.sqrt |u - t| +
              Real.sqrt (N : ℝ)) := by
        simp_rw [Finset.mul_sum]
      _ ≤ 4 * ((N : ℝ) * Real.log (2 * L) +
          (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ))) := by
        simpa using (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 4))
      _ = 4 * (N : ℝ) * Real.log (2 * L) +
          4 * (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ)) := by ring
  calc
    ‖∑ t ∈ W, ∑ u ∈ W,
        conj (eta t) * eta u * gmDyadicKernel N (u - t)‖ ≤
      ∑ t ∈ W, ‖∑ u ∈ W,
        conj (eta t) * eta u * gmDyadicKernel N (u - t)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ t ∈ W, ∑ u ∈ W,
        ‖conj (eta t) * eta u * gmDyadicKernel N (u - t)‖ := by
      apply Finset.sum_le_sum
      intro t ht
      exact norm_sum_le _ _
    _ = ∑ t ∈ W, ∑ u ∈ W, ‖gmDyadicKernel N (u - t)‖ := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro u hu
      have hstar : ‖(starRingEnd ℂ) (eta t)‖ = 1 := by
        calc
          ‖(starRingEnd ℂ) (eta t)‖ = ‖eta t‖ := norm_star _
          _ = 1 := heta t ht
      rw [norm_mul, norm_mul, hstar, heta u hu]
      norm_num
    _ ≤ ∑ t ∈ W,
        (4 * (N : ℝ) * Real.log (2 * L) +
          4 * (W.card : ℝ) *
            (Real.sqrt L + Real.sqrt (N : ℝ))) := by
      apply Finset.sum_le_sum
      intro t ht
      exact hsum t ht
    _ = 4 * (W.card : ℝ) *
        ((N : ℝ) * Real.log (2 * L) +
          (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ))) := by
      simp only [Finset.sum_add_distrib]
      simp [nsmul_eq_mul]
      ring
    _ ≤ 4 * (W.card : ℝ) *
        (Real.sqrt (N : ℝ) + (N : ℝ) * Real.log (2 * L) +
          (W.card : ℝ) * (Real.sqrt L + Real.sqrt (N : ℝ))) := by
      gcongr
      nlinarith [Real.sqrt_nonneg (N : ℝ)]

end GuthMaynardGMHighValueComplement

#print axioms GuthMaynardGMHighValueComplement.gm_kernel_correlation_bound_of_pointwise_shell
