import GuthMaynardS3LiteralTruncation
import GuthMaynardS3LiteralAffineReduction

/-! # Global literal S3 reduction to concrete affine profile integrals

The infinite Fourier cube is truncated with the actual smooth cutoff tail,
then each retained frequency is bounded by the constructed affine profile.
No S3 estimate or affine-incidence budget is a hypothesis.
-/

namespace GuthMaynardS3LiteralGlobalReduction

open scoped BigOperators
open GuthMaynardS3LiteralTruncation GuthMaynardS3LiteralAffineReduction
open GuthMaynardS3LiteralRadialDecay GuthMaynardEquation55Infinite

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def affineFrequencyMajorant (N : ℕ) (W : Finset ℝ) (rho : ℝ) (p : Frequency) : ℝ :=
  (4*radialDerivativeBudget 0*rho*(N : ℝ)^2/|(p.1.2 : ℝ)|) *
    affineProfileIntegral ((N : ℝ)*|(p.1.2 : ℝ)|/(2*rho)) W p.1.1 p.1.2 p.2

/-- A global exact-source reduction with separately visible radial and
Fourier-truncation errors. The retained affine sum is still to be estimated
by the source's profile and incidence arguments. -/
theorem norm_sourceS3_le_affine_sum_add_errors {N M j : ℕ} (hN : 0<N)
    (hM : 1 ≤ M) (hj : 2 ≤ j) {T rho : ℝ} (hT : 0 ≤ T) (hrho : 0<rho)
    (W : Finset ℝ) (hdiam : ∀ a∈W,∀ b∈W,|a-b| ≤ T) (q : ℕ) :
    ‖sourceS3 N W‖ ≤
      (∑ p∈prefixFrequencyCube M,affineFrequencyMajorant N W rho p) +
      ((prefixFrequencyCube M).card : ℝ)*
        ((9/4 : ℝ)*(N : ℝ)^3*radialDerivativeBudget q*(W.card : ℝ)^3/rho^q) +
      3*(N : ℝ)^3*(W.card : ℝ)^3*prefixError T N M j*(prefixEnvelope T N M j)^2 := by
  have htr := norm_sourceS3_le_finite_block_add_error hN hM hj hT W hdiam
  have hfinite :
      ‖∑ p∈prefixFrequencyCube M,
        if GuthMaynardEquation55Split.exactlyThreeNonzero p.1.1 p.1.2 p.2 then frequencyTerm N W p else 0‖ ≤
      (∑ p∈prefixFrequencyCube M,affineFrequencyMajorant N W rho p) +
      ((prefixFrequencyCube M).card : ℝ)*
        ((9/4 : ℝ)*(N : ℝ)^3*radialDerivativeBudget q*(W.card : ℝ)^3/rho^q) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ p∈prefixFrequencyCube M,(affineFrequencyMajorant N W rho p +
          (9/4 : ℝ)*(N : ℝ)^3*radialDerivativeBudget q*(W.card : ℝ)^3/rho^q) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨h12,h3⟩ := Finset.mem_product.mp hp
        obtain ⟨h1,h2⟩ := Finset.mem_product.mp h12
        have hm : GuthMaynardEquation55Split.exactlyThreeNonzero p.1.1 p.1.2 p.2 :=
          ⟨nonzeroPrefix_ne_zero h1,nonzeroPrefix_ne_zero h2,nonzeroPrefix_ne_zero h3⟩
        rw [if_pos hm]
        exact norm_sourceIm_le_affine hN W p.1.1 p.1.2 p.2 hm.2.1 hrho q
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  linarith only [htr,hfinite]

end
end GuthMaynardS3LiteralGlobalReduction

#print axioms GuthMaynardS3LiteralGlobalReduction.norm_sourceS3_le_affine_sum_add_errors
