import GuthMaynardS3LiteralScaleComparison

/-! # Exact nonzero-frequency dyadic block supplied to Proposition 9.1 -/

namespace GuthMaynardS3LiteralDyadicBlock

open scoped BigOperators
open MeasureTheory
open GuthMaynardS3LiteralAffineReduction GuthMaynardS3LiteralScaleComparison
open GuthMaynardS3LiteralLocalization
open GuthMaynardS3LiteralRadialDecay GuthMaynardEquation55Infinite GuthMaynardEquation55Split

noncomputable section

theorem affineProfileIntegral_nonneg (B : ℝ) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    0 ≤ affineProfileIntegral B W m1 m2 m3 := by
  apply integral_nonneg
  intro v
  unfold GuthMaynardS3LiteralProfile.smoothedRatio
  positivity

/-- Common-profile form of the literal per-frequency reduction. -/
theorem norm_sourceIm_le_common_profile {N : ℕ} (hN : 0<N)
    {M rho : ℝ} (hM : 0<M) (hrho : 0<rho) (W : Finset ℝ)
    (m1 m2 m3 : ℤ) (hlo : M ≤ |(m2 : ℝ)|) (hhi : |(m2 : ℝ)| ≤ 2*M) (q : ℕ) :
    ‖sourceIm N W m1 m2 m3‖ ≤
      (16*radialDerivativeBudget 0*rho*(N : ℝ)^2/M) *
        affineProfileIntegral ((N : ℝ)*M/(4*rho)) W m1 m2 m3 +
      (9/4 : ℝ)*(N : ℝ)^3*radialDerivativeBudget q*(W.card : ℝ)^3/rho^q := by
  have hmPos : 0< |(m2 : ℝ)| := hM.trans_le hlo
  have hm2 : m2≠0 := by intro hz; simp [hz] at hmPos
  have hNR : 0<(N : ℝ) := Nat.cast_pos.mpr hN
  let B0 := (N : ℝ)*M/(4*rho)
  let B := (N : ℝ)*|(m2 : ℝ)|/(2*rho)
  have hB0 : 0<B0 := by dsimp [B0]; positivity
  have hBlo : 2*B0 ≤ B := by
    dsimp [B0,B]
    apply (le_div_iff₀ (by positivity : 0<2*rho)).2
    have hm := mul_le_mul_of_nonneg_left hlo hNR.le
    field_simp
    nlinarith only [hlo]
  have hBhi : B ≤ 4*B0 := by
    dsimp [B0,B]
    apply (div_le_iff₀ (by positivity : 0<2*rho)).2
    have hm := mul_le_mul_of_nonneg_left hhi hNR.le
    field_simp
    nlinarith only [hhi]
  have hp := affineProfileIntegral_le_four hB0 hBlo hBhi W m1 m2 m3
  have hc := div_le_div_of_nonneg_left
    (show 0 ≤ 4*radialDerivativeBudget 0*rho*(N : ℝ)^2 by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (radialDerivativeBudget_nonneg 0)) hrho.le) (sq_nonneg _)) hM hlo
  have hm := mul_le_mul hc hp (affineProfileIntegral_nonneg B W m1 m2 m3)
    (show 0 ≤ 4*radialDerivativeBudget 0*rho*(N : ℝ)^2/M by
      exact div_nonneg (by have hC0 := radialDerivativeBudget_nonneg 0; positivity) hM.le)
  have hh := norm_sourceIm_le_affine hN W m1 m2 m3 hm2 hrho q
  apply hh.trans
  have hmain : (4*radialDerivativeBudget 0*rho*(N : ℝ)^2/|(m2 : ℝ)|)*
      affineProfileIntegral B W m1 m2 m3 ≤
      (16*radialDerivativeBudget 0*rho*(N : ℝ)^2/M)*
        affineProfileIntegral B0 W m1 m2 m3 := by
    convert hm using 1 <;> ring
  linarith only [hmain]

/-- A literal finite S3 block. The nonzero-frequency mask is part of the
hypothesis, so none of the coordinate planes enters this block. -/
theorem norm_sourceS3_block_le {N : ℕ} (hN : 0<N)
    {M rho : ℝ} (hM : 0<M) (hrho : 0<rho) (W : Finset ℝ)
    (Omega : Finset Frequency) (q : ℕ)
    (hmask : ∀ p∈Omega,exactlyThreeNonzero p.1.1 p.1.2 p.2)
    (hlo : ∀ p∈Omega,M ≤ |(p.1.2 : ℝ)|)
    (hhi : ∀ p∈Omega,|(p.1.2 : ℝ)| ≤ 2*M) :
    ‖∑ p∈Omega,if exactlyThreeNonzero p.1.1 p.1.2 p.2 then frequencyTerm N W p else 0‖ ≤
      (16*radialDerivativeBudget 0*rho*(N : ℝ)^2/M) *
        (∑ p∈Omega,affineProfileIntegral ((N : ℝ)*M/(4*rho)) W p.1.1 p.1.2 p.2) +
      (Omega.card : ℝ)*((9/4 : ℝ)*(N : ℝ)^3*radialDerivativeBudget q*(W.card : ℝ)^3/rho^q) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p∈Omega,((16*radialDerivativeBudget 0*rho*(N : ℝ)^2/M)*
        affineProfileIntegral ((N : ℝ)*M/(4*rho)) W p.1.1 p.1.2 p.2 +
        (9/4 : ℝ)*(N : ℝ)^3*radialDerivativeBudget q*(W.card : ℝ)^3/rho^q) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [if_pos (hmask p hp)]
      exact norm_sourceIm_le_common_profile hN hM hrho W p.1.1 p.1.2 p.2 (hlo p hp) (hhi p hp) q
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum]; simp

end
end GuthMaynardS3LiteralDyadicBlock

#print axioms GuthMaynardS3LiteralDyadicBlock.norm_sourceS3_block_le
