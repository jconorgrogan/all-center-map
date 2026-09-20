import GuthMaynardS3LiteralFullSelectionActual
import GuthMaynardS3LiteralUniform106Fourier

namespace GuthMaynardS3LiteralSelectedAffineUniform106

open scoped BigOperators
open GuthMaynardS3LiteralFullSelection
open GuthMaynardS3LiteralFullSelectionActual
open GuthMaynardS3LiteralBalancedSectorGeometry
open GuthMaynardS3LiteralActualSixSectorBound
open GuthMaynardS3LiteralTruncation
open GuthMaynardEquation55Infinite
open GuthMaynardS3LiteralRadialDecay
open GuthMaynardS3LiteralLocalization
open GuthMaynardS3LiteralUniform106Radial
open GuthMaynardS3LiteralUniform106Fourier
open GuthMaynardSectionThreeCutoffDerivativeBudget

noncomputable section

/-- The selected affine block after the literal finite-frequency selector.  The
radial tail created when replacing the selected block norm by its affine
majorant remains explicit, while the prefix-to-infinite error is the proved
uniform-106 Fourier error at the canonical cutoff. -/
theorem norm_sourceS3_le_selected_affine_uniform106
    {N : ℕ} (hN : 0 < N)
    {T eta : ℝ} (hT : 1 ≤ T) (heta : 0 < eta)
    (hcut : 2 * (N : ℝ) ≤ Real.rpow T (1 + eta))
    (W : Finset ℝ)
    (hdiam : ∀ a ∈ W, ∀ b ∈ W, |a - b| ≤ T)
    (hNle : (N : ℝ) ≤ T) (hWle : (W.card : ℝ) ≤ 2 * T)
    (hslack : GuthMaynardS3LiteralUniform106Radial.s3Rho T eta /
      (N : ℝ) ≤ 1) :
    ∃ i ∈ GuthMaynardS3LiteralBalancedSectorGeometry.dyadicExponents
        (GuthMaynardS3LiteralUniform106Radial.s3FrequencyCutoff T eta N),
      ∃ k ∈ GuthMaynardS3LiteralBalancedSectorGeometry.dyadicExponents
        (GuthMaynardS3LiteralUniform106Radial.s3FrequencyCutoff T eta N),
        ∃ d ∈ Finset.range 4,
          ‖sourceS3 N W‖ ≤
            6 * ((orderedBalancedKeys
              (GuthMaynardS3LiteralUniform106Radial.s3FrequencyCutoff T eta N)).card : ℝ) *
              orderedBalancedBlockAffine N W
                (GuthMaynardS3LiteralUniform106Radial.s3Rho T eta)
                (GuthMaynardS3LiteralUniform106Radial.s3FrequencyCutoff T eta N) i k d +
            (((prefixFrequencyCube
              (GuthMaynardS3LiteralUniform106Radial.s3FrequencyCutoff T eta N)).card : ℝ) +
              6 * ((orderedBalancedKeys
                (GuthMaynardS3LiteralUniform106Radial.s3FrequencyCutoff T eta N)).card : ℝ) *
                ((orderedBalancedBlock
                  (GuthMaynardS3LiteralUniform106Radial.s3FrequencyCutoff T eta N)
                  i k d).card : ℝ)) *
              ((9 / 4 : ℝ) * (N : ℝ) ^ 3 *
                radialDerivativeBudget
                  (GuthMaynardS3LiteralUniform106Radial.s3Uniform106DecayOrder eta) *
                (W.card : ℝ) ^ 3 /
                (GuthMaynardS3LiteralUniform106Radial.s3Rho T eta) ^
                  GuthMaynardS3LiteralUniform106Radial.s3Uniform106DecayOrder eta) +
            (24 * lemma43DerivativeConstant 0 ^ 2 *
                s3PrefixErrorCoeff eta + 6 * s3PrefixErrorCoeff eta ^ 3) *
              (8 * Real.rpow T (-100 : ℝ)) := by
  let Mcut : ℕ := GuthMaynardS3LiteralUniform106Radial.s3FrequencyCutoff T eta N
  let rho : ℝ := GuthMaynardS3LiteralUniform106Radial.s3Rho T eta
  let q : ℕ := GuthMaynardS3LiteralUniform106Radial.s3Uniform106DecayOrder eta
  have hMcut : 1 ≤ Mcut := by
    dsimp [Mcut, GuthMaynardS3LiteralUniform106Radial.s3FrequencyCutoff]
    exact le_max_left _ _
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hrho : 0 < rho := by
    dsimp [rho]
    exact GuthMaynardS3LiteralUniform106Radial.s3Rho_pos hTpos heta
  have hq : 2 ≤ q := by
    dsimp [q, GuthMaynardS3LiteralUniform106Radial.s3Uniform106DecayOrder,
      GuthMaynardS3LiteralErrorContract.s3Uniform106DecayOrder]
    have hc : 0 ≤ Nat.ceil (110 / eta) := Nat.zero_le _
    omega
  have hslack' : rho / (N : ℝ) ≤ 1 := by
    simpa [rho] using hslack
  have hsel := norm_sourceS3_le_selected_ordered_block_actual
    hN hMcut (by linarith : 0 ≤ T) W hdiam hrho hslack' hq
  obtain ⟨i, hi, k, hk, d, hd, hsel⟩ := hsel
  have hblock := orderedBalancedBlock_norm_le_affine_add_tail
    hN hrho W Mcut i k d q
  have hscale : 0 ≤ 6 * ((orderedBalancedKeys Mcut).card : ℝ) := by
    positivity
  have hblock' := mul_le_mul_of_nonneg_left hblock hscale
  have hfour := GuthMaynardS3LiteralUniform106Fourier.s3FourierError_le_uniform106
    hN hT heta hcut W hNle hWle
  have hfour' :
      3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
          prefixError T N Mcut q * prefixEnvelope T N Mcut q ^ 2 ≤
        (24 * lemma43DerivativeConstant 0 ^ 2 * s3PrefixErrorCoeff eta +
          6 * s3PrefixErrorCoeff eta ^ 3) *
          (8 * Real.rpow T (-100 : ℝ)) := by
    simpa [Mcut, q, GuthMaynardS3LiteralUniform106Fourier.s3FourierError,
      GuthMaynardS3LiteralUniform106Radial.s3Uniform106DecayOrder] using hfour
  refine ⟨i, ?_, k, ?_, d, hd, ?_⟩
  · simpa [Mcut] using hi
  · simpa [Mcut] using hk
  · have hgoal :
        ‖sourceS3 N W‖ ≤
          6 * ((orderedBalancedKeys Mcut).card : ℝ) *
              orderedBalancedBlockAffine N W rho Mcut i k d +
            (((prefixFrequencyCube Mcut).card : ℝ) +
              6 * ((orderedBalancedKeys Mcut).card : ℝ) *
                ((orderedBalancedBlock Mcut i k d).card : ℝ)) *
              ((9 / 4 : ℝ) * (N : ℝ) ^ 3 * radialDerivativeBudget q *
                (W.card : ℝ) ^ 3 / rho ^ q) +
            (24 * lemma43DerivativeConstant 0 ^ 2 *
                s3PrefixErrorCoeff eta + 6 * s3PrefixErrorCoeff eta ^ 3) *
              (8 * Real.rpow T (-100 : ℝ)) := by
      nlinarith only [hsel, hblock', hfour']
    simpa [Mcut, rho, q,
      GuthMaynardS3LiteralUniform106Radial.s3Uniform106DecayOrder] using hgoal

end
end GuthMaynardS3LiteralSelectedAffineUniform106

#print axioms GuthMaynardS3LiteralSelectedAffineUniform106.norm_sourceS3_le_selected_affine_uniform106
