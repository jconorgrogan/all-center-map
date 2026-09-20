import GuthMaynardS3LiteralSelectionLedger
import GuthMaynardS3LiteralFinalSeamParameterAdapter
import GuthMaynardS3BlockEnergyEnvelope
import GuthMaynardS3BlockSqrtLogEnvelope

open scoped Real
open GuthMaynardHeathBrownInterface
open GuthMaynardEquation55Infinite
open GuthMaynardS3LiteralLemma82
open GuthMaynardS3LiteralUniform106Radial
open GuthMaynardS3LiteralBalancedSectorGeometry
open GuthMaynardS3LiteralLemma83Energy
open GuthMaynardS3LiteralSelectionLedger
open GuthMaynardS3LiteralFinalSeamParameterAdapter
open GuthMaynardS3BlockEnergyEnvelope
open GuthMaynardS3BlockSqrtLogEnvelope

noncomputable section
set_option maxHeartbeats 1200000
namespace GuthMaynardS3FinalSeamSourceBound

/-- Final-seam source consumer.  Selection supplies literal witnesses, the
block envelope supplies the squared affine estimate, and the scalar square-root
ledger converts the two into the displayed source bound. -/
theorem norm_sourceS3_le_final_seam
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∃ T0 : ℝ, 0 < T0 ∧
      ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ),
        256 ≤ N → T = (N : ℝ) ^ (6 / 5 : ℝ) →
        T0 ≤ 64 * T ^ 3 →
        (W.card : ℝ) ≤ 2 * T →
        TEtaSeparated W T eta →
        ContainedInIntervalOfLength W T →
        ‖sourceS3 N W‖ ≤
          C * T ^ (6 * eta) *
            (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
              T * (N : ℝ) * Real.sqrt (W.card : ℝ) *
                Real.sqrt (sourceApproximateAdditiveEnergy W)) +
          C * T ^ (-100 : ℝ) := by
  have hetaone : eta ≤ 1 := by linarith
  obtain ⟨Csel, hCsel, hsel⟩ :=
    exists_selected_affine_log_ledger heta hetaone
  obtain ⟨Cm, Ct, T0, hCm, hCt, hT0, hblock⟩ :=
    block_energy_envelope heta heta1
  let Qeta : ℝ := (7 + 2 / Real.log 2) * (1 + 3 / eta) ^ 3
  let Cfinal : ℝ := Csel * (Real.sqrt Cm * Qeta + Real.sqrt Ct + 1) + 1
  have hQeta : 0 ≤ Qeta := by
    dsimp [Qeta]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hCfinal : 0 < Cfinal := by
    dsimp [Cfinal]
    positivity
  refine ⟨Cfinal, hCfinal, T0, hT0, ?_⟩
  intro N T W hN256 hTdef hUT hcard hsep hcontained
  have hNpos : 0 < N := by omega
  have hNposR : 0 < (N : ℝ) := Nat.cast_pos.mpr hNpos
  have hNleT : (N : ℝ) ≤ T := by
    rw [hTdef]
    calc
      (N : ℝ) = Real.rpow (N : ℝ) 1 := by
        symm
        exact Real.rpow_one _
      _ ≤ Real.rpow (N : ℝ) (6 / 5 : ℝ) := by
        have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hT1 : 1 ≤ T := (final_seam_eventual_bounds hN256 hTdef heta heta1).1
  have hdiam : ∀ a ∈ W, ∀ b ∈ W, |a - b| ≤ T := by
    rcases hcontained with ⟨x, hx⟩
    intro a ha b hb
    have ha' := hx a ha
    have hb' := hx b hb
    rw [abs_le]
    constructor <;> nlinarith [ha'.1, ha'.2, hb'.1, hb'.2]
  have hcut : 2 * (N : ℝ) ≤ Real.rpow T (1 + eta) := by
    have hb := final_seam_eventual_bounds hN256 hTdef heta heta1
    exact hb.2.1
  have hrhoN : 16 * s3Rho T eta ≤ (N : ℝ) := by
    have hb := final_seam_eventual_bounds hN256 hTdef heta heta1
    exact hb.2.2
  have hslack : s3Rho T eta / (N : ℝ) ≤ 1 := by
    have hrho : 0 ≤ s3Rho T eta :=
      (s3Rho_pos (lt_of_lt_of_le zero_lt_one hT1) heta).le
    apply (div_le_iff₀ hNposR).2
    linarith
  obtain ⟨i, hi, k, hk, d, hd, hselected⟩ :=
    hsel W hNpos hT1 hcut hdiam hNleT hcard hslack
  have hparam := final_seam_parameter_adapter hN256 hTdef heta heta1 hk W hcard
  have hK : (2 : ℝ) ^ k ≤ T ^ 2 := by
    have hh := hparam.2.2.1
    nlinarith
  have henergy := hblock N T W (s3FrequencyCutoff T eta N) i k d
    hN256 hTdef hUT hcard hsep hcontained hk (Finset.mem_range.mp hd)
  have hR : 0 ≤ (W.card : ℝ) := by positivity
  have hE : 0 ≤ (sourceApproximateAdditiveEnergy W : ℝ) := by positivity
  have hX := block_sqrt_log_envelope (T := T) (eta := eta)
    (R := (W.card : ℝ)) (E := (sourceApproximateAdditiveEnergy W : ℝ))
    (n := (N : ℝ)) (Cm := Cm) (Ct := Ct) (X :=
      orderedBalancedBlockAffine N W (s3Rho T eta)
        (s3FrequencyCutoff T eta N) i k d)
    hT1 heta hK hR hE (by positivity) hCm hCt henergy
  have hXabs :
      (1 + Real.log T) ^ 2 *
          orderedBalancedBlockAffine N W (s3Rho T eta)
            (s3FrequencyCutoff T eta N) i k d ≤
      (1 + Real.log T) ^ 2 *
        |orderedBalancedBlockAffine N W (s3Rho T eta)
            (s3FrequencyCutoff T eta N) i k d| := by
    have hlog : 0 ≤ (1 + Real.log T) ^ 2 := sq_nonneg _
    exact mul_le_mul_of_nonneg_left (le_abs_self _) hlog
  have hCselmain := mul_le_mul_of_nonneg_left hX hCsel
  have hCselabs := mul_le_mul_of_nonneg_left hXabs hCsel
  have hsource' : ‖sourceS3 N W‖ ≤
      Csel * ((1 + Real.log T) ^ 2 *
        |orderedBalancedBlockAffine N W (s3Rho T eta)
          (s3FrequencyCutoff T eta N) i k d|) + Csel * T^(-100 : ℝ) := by
    calc
      ‖sourceS3 N W‖ ≤
          Csel * (1 + Real.log T) ^ 2 *
              orderedBalancedBlockAffine N W (s3Rho T eta)
                (s3FrequencyCutoff T eta N) i k d + Csel * T^(-100 : ℝ) :=
        hselected
      _ = Csel * ((1 + Real.log T) ^ 2 *
          orderedBalancedBlockAffine N W (s3Rho T eta)
            (s3FrequencyCutoff T eta N) i k d) + Csel * T^(-100 : ℝ) := by ring
      _ ≤ _ := add_le_add_left hCselabs (Csel * T^(-100 : ℝ))
  have hmain0 : 0 ≤ T ^ (6 * eta) *
      (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
        T * (N : ℝ) * Real.sqrt (W.card : ℝ) *
          Real.sqrt (sourceApproximateAdditiveEnergy W)) := by positivity
  have htail0 : 0 ≤ T ^ (-100 : ℝ) := by positivity
  have hXQ :
      (1 + Real.log T) ^ 2 *
          |orderedBalancedBlockAffine N W (s3Rho T eta)
            (s3FrequencyCutoff T eta N) i k d| ≤
      Real.sqrt Cm * Qeta * T^(6*eta) *
          (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
            T * (N : ℝ) * Real.sqrt (W.card : ℝ) *
              Real.sqrt (sourceApproximateAdditiveEnergy W)) +
        Real.sqrt Ct * T^(-100 : ℝ) := by
    simpa [Qeta] using hX
  have hcoefmain : Csel * Real.sqrt Cm * Qeta ≤ Cfinal := by
    change Csel * Real.sqrt Cm * Qeta ≤
      Csel * (Real.sqrt Cm * Qeta + Real.sqrt Ct + 1) + 1
    have hnon : 0 ≤ Csel * (Real.sqrt Ct + 1) := by positivity
    calc
      Csel * Real.sqrt Cm * Qeta ≤
          Csel * Real.sqrt Cm * Qeta + Csel * (Real.sqrt Ct + 1) := by linarith
      _ = Csel * (Real.sqrt Cm * Qeta + Real.sqrt Ct + 1) := by ring
      _ ≤ Csel * (Real.sqrt Cm * Qeta + Real.sqrt Ct + 1) + 1 := by linarith
  have hcoefTail : Csel * (Real.sqrt Ct + 1) ≤ Cfinal := by
    change Csel * (Real.sqrt Ct + 1) ≤
      Csel * (Real.sqrt Cm * Qeta + Real.sqrt Ct + 1) + 1
    have hnon : 0 ≤ Csel * (Real.sqrt Cm * Qeta) := by positivity
    calc
      Csel * (Real.sqrt Ct + 1) ≤
          Csel * (Real.sqrt Cm * Qeta + Real.sqrt Ct + 1) := by linarith
      _ ≤ Csel * (Real.sqrt Cm * Qeta + Real.sqrt Ct + 1) + 1 := by linarith
  calc
    ‖sourceS3 N W‖ ≤
        Csel * ((1 + Real.log T) ^ 2 *
          |orderedBalancedBlockAffine N W (s3Rho T eta)
            (s3FrequencyCutoff T eta N) i k d|) + Csel * T^(-100 : ℝ) := hsource'
    _ ≤ Csel * (Real.sqrt Cm * Qeta * T^(6*eta) *
          (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
            T * (N : ℝ) * Real.sqrt (W.card : ℝ) *
              Real.sqrt (sourceApproximateAdditiveEnergy W))) +
        Csel * (Real.sqrt Ct + 1) * T^(-100 : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hXQ hCsel
      have hm' := add_le_add_right hm (Csel * T^(-100 : ℝ))
      simpa only [one_mul, mul_add, add_mul, mul_assoc, add_assoc, add_left_comm, add_comm] using hm'
    _ ≤ Cfinal * T^(6*eta) *
          (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
            T * (N : ℝ) * Real.sqrt (W.card : ℝ) *
              Real.sqrt (sourceApproximateAdditiveEnergy W)) +
        Cfinal * T^(-100 : ℝ) := by
      have hm := mul_le_mul_of_nonneg_right hcoefmain hmain0
      have ht := mul_le_mul_of_nonneg_right hcoefTail htail0
      nlinarith

end GuthMaynardS3FinalSeamSourceBound

#print axioms GuthMaynardS3FinalSeamSourceBound.norm_sourceS3_le_final_seam
