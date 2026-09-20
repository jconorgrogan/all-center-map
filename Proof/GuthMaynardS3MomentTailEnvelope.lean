import GuthMaynardS3ScaledWideMoments

open scoped BigOperators Real
open MeasureTheory
noncomputable section

namespace GuthMaynardS3MomentTailEnvelope

open GuthMaynardJIteration
open GuthMaynardS3LiteralLemma83Energy
open GuthMaynardS3LiteralLemma83Transfer

/-- Fixed Fourier order for the literal Lemma 8.3 tail. -/
def sourceS3MomentTailOrder (eta : ℝ) : ℕ :=
  Nat.ceil (410 / eta) + 2

private theorem rpow_nat_mul {T delta : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    Real.rpow T delta ^ n = Real.rpow T (delta * (n : ℝ)) := by
  exact (Real.rpow_mul_natCast hT delta n).symm

private theorem sourceS3MomentTailOrder_mul {eta : ℝ} (heta : 0 < eta) :
    (410 : ℝ) ≤ eta * (sourceS3MomentTailOrder eta : ℝ) := by
  have hceil : 410 / eta ≤ (Nat.ceil (410 / eta) : ℝ) := Nat.le_ceil _
  have hmul : (410 : ℝ) ≤ eta * (Nat.ceil (410 / eta) : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ heta).mp hceil
  unfold sourceS3MomentTailOrder
  have hcast : ((Nat.ceil (410 / eta) + 2 : ℕ) : ℝ) =
      (Nat.ceil (410 / eta) : ℝ) + 2 := by norm_num
  rw [hcast]
  nlinarith [hmul]

private theorem sourceS3MomentTailOrder_exponent {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) :
    eta * (1 - (sourceS3MomentTailOrder eta : ℝ)) + 4 ≤ (-400 : ℝ) := by
  have hq := sourceS3MomentTailOrder_mul heta
  nlinarith

private theorem sourceBumpFourierConstant_proof_irrel
    {p q : (0 : ℝ) < 1} (n : ℕ) :
    sourceBumpFourierConstant 1 p n = sourceBumpFourierConstant 1 q n := by
  congr

/-- Literal moment-tail envelope after setting `R = 4 T^eta` and fixing the
Fourier order as a function of `eta`. The constant is independent of `T` and
`W`; no decay premise is assumed. -/
theorem lemma83EnergyBound_scaled_uniform
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ Ceta : ℝ, 0 < Ceta ∧
      ∀ (T : ℝ) (W : Finset ℝ) (hT : 1 ≤ T)
          (hcard : (W.card : ℝ) ≤ 2 * T),
          48 * lemma83EnergyBound W (4 * Real.rpow T eta)
              (by
                exact mul_pos (by norm_num)
                  (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT) eta))
              (sourceS3MomentTailOrder eta) ≤
            Ceta * Real.rpow T eta *
                (sourceApproximateAdditiveEnergy W : ℝ) +
              Ceta * Real.rpow T (-400 : ℝ) := by
  have hqexp := sourceS3MomentTailOrder_exponent heta heta1
  let C0 : ℝ := sourceBumpFourierConstant 1 zero_lt_one 0
  let Cq : ℝ := sourceBumpFourierConstant 1 zero_lt_one
      (sourceS3MomentTailOrder eta)
  let K : ℝ := 3072 * Cq * (2 * Real.pi) ^ (sourceS3MomentTailOrder eta)
  let Ceta : ℝ := 1 + 192 * C0 + K
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    exact sourceBumpFourierConstant_nonneg 1 zero_lt_one 0
  have hCq : 0 ≤ Cq := by
    dsimp [Cq]
    exact sourceBumpFourierConstant_nonneg 1 zero_lt_one _
  have hpi : 0 ≤ (2 * Real.pi) ^ (sourceS3MomentTailOrder eta) := by positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hCeta : 0 < Ceta := by
    dsimp [Ceta]
    nlinarith
  refine ⟨Ceta, hCeta, ?_⟩
  intro T W hT hcard
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT0 : 0 ≤ T := hTpos.le
  have hpowpos : 0 < Real.rpow T eta := Real.rpow_pos_of_pos hTpos eta
  have hpow0 : 0 ≤ Real.rpow T eta := hpowpos.le
  let hR : 0 < 4 * Real.rpow T eta :=
    mul_pos (by norm_num) hpowpos
  have hRpos : 0 < 4 * Real.rpow T eta := by positivity
  have hdenpos : 0 < 1 + (4 * Real.rpow T eta) / (2 * Real.pi) := by
    have hpi_pos : 0 < (2 * Real.pi : ℝ) := by positivity
    positivity
  have hden : (4 * Real.rpow T eta) / (2 * Real.pi) ≤
      1 + (4 * Real.rpow T eta) / (2 * Real.pi) := by linarith
  have hdenpow : ((4 * Real.rpow T eta) / (2 * Real.pi)) ^
      (sourceS3MomentTailOrder eta) ≤
      (1 + (4 * Real.rpow T eta) / (2 * Real.pi)) ^
        (sourceS3MomentTailOrder eta) := by
    exact pow_le_pow_left₀ (by positivity) hden _
  have htailden : 1 / (1 + (4 * Real.rpow T eta) / (2 * Real.pi)) ^
      (sourceS3MomentTailOrder eta) ≤
      1 / ((4 * Real.rpow T eta) / (2 * Real.pi)) ^
        (sourceS3MomentTailOrder eta) := by
    exact one_div_le_one_div_of_le (by positivity) hdenpow
  have hcard0 : 0 ≤ (W.card : ℝ) := by positivity
  have hcardpow : (W.card : ℝ) ^ 4 ≤ (2 * T) ^ 4 := by
    exact pow_le_pow_left₀ hcard0 hcard 4
  have htail0 :
      48 * (4 * Real.rpow T eta) * Cq /
          (1 + (4 * Real.rpow T eta) / (2 * Real.pi)) ^
            (sourceS3MomentTailOrder eta) * (W.card : ℝ) ^ 4 ≤
        K * Real.rpow T (-400 : ℝ) := by
    have hleft_nonneg : 0 ≤
        48 * (4 * Real.rpow T eta) * Cq /
          (1 + (4 * Real.rpow T eta) / (2 * Real.pi)) ^
            (sourceS3MomentTailOrder eta) := by positivity
    have hcardpow : (W.card : ℝ) ^ 4 ≤ (2 * T) ^ 4 := by
      exact pow_le_pow_left₀ (by positivity) hcard 4
    have hdenbase : 0 < (4 * Real.rpow T eta) / (2 * Real.pi) := by positivity
    have hden : (4 * Real.rpow T eta) / (2 * Real.pi) ≤
        1 + (4 * Real.rpow T eta) / (2 * Real.pi) := by linarith
    have htail1 :
        48 * (4 * Real.rpow T eta) * Cq /
            (1 + (4 * Real.rpow T eta) / (2 * Real.pi)) ^
              (sourceS3MomentTailOrder eta) * (W.card : ℝ) ^ 4 ≤
          48 * (4 * Real.rpow T eta) * Cq /
            ((4 * Real.rpow T eta) / (2 * Real.pi)) ^
              (sourceS3MomentTailOrder eta) * (2 * T) ^ 4 := by
      calc
        _ ≤ 48 * (4 * Real.rpow T eta) * Cq /
            (1 + (4 * Real.rpow T eta) / (2 * Real.pi)) ^
              (sourceS3MomentTailOrder eta) * (2 * T) ^ 4 :=
          mul_le_mul_of_nonneg_left hcardpow hleft_nonneg
        _ ≤ _ := by
          have hnum : 0 ≤ 48 * (4 * Real.rpow T eta) * Cq := by positivity
          have hdenbasepow : 0 <
              ((4 * Real.rpow T eta) / (2 * Real.pi)) ^
                (sourceS3MomentTailOrder eta) := pow_pos hdenbase _
          have hnum' : 0 ≤
              48 * (4 * Real.rpow T eta) * Cq * (2 * T) ^ 4 := by positivity
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact div_le_div_of_nonneg_left hnum hdenbasepow hdenpow
    have hTpow4 : (2 * T) ^ 4 = 16 * Real.rpow T (4 : ℝ) := by
      rw [mul_pow]
      norm_num
    have htail2 :
        48 * (4 * Real.rpow T eta) * Cq /
            ((4 * Real.rpow T eta) / (2 * Real.pi)) ^
              (sourceS3MomentTailOrder eta) * (2 * T) ^ 4 ≤
          48 * (4 * Real.rpow T eta) * Cq /
            ((4 * Real.rpow T eta) / (2 * Real.pi)) ^
              (sourceS3MomentTailOrder eta) * (16 * Real.rpow T (4 : ℝ)) := by
      simpa [hTpow4] using htail1
    have hpoweta_q : (Real.rpow T eta) ^ (sourceS3MomentTailOrder eta) =
        Real.rpow T (eta * (sourceS3MomentTailOrder eta : ℝ)) :=
      rpow_nat_mul hT0 _
    have hpowcombine :
        Real.rpow T eta * Real.rpow T (4 : ℝ) /
            Real.rpow T (eta * (sourceS3MomentTailOrder eta : ℝ)) ≤
          Real.rpow T (-400 : ℝ) := by
      calc
        _ = Real.rpow T (eta + 4) /
            Real.rpow T (eta * (sourceS3MomentTailOrder eta : ℝ)) := by
          have hradd := Real.rpow_add hTpos eta (4 : ℝ)
          exact (congrArg (fun z : ℝ => z /
            Real.rpow T (eta * (sourceS3MomentTailOrder eta : ℝ))) hradd).symm
        _ ≤ _ := by
          apply (div_le_iff₀ (Real.rpow_pos_of_pos hTpos _)).2
          have hradd := Real.rpow_add hTpos (-400 : ℝ)
            (eta * (sourceS3MomentTailOrder eta : ℝ))
          calc
            _ ≤ Real.rpow T (-400 +
                eta * (sourceS3MomentTailOrder eta : ℝ)) := by
              apply Real.rpow_le_rpow_of_exponent_le hT
              nlinarith [hqexp]
            _ = _ := hradd
    have htail3 :
        48 * (4 * Real.rpow T eta) * Cq /
            ((4 * Real.rpow T eta) / (2 * Real.pi)) ^
              (sourceS3MomentTailOrder eta) * (16 * Real.rpow T (4 : ℝ)) ≤
          K * Real.rpow T (-400 : ℝ) := by
      rw [div_pow]
      calc
        _ = (K * (Real.rpow T eta * Real.rpow T (4 : ℝ) /
            (Real.rpow T eta) ^ (sourceS3MomentTailOrder eta))) /
              (4 : ℝ) ^ (sourceS3MomentTailOrder eta) := by
          dsimp [K]
          rw [mul_pow]
          field_simp [ne_of_gt hpowpos]
          ring
        _ ≤ K * (Real.rpow T eta * Real.rpow T (4 : ℝ) /
            (Real.rpow T eta) ^ (sourceS3MomentTailOrder eta)) := by
          have hA : 0 ≤ K * (Real.rpow T eta * Real.rpow T (4 : ℝ) /
              (Real.rpow T eta) ^ (sourceS3MomentTailOrder eta)) := by
            have hdenq : 0 ≤ (Real.rpow T eta) ^
                (sourceS3MomentTailOrder eta) := by positivity
            exact mul_nonneg hK
              (div_nonneg (mul_nonneg hpow0 (Real.rpow_nonneg hT0 _)) hdenq)
          have hd : 1 ≤ (4 : ℝ) ^ (sourceS3MomentTailOrder eta) :=
            one_le_pow₀ (by norm_num)
          calc
            _ ≤ (K * (Real.rpow T eta * Real.rpow T (4 : ℝ) /
                (Real.rpow T eta) ^ (sourceS3MomentTailOrder eta))) / 1 :=
              div_le_div_of_nonneg_left hA (by norm_num) hd
            _ = _ := by ring
        _ = K * (Real.rpow T eta * Real.rpow T (4 : ℝ) /
            Real.rpow T (eta * (sourceS3MomentTailOrder eta : ℝ))) := by
          rw [hpoweta_q]
        _ ≤ K * Real.rpow T (-400 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hpowcombine hK
    exact htail1.trans (htail2.trans htail3)
  have hmain :
      48 * (4 * Real.rpow T eta) *
          sourceBumpFourierConstant 1 zero_lt_one 0 *
          (sourceApproximateAdditiveEnergy W : ℝ) ≤
        Ceta * Real.rpow T eta *
          (sourceApproximateAdditiveEnergy W : ℝ) := by
    have hE : 0 ≤ (sourceApproximateAdditiveEnergy W : ℝ) := by positivity
    have hcoef : 192 * sourceBumpFourierConstant 1 zero_lt_one 0 ≤ Ceta := by
      dsimp [Ceta, C0]
      nlinarith
    calc
      _ = (192 * sourceBumpFourierConstant 1 zero_lt_one 0) *
          (Real.rpow T eta * (sourceApproximateAdditiveEnergy W : ℝ)) := by ring
      _ ≤ Ceta * (Real.rpow T eta *
          (sourceApproximateAdditiveEnergy W : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hcoef (mul_nonneg hpow0 hE)
      _ = _ := by ring
  have htail :
      48 * (4 * Real.rpow T eta) *
          sourceBumpFourierConstant 1 zero_lt_one
            (sourceS3MomentTailOrder eta) /
          (1 + (4 * Real.rpow T eta) / (2 * Real.pi)) ^
            (sourceS3MomentTailOrder eta) * (W.card : ℝ) ^ 4 ≤
        Ceta * Real.rpow T (-400 : ℝ) := by
    have := htail0
    have hKle : K ≤ Ceta := by
      dsimp [Ceta]
      nlinarith
    have := mul_le_mul_of_nonneg_right hKle
      (Real.rpow_nonneg hT0 (-400 : ℝ))
    exact htail0.trans this
  unfold lemma83EnergyBound
  have hadd := add_le_add hmain htail
  convert hadd using 1 <;> try ring <;> congr

#print axioms GuthMaynardS3MomentTailEnvelope.lemma83EnergyBound_scaled_uniform

end GuthMaynardS3MomentTailEnvelope
