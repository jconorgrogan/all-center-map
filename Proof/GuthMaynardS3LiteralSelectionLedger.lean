import GuthMaynardS3LiteralSelectedAffineUniform106

namespace GuthMaynardS3LiteralSelectionLedger

open scoped BigOperators
open GuthMaynardS3LiteralFullSelection
open GuthMaynardS3LiteralFullSelectionActual
open GuthMaynardS3LiteralSelectedAffineUniform106
open GuthMaynardS3LiteralBalancedSectorGeometry
open GuthMaynardS3LiteralActualSixSectorBound
open GuthMaynardS3LiteralTruncation
open GuthMaynardEquation55Infinite
open GuthMaynardS3LiteralRadialDecay
open GuthMaynardS3LiteralLocalization
open GuthMaynardS3LiteralAffineReduction
open GuthMaynardS3LiteralDyadicBlock
open GuthMaynardS3LiteralUniform106Radial
open GuthMaynardS3LiteralUniform106Fourier
open GuthMaynardSectionThreeCutoffDerivativeBudget

noncomputable section

set_option maxHeartbeats 1000000

/-- The finite ordered key count is logarithmic in the canonical cutoff, with
all constants displayed rather than hidden in an asymptotic symbol. -/
theorem orderedBalancedKeys_card_le_log_sq
    {N : ℕ} (hN : 0 < N)
    {T eta : ℝ} (hT : 1 ≤ T) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hcut : 2 * (N : ℝ) ≤ Real.rpow T (1 + eta)) :
    ((orderedBalancedKeys (s3FrequencyCutoff T eta N)).card : ℝ) ≤
      4 * (2 / Real.log 2 + 1) ^ 2 * (1 + Real.log T) ^ 2 := by
  let M : ℕ := s3FrequencyCutoff T eta N
  have hM : 1 ≤ M := by
    dsimp [M, s3FrequencyCutoff]
    exact le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hMle0 := s3Cutoff_le_rpow hN hT hcut
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hNone : 1 ≤ (N : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hN)
  have hpowT0 : 0 ≤ Real.rpow T (1 + eta) :=
    Real.rpow_nonneg (le_trans (by norm_num) hT) _
  have hMle : (M : ℝ) ≤ Real.rpow T (1 + eta) := by
    dsimp [M] at hMle0 ⊢
    have hdiv : Real.rpow T (1 + eta) / (N : ℝ) ≤
        Real.rpow T (1 + eta) := by
      exact (div_le_iff₀ hNpos).mpr (by nlinarith)
    exact hMle0.trans hdiv
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlogM : Real.log (M : ℝ) ≤ (1 + eta) * Real.log T := by
    have hlog := Real.log_le_log (by positivity : 0 < (M : ℝ)) hMle
    simpa [Real.log_rpow hTpos] using hlog
  have hlogM2 : Real.log (M : ℝ) ≤ 2 * Real.log T := by
    have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT
    nlinarith
  have hpowlog := Nat.pow_log_le_self 2 (Nat.ne_of_gt hMpos)
  have hpowlogR : (2 : ℝ) ^ Nat.log 2 M ≤ (M : ℝ) := by
    exact_mod_cast hpowlog
  have hlogpow := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 M) hpowlogR
  have hlogpow' : (Nat.log 2 M : ℝ) * Real.log 2 ≤ Real.log (M : ℝ) := by
    simpa [Real.log_pow] using hlogpow
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : (Nat.log 2 M : ℝ) ≤ Real.log (M : ℝ) / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    simpa [mul_comm] using hlogpow'
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hL2 : (Nat.log 2 M : ℝ) ≤ 2 * Real.log T / Real.log 2 :=
    hL.trans (div_le_div_of_nonneg_right hlogM2 hlog2.le)
  have hL1 : (Nat.log 2 M : ℝ) + 1 ≤
      (2 / Real.log 2 + 1) * (1 + Real.log T) := by
    have hc : 0 ≤ 2 / Real.log 2 := by positivity
    calc
      (Nat.log 2 M : ℝ) + 1 ≤ 2 * Real.log T / Real.log 2 + 1 := by linarith
      _ = (2 / Real.log 2) * Real.log T + 1 := by ring
      _ ≤ (2 / Real.log 2) * (1 + Real.log T) + 1 := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_right (mul_le_mul_of_nonneg_left
            (by linarith : (Real.log T : ℝ) ≤ 1 + Real.log T) hc) 1)
      _ ≤ (2 / Real.log 2 + 1) * (1 + Real.log T) := by
        nlinarith
  have hsq : ((Nat.log 2 M : ℝ) + 1) ^ 2 ≤
      (2 / Real.log 2 + 1) ^ 2 * (1 + Real.log T) ^ 2 := by
    have hleft : 0 ≤ (Nat.log 2 M : ℝ) + 1 := by positivity
    have hright : 0 ≤ (2 / Real.log 2 + 1) * (1 + Real.log T) := by positivity
    nlinarith
  have hcard : ((orderedBalancedKeys M).card : ℝ) =
      4 * ((Nat.log 2 M : ℝ) + 1) ^ 2 := by
    rw [orderedBalancedKeys_card]
    simp [dyadicExponents, Nat.cast_mul, Nat.cast_add, pow_two, M, hM]
  rw [show s3FrequencyCutoff T eta N = M by rfl]
  rw [hcard]
  nlinarith

theorem selected_radial_error_le_uniform106
    {N : ℕ} (hN : 0 < N)
    {T eta : ℝ} (hT : 1 ≤ T) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hcut : 2 * (N : ℝ) ≤ Real.rpow T (1 + eta))
    (W : Finset ℝ)
    (hNle : (N : ℝ) ≤ T) (hWle : (W.card : ℝ) ≤ 2 * T)
    (i k d : ℕ) :
    let M := s3FrequencyCutoff T eta N
    let q := s3Uniform106DecayOrder eta
    (((prefixFrequencyCube M).card : ℝ) +
        6 * ((orderedBalancedKeys M).card : ℝ) *
        ((orderedBalancedBlock M i k d).card : ℝ)) *
      ((9 / 4 : ℝ) * (N : ℝ) ^ 3 * radialDerivativeBudget q *
        (W.card : ℝ) ^ 3 /
          (s3Rho T eta) ^ q) ≤
      3600 * radialDerivativeBudget q * (8 * Real.rpow T (-100 : ℝ)) := by
  dsimp
  let M : ℕ := s3FrequencyCutoff T eta N
  let q : ℕ := s3Uniform106DecayOrder eta
  have hM : 1 ≤ M := by
    dsimp [M, s3FrequencyCutoff]
    exact le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hN1 : 1 ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hN)
  have hMle := s3Cutoff_le_rpow hN hT hcut
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT0 : 0 ≤ T := hTpos.le
  have hq : 2 ≤ q := by
    dsimp [q, s3Uniform106DecayOrder,
      GuthMaynardS3LiteralErrorContract.s3Uniform106DecayOrder]
    have hc : 0 ≤ Nat.ceil (110 / eta) := Nat.zero_le _
    omega
  have hM5 : (M : ℝ) ^ 5 ≤
      Real.rpow T (5 + 5 * eta) / (N : ℝ) ^ 5 := by
    have hp := pow_le_pow_left₀ hM0 hMle 5
    have hr : Real.rpow T (1 + eta) ^ (5 : ℕ) =
        Real.rpow T (5 + 5 * eta) := by
      calc
        Real.rpow T (1 + eta) ^ (5 : ℕ) =
            Real.rpow (Real.rpow T (1 + eta)) (5 : ℝ) :=
          (Real.rpow_natCast _ 5).symm
        _ = Real.rpow T ((1 + eta) * (5 : ℝ)) :=
          (Real.rpow_mul hT0 (1 + eta) (5 : ℝ)).symm
        _ = Real.rpow T (5 + 5 * eta) := by
          congr 1
          ring
    calc
      (M : ℝ) ^ 5 ≤
          (Real.rpow T (1 + eta) / (N : ℝ)) ^ 5 := hp
      _ = Real.rpow T (1 + eta) ^ 5 / (N : ℝ) ^ 5 := by rw [div_pow]
      _ = Real.rpow T (5 + 5 * eta) / (N : ℝ) ^ 5 := by rw [hr]
  have hW3 : (W.card : ℝ) ^ 3 ≤ (2 * T) ^ 3 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hWle 3
  have hN2 : 1 ≤ (N : ℝ) ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hN1 2
  have hcube : ((prefixFrequencyCube M).card : ℝ) = 8 * (M : ℝ) ^ 3 := by
    rw [prefixFrequencyCube_card]
    norm_num
  have hblockcard : ((orderedBalancedBlock M i k d).card : ℝ) ≤
      ((prefixFrequencyCube M).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (fun p hp => (Finset.mem_filter.mp hp).1)
  have hkeys : ((orderedBalancedKeys M).card : ℝ) ≤ 4 * (M : ℝ) ^ 2 := by
    have hL : Nat.log 2 M + 1 ≤ M := by
      have := Nat.log_lt_self 2 (Nat.ne_of_gt hMpos)
      omega
    have hLr : (Nat.log 2 M : ℝ) + 1 ≤ (M : ℝ) := by
      exact_mod_cast hL
    have hcard : ((orderedBalancedKeys M).card : ℝ) =
        4 * ((Nat.log 2 M : ℝ) + 1) ^ 2 := by
      rw [orderedBalancedKeys_card]
      simp [dyadicExponents, Nat.cast_mul, Nat.cast_add, pow_two,
        max_eq_left hM]
    rw [hcard]
    have hsq : ((Nat.log 2 M : ℝ) + 1) ^ 2 ≤ (M : ℝ) ^ 2 := by
      nlinarith
    nlinarith
  have hMpow : (M : ℝ) ^ 3 ≤ (M : ℝ) ^ 5 := by
    have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    exact pow_le_pow_right₀ hMreal (by norm_num)
  have hcardfactor :
      ((prefixFrequencyCube M).card : ℝ) +
        6 * ((orderedBalancedKeys M).card : ℝ) *
          ((orderedBalancedBlock M i k d).card : ℝ) ≤
        200 * (M : ℝ) ^ 5 := by
    have hkb := mul_le_mul hkeys hblockcard (by positivity) (by positivity)
    rw [hcube]
    calc
      8 * (M : ℝ) ^ 3 +
          6 * ((orderedBalancedKeys M).card : ℝ) *
            ((orderedBalancedBlock M i k d).card : ℝ) ≤
          8 * (M : ℝ) ^ 3 + 6 * ((4 * (M : ℝ) ^ 2) *
            (8 * (M : ℝ) ^ 3)) := by nlinarith
      _ ≤ 200 * (M : ℝ) ^ 5 := by
        nlinarith [hMpow]
  have hqexp : 3 + 5 + 5 * eta - eta * (q : ℝ) ≤ -101 := by
    have hreserve := GuthMaynardS3LiteralErrorContract.uniform106_order_reserve
      (eta := eta) heta
    have hreserve' : 110 + 4 * eta ≤ eta * (q : ℝ) := by
      simpa [q, s3Uniform106DecayOrder,
        GuthMaynardS3LiteralErrorContract.s3Uniform106DecayOrder] using hreserve
    nlinarith
  have hcore :
      (M : ℝ) ^ 5 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 /
          (s3Rho T eta) ^ q ≤
        8 * Real.rpow T (-100 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hM5 (by positivity : 0 ≤ (N : ℝ) ^ 3)
    have hR : 0 ≤ Real.rpow T (5 + 5 * eta) := Real.rpow_nonneg hT0 _
    have hmul' := mul_le_mul hmul hW3 (by positivity)
      (by positivity : 0 ≤ Real.rpow T (5 + 5 * eta) / (N : ℝ) ^ 5 * (N : ℝ) ^ 3)
    have hdivN : Real.rpow T (5 + 5 * eta) / (N : ℝ) ^ 2 ≤
        Real.rpow T (5 + 5 * eta) := by
      have hA : 0 ≤ Real.rpow T (5 + 5 * eta) :=
        Real.rpow_nonneg hT0 _
      exact (div_le_iff₀ (by positivity : 0 < (N : ℝ) ^ 2)).mpr (by
        nlinarith [hA, hN2])
    have hrho : 0 < (s3Rho T eta) ^ q :=
      pow_pos (s3Rho_pos hTpos heta) _
    have hrpow : (s3Rho T eta) ^ q = Real.rpow T (eta * (q : ℝ)) := by
      simpa only [Nat.cast_ofNat] using s3Rho_pow hT0 q
    have htime : Real.rpow T (8 + 5 * eta - eta * (q : ℝ)) ≤
        Real.rpow T (-100 : ℝ) := by
      have he : 8 + 5 * eta - eta * (q : ℝ) ≤ -100 := by
        nlinarith [hqexp]
      exact Real.rpow_le_rpow_of_exponent_le hT he
    have hmain :
        (M : ℝ) ^ 5 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 /
            (s3Rho T eta) ^ q ≤
          8 * Real.rpow T (8 + 5 * eta - eta * (q : ℝ)) := by
      have hN3 : 0 ≤ (N : ℝ) ^ 3 := by positivity
      have hW3' : 0 ≤ (W.card : ℝ) ^ 3 := by positivity
      have hdiv := div_le_div_of_nonneg_right hmul' hrho.le
      calc
        (M : ℝ) ^ 5 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 /
            (s3Rho T eta) ^ q ≤
            (Real.rpow T (5 + 5 * eta) / (N : ℝ) ^ 5) *
              (N : ℝ) ^ 3 * (2 * T) ^ 3 /
                (s3Rho T eta) ^ q := hdiv
        _ ≤ 8 * T ^ 3 * (Real.rpow T (5 + 5 * eta) / (N : ℝ) ^ 2) /
              (s3Rho T eta) ^ q := by
          have heq :
              (Real.rpow T (5 + 5 * eta) / (N : ℝ) ^ 5) *
                  (N : ℝ) ^ 3 * (2 * T) ^ 3 /
                  (s3Rho T eta) ^ q =
                8 * T ^ 3 * (Real.rpow T (5 + 5 * eta) / (N : ℝ) ^ 2) /
                  (s3Rho T eta) ^ q := by
            field_simp [hNpos.ne', hrho.ne']
            ring
          rw [heq]
        _ ≤ 8 * T ^ 3 * Real.rpow T (5 + 5 * eta) /
              (s3Rho T eta) ^ q := by
          have htmp := mul_le_mul_of_nonneg_left hdivN
            (by positivity : (0 : ℝ) ≤ 8 * T ^ 3)
          exact div_le_div_of_nonneg_right htmp
            hrho.le
        _ = 8 * Real.rpow T (8 + 5 * eta - eta * (q : ℝ)) := by
          have hsub : Real.rpow T (8 + 5 * eta) /
                Real.rpow T (eta * (q : ℝ)) =
              Real.rpow T (8 + 5 * eta - eta * (q : ℝ)) := by
            exact (Real.rpow_sub hTpos _ _).symm
          calc
            8 * T ^ 3 * Real.rpow T (5 + 5 * eta) /
                (s3Rho T eta) ^ q =
              8 * (T ^ 3 * Real.rpow T (5 + 5 * eta) /
                Real.rpow T (eta * (q : ℝ))) := by
              rw [hrpow]
              field_simp [Real.rpow_pos_of_pos hTpos _ |>.ne']
            _ = 8 * Real.rpow T (8 + 5 * eta - eta * (q : ℝ)) := by
              rw [show T ^ 3 = Real.rpow T (3 : ℝ) by
                exact (Real.rpow_natCast T 3).symm]
              have hprod : Real.rpow T (3 : ℝ) *
                  Real.rpow T (5 + 5 * eta) =
                  Real.rpow T (8 + 5 * eta) := by
                calc
                  _ = Real.rpow T (3 + (5 + 5 * eta)) :=
                    (Real.rpow_add hTpos _ _).symm
                  _ = _ := by congr 1 <;> ring
              rw [hprod]
              rw [hsub]
    exact hmain.trans (mul_le_mul_of_nonneg_left htime (by positivity))
  have hbudget : 0 ≤ radialDerivativeBudget q := radialDerivativeBudget_nonneg q
  have htail :
      (((prefixFrequencyCube M).card : ℝ) +
          6 * ((orderedBalancedKeys M).card : ℝ) *
            ((orderedBalancedBlock M i k d).card : ℝ)) *
        ((9 / 4 : ℝ) * (N : ℝ) ^ 3 * radialDerivativeBudget q *
          (W.card : ℝ) ^ 3 / (s3Rho T eta) ^ q) ≤
      3600 * radialDerivativeBudget q * (8 * Real.rpow T (-100 : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hcardfactor
      (by
        have hrho : 0 < (s3Rho T eta) ^ q :=
          pow_pos (s3Rho_pos hTpos heta) _
        positivity : 0 ≤ (9 / 4 : ℝ) * (N : ℝ) ^ 3 *
        radialDerivativeBudget q * (W.card : ℝ) ^ 3 /
          (s3Rho T eta) ^ q)
    have hrew :
        200 * (M : ℝ) ^ 5 *
            ((9 / 4 : ℝ) * (N : ℝ) ^ 3 * radialDerivativeBudget q *
              (W.card : ℝ) ^ 3 / (s3Rho T eta) ^ q) =
          450 * radialDerivativeBudget q *
            ((M : ℝ) ^ 5 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 /
              (s3Rho T eta) ^ q) := by ring
    calc
      _ ≤ 200 * (M : ℝ) ^ 5 *
          ((9 / 4 : ℝ) * (N : ℝ) ^ 3 * radialDerivativeBudget q *
            (W.card : ℝ) ^ 3 / (s3Rho T eta) ^ q) := hmul
      _ = 450 * radialDerivativeBudget q *
          ((M : ℝ) ^ 5 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 /
            (s3Rho T eta) ^ q) := hrew
      _ ≤ 450 * radialDerivativeBudget q * (8 * Real.rpow T (-100 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
      _ ≤ _ := by
        have hX : 0 ≤ Real.rpow T (-100 : ℝ) := Real.rpow_nonneg hT0 _
        have hz : 0 ≤ radialDerivativeBudget q *
            (8 * Real.rpow T (-100 : ℝ)) :=
          mul_nonneg hbudget (mul_nonneg (by norm_num) hX)
        nlinarith
  simpa [M, q] using htail

def s3SelectionLedgerConstant (eta : ℝ) : ℝ :=
  max (24 * (2 / Real.log 2 + 1) ^ 2)
    (28800 * radialDerivativeBudget (s3Uniform106DecayOrder eta) +
      8 * (24 * lemma43DerivativeConstant 0 ^ 2 * s3PrefixErrorCoeff eta +
        6 * s3PrefixErrorCoeff eta ^ 3))

theorem s3SelectionLedgerConstant_nonneg (eta : ℝ) :
    0 ≤ s3SelectionLedgerConstant eta := by
  unfold s3SelectionLedgerConstant
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB := radialDerivativeBudget_nonneg (s3Uniform106DecayOrder eta)
  have hK := s3PrefixErrorCoeff_nonneg eta
  positivity

/-- A complete selected-block ledger with the key multiplier and both
negligible errors quantified by one eta-dependent constant.  The logarithm is
shifted by one so the statement remains meaningful at `T = 1`. -/
theorem exists_selected_affine_log_ledger {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {N : ℕ} {T : ℝ} (W : Finset ℝ),
        0 < N → 1 ≤ T →
        2 * (N : ℝ) ≤ Real.rpow T (1 + eta) →
        (∀ a ∈ W, ∀ b ∈ W, |a - b| ≤ T) →
        (N : ℝ) ≤ T → (W.card : ℝ) ≤ 2 * T →
        s3Rho T eta / (N : ℝ) ≤ 1 →
        ∃ i ∈ dyadicExponents (s3FrequencyCutoff T eta N),
          ∃ k ∈ dyadicExponents (s3FrequencyCutoff T eta N),
            ∃ d ∈ Finset.range 4,
              ‖sourceS3 N W‖ ≤
                C * (1 + Real.log T) ^ 2 *
                    orderedBalancedBlockAffine N W (s3Rho T eta)
                      (s3FrequencyCutoff T eta N) i k d +
                  C * Real.rpow T (-100 : ℝ) := by
  refine ⟨s3SelectionLedgerConstant eta,
    s3SelectionLedgerConstant_nonneg eta, ?_⟩
  intro N T W hN hT hcut hdiam hNle hWle hslack
  obtain ⟨i, hi, k, hk, d, hd, hsel⟩ :=
    norm_sourceS3_le_selected_affine_uniform106 hN hT heta hcut W hdiam
      hNle hWle hslack
  have hkey := orderedBalancedKeys_card_le_log_sq hN hT heta heta1 hcut
  have hkey6 := mul_le_mul_of_nonneg_left hkey
    (by norm_num : (0 : ℝ) ≤ 6)
  have haff : 0 ≤ orderedBalancedBlockAffine N W (s3Rho T eta)
      (s3FrequencyCutoff T eta N) i k d := by
    unfold orderedBalancedBlockAffine
    apply mul_nonneg
    · have hB := radialDerivativeBudget_nonneg 0
      have hr := s3Rho_pos (lt_of_lt_of_le zero_lt_one hT) heta
      positivity
    · exact Finset.sum_nonneg fun p _ => affineProfileIntegral_nonneg _ W _ _ _
  have hmain := mul_le_mul_of_nonneg_right hkey6 haff
  have hrad := selected_radial_error_le_uniform106 hN hT heta heta1 hcut W
    hNle hWle i k d
  have hfourcoeff : 0 ≤
      24 * lemma43DerivativeConstant 0 ^ 2 * s3PrefixErrorCoeff eta +
        6 * s3PrefixErrorCoeff eta ^ 3 := by
    have hK := s3PrefixErrorCoeff_nonneg eta
    positivity
  have hRpow : 0 ≤ Real.rpow T (-100 : ℝ) :=
    Real.rpow_nonneg (le_trans (by norm_num) hT) _
  have hE :
      28800 * radialDerivativeBudget (s3Uniform106DecayOrder eta) +
        8 * (24 * lemma43DerivativeConstant 0 ^ 2 * s3PrefixErrorCoeff eta +
          6 * s3PrefixErrorCoeff eta ^ 3) ≤
      s3SelectionLedgerConstant eta := by
    exact le_max_right _ _
  have hErr := mul_le_mul_of_nonneg_right hE hRpow
  have hCkey :
      24 * (2 / Real.log 2 + 1) ^ 2 * (1 + Real.log T) ^ 2 ≤
        s3SelectionLedgerConstant eta * (1 + Real.log T) ^ 2 := by
    have hL : 0 ≤ (1 + Real.log T) ^ 2 := sq_nonneg _
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hL
  have hmainC := mul_le_mul_of_nonneg_right hCkey haff
  refine ⟨i, hi, k, hk, d, hd, ?_⟩
  nlinarith only [hsel, hmain, hmainC, hrad, hErr]

end
end GuthMaynardS3LiteralSelectionLedger

#print axioms GuthMaynardS3LiteralSelectionLedger.orderedBalancedKeys_card_le_log_sq
#print axioms GuthMaynardS3LiteralSelectionLedger.selected_radial_error_le_uniform106
#print axioms GuthMaynardS3LiteralSelectionLedger.exists_selected_affine_log_ledger
