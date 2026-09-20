import GuthMaynardLemma118IntervalPacking
import GuthMaynardEnergyGeometry

open scoped BigOperators Real
open GuthMaynardHeathBrownInterface
open CGLProofDAG

noncomputable section
namespace GuthMaynardEnergy116LogAbsorption

private theorem log_two_mul_le_rpow_local {T eta : ℝ} (hT : 1 ≤ T)
    (heta : 0 < eta) :
    Real.log (2 * T) ≤ (Real.log 2 + 1 / eta) * Real.rpow T eta := by
  have hTp : 0 < T := by linarith
  have hp : 1 ≤ Real.rpow T eta := Real.one_le_rpow hT heta.le
  have hl := Real.log_le_rpow_div hTp.le heta
  change Real.log T ≤ Real.rpow T eta / eta at hl
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hTp.ne']
  have hh := mul_le_mul_of_nonneg_left hp
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  calc
    Real.log 2 + Real.log T ≤
        Real.log 2 * Real.rpow T eta + Real.rpow T eta / eta := by linarith
    _ = (Real.log 2 + 1 / eta) * Real.rpow T eta := by ring

private theorem interval_card_le_two_time
    {T : ℝ} {W : Finset ℝ} (hT : 1 ≤ T)
    (hsep : OneSeparated W)
    (hcontained : ContainedInIntervalOfLength W T) :
    (W.card : ℝ) ≤ 2 * T := by
  obtain ⟨a, ha⟩ := hcontained
  have hpack := GuthMaynardLemma118.card_cast_le_one_add_div
    W a T 1 (by norm_num) (by linarith) ha hsep
  norm_num at hpack
  linarith

/-- A fixed logarithmic multiplicity factor is absorbed into an arbitrary
positive power of the interval length.  The packing estimate is derived
internally from one-separation and interval containment. -/
theorem exists_log_square_absorption :
    ∀ eps : ℝ, 0 < eps →
      ∃ C : ℝ, 0 < C ∧
        ∀ (T : ℝ) (W : Finset ℝ),
          1 ≤ T → OneSeparated W →
          ContainedInIntervalOfLength W T →
          Real.rpow (2 * T + 1) (eps / 2) *
              ((Nat.log2 W.card : ℝ) + 1) ^ 2 ≤
            C * Real.rpow T eps := by
  intro eps heps
  let eta : ℝ := eps / 4
  let A : ℝ := Real.log 2 + 1 / eta
  let D : ℝ := 1 / Real.log 2 + 1
  let B : ℝ := D * (1 + A)
  let C : ℝ := Real.rpow 3 (eps / 2) * B ^ 2
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro T W hT hsep hcontained
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hcard : (W.card : ℝ) ≤ 2 * T :=
    interval_card_le_two_time hT hsep hcontained
  have hbase : Real.rpow (2 * T + 1) (eps / 2) ≤
      Real.rpow (3 * T) (eps / 2) := by
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    linarith
  have hlogbase : 0 ≤ Real.log (2 * T) :=
    Real.log_nonneg (by linarith)
  have hlogBound :
      (Nat.log2 W.card : ℝ) + 1 ≤ B * Real.rpow T eta := by
    by_cases hWne : W.Nonempty
    · have hcardpos : 0 < W.card := Finset.card_pos.mpr hWne
      have hcardrealpos : 0 < (W.card : ℝ) := Nat.cast_pos.mpr hcardpos
      have hlogcard : Real.log (W.card : ℝ) ≤ Real.log (2 * T) := by
        apply Real.log_le_log hcardrealpos
        exact hcard
      have hpowlog := Nat.pow_log_le_self 2 (Nat.ne_of_gt hcardpos)
      have hpowlogR : (2 : ℝ) ^ Nat.log 2 W.card ≤ (W.card : ℝ) := by
        exact_mod_cast hpowlog
      have hlogpow := Real.log_le_log
        (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 W.card) hpowlogR
      have hlogpow' : (Nat.log 2 W.card : ℝ) * Real.log 2 ≤
          Real.log (W.card : ℝ) := by
        simpa [Real.log_pow] using hlogpow
      have hlogpow2' : (Nat.log2 W.card : ℝ) * Real.log 2 ≤
          Real.log (W.card : ℝ) := by
        rw [Nat.log2_eq_log_two]
        exact hlogpow'
      have hlognat : (Nat.log2 W.card : ℝ) ≤
          Real.log (2 * T) / Real.log 2 := by
        apply (le_div_iff₀ hlog2).2
        exact hlogpow2'.trans hlogcard
      have hL0 : (Nat.log2 W.card : ℝ) + 1 ≤
          D * (1 + Real.log (2 * T)) := by
        dsimp [D]
        calc
          (Nat.log2 W.card : ℝ) + 1 ≤
              Real.log (2 * T) / Real.log 2 + 1 := by linarith
          _ = (1 / Real.log 2) * Real.log (2 * T) + 1 := by ring
          _ ≤ (1 / Real.log 2) * (1 + Real.log (2 * T)) + 1 := by
            have hnonneg : 0 ≤ 1 / Real.log 2 := by positivity
            gcongr
            linarith
          _ ≤ (1 / Real.log 2 + 1) * (1 + Real.log (2 * T)) := by
            nlinarith
      have hlogT := log_two_mul_le_rpow_local hT heta
      have hpoweta : 1 ≤ Real.rpow T eta := Real.one_le_rpow hT heta.le
      have hL1 : 1 + Real.log (2 * T) ≤
          (1 + A) * Real.rpow T eta := by
        dsimp [A]
        calc
          1 + Real.log (2 * T) ≤ 1 + A * Real.rpow T eta := by
            gcongr
          _ ≤ Real.rpow T eta + A * Real.rpow T eta := by
            gcongr
          _ = (1 + A) * Real.rpow T eta := by ring
      calc
        (Nat.log2 W.card : ℝ) + 1 ≤
            D * (1 + Real.log (2 * T)) := hL0
        _ ≤ D * ((1 + A) * Real.rpow T eta) :=
          mul_le_mul_of_nonneg_left hL1 hD.le
        _ = B * Real.rpow T eta := by dsimp [B]; ring
    · have hWzero : W.card = 0 := Nat.eq_zero_of_not_pos (by
        intro hpos
        exact hWne (Finset.card_pos.mp hpos))
      have hpoweta : 1 ≤ Real.rpow T eta := Real.one_le_rpow hT heta.le
      have hB1 : 1 ≤ B := by
        dsimp [B, D, A]
        have hD1 : 1 ≤ 1 / Real.log 2 + 1 := by
          have : 0 < 1 / Real.log 2 := by positivity
          linarith
        have hA1 : 1 ≤ 1 + (Real.log 2 + 1 / eta) := by
          have hlog : 0 ≤ Real.log (2 : ℝ) := hlog2.le
          have heta' : 0 ≤ 1 / eta := by positivity
          linarith
        have hmul := mul_le_mul hD1 hA1 (by norm_num) (by positivity)
        simpa using hmul
      simp [hWzero]
      have hBt : 1 ≤ B * Real.rpow T eta := by
        calc
          1 ≤ B := hB1
          _ = B * 1 := by ring
          _ ≤ B * Real.rpow T eta :=
            mul_le_mul_of_nonneg_left hpoweta (by positivity)
      exact hBt
  have hlogsq :
      ((Nat.log2 W.card : ℝ) + 1) ^ 2 ≤
        (B * Real.rpow T eta) ^ 2 := by
    have hleft : 0 ≤ (Nat.log2 W.card : ℝ) + 1 :=
      add_nonneg (Nat.cast_nonneg _) (by norm_num)
    have hright : 0 ≤ B * Real.rpow T eta :=
      mul_nonneg hB.le (Real.rpow_nonneg hTpos.le eta)
    exact (sq_le_sq₀ hleft hright).2 hlogBound
  have hbaseEq : Real.rpow (3 * T) (eps / 2) =
      Real.rpow 3 (eps / 2) * Real.rpow T (eps / 2) := by
    exact Real.mul_rpow (by norm_num) hTpos.le
  have hpowSq : (B * Real.rpow T eta) ^ 2 =
      B ^ 2 * Real.rpow T (eps / 2) := by
    calc
      (B * Real.rpow T eta) ^ 2 = B ^ 2 * (Real.rpow T eta) ^ 2 := by ring
      _ = B ^ 2 * Real.rpow T (2 * eta) := by
        congr 1
        calc
          (Real.rpow T eta) ^ 2 =
              Real.rpow (Real.rpow T eta) (2 : ℝ) :=
            (Real.rpow_natCast _ 2).symm
          _ = Real.rpow T (eta * 2) :=
            (Real.rpow_mul hTpos.le eta 2).symm
          _ = Real.rpow T (2 * eta) := by congr 1 <;> ring
      _ = B ^ 2 * Real.rpow T (eps / 2) := by
        congr 2
        dsimp [eta]
        ring
  calc
    Real.rpow (2 * T + 1) (eps / 2) *
        ((Nat.log2 W.card : ℝ) + 1) ^ 2 ≤
      Real.rpow (3 * T) (eps / 2) *
        (B * Real.rpow T eta) ^ 2 :=
      mul_le_mul hbase hlogsq (sq_nonneg _)
        (Real.rpow_nonneg (by positivity : 0 ≤ 3 * T) _)
    _ = C * Real.rpow T eps := by
      rw [hbaseEq, hpowSq]
      dsimp [C]
      calc
        Real.rpow 3 (eps / 2) * Real.rpow T (eps / 2) *
            (B ^ 2 * Real.rpow T (eps / 2)) =
            Real.rpow 3 (eps / 2) * B ^ 2 *
              (Real.rpow T (eps / 2) * Real.rpow T (eps / 2)) := by ring
        _ = Real.rpow 3 (eps / 2) * B ^ 2 * Real.rpow T eps := by
          have hr : Real.rpow T (eps / 2) * Real.rpow T (eps / 2) =
              Real.rpow T eps := by
            calc
              _ = Real.rpow T ((eps / 2) + (eps / 2)) :=
                (Real.rpow_add hTpos _ _).symm
              _ = Real.rpow T eps := by congr 1; ring
          rw [hr]

end GuthMaynardEnergy116LogAbsorption

#print axioms GuthMaynardEnergy116LogAbsorption.exists_log_square_absorption
