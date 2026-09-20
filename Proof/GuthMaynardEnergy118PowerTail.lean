import GuthMaynardEnergyGeometry
import GuthMaynardLemma118IntervalPacking

open scoped BigOperators Real
open GuthMaynardEnergyGeometry
open GuthMaynardS3LiteralLemma83Energy
open GuthMaynardHeathBrownInterface
open CGLProofDAG

noncomputable section
namespace GuthMaynardEnergy118PowerTail

private theorem power_tail_order_mul {eta : ℝ} (heta : 0 < eta) :
    (2 : ℝ) ≤ eta * (Nat.ceil ((2 : ℝ) / eta) : ℝ) := by
  have hceil : (2 : ℝ) / eta ≤ (Nat.ceil ((2 : ℝ) / eta) : ℝ) :=
    Nat.le_ceil _
  have hmul : (2 : ℝ) ≤ (Nat.ceil ((2 : ℝ) / eta) : ℝ) * eta :=
    (div_le_iff₀ heta).mp hceil
  simpa [mul_comm] using hmul

private theorem power_tail_rpow_lower {eta T : ℝ} (heta : 0 < eta)
    (hT : 1 ≤ T) :
    T ^ (2 : ℕ) ≤ (Real.rpow T eta) ^ Nat.ceil ((2 : ℝ) / eta) := by
  let k : ℕ := Nat.ceil ((2 : ℝ) / eta)
  have hηk : (2 : ℝ) ≤ eta * (k : ℝ) := by
    dsimp [k]
    exact power_tail_order_mul heta
  have hexp : Real.rpow T (2 : ℝ) ≤ Real.rpow T (eta * (k : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hT hηk
  have hpow : Real.rpow T (eta * (k : ℝ)) = (Real.rpow T eta) ^ k := by
    exact Real.rpow_mul_natCast (by positivity : 0 ≤ T) eta k
  calc
    T ^ (2 : ℕ) = Real.rpow T (2 : ℝ) := by
      symm
      exact Real.rpow_natCast T 2
    _ ≤ Real.rpow T (eta * (k : ℝ)) := hexp
    _ = (Real.rpow T eta) ^ k := hpow

/-- The bounded Fourier tail factor is absorbed using only interval packing and
the diagonal lower bound for the literal additive energy.  The order `k` is
chosen from `eta` before `T` and `W` are introduced. -/
theorem exists_bounded_tail_absorption :
    ∀ eta : ℝ, 0 < eta →
      ∃ k : ℕ, ∀ (T : ℝ) (W : Finset ℝ),
        1 ≤ T → OneSeparated W →
        ContainedInIntervalOfLength W T →
        (W.card : ℝ) ^ 3 * (Real.rpow T eta ^ k)⁻¹ ≤
          4 * Real.sqrt (W.card : ℝ) *
            Real.sqrt (sourceApproximateAdditiveEnergy W : ℝ) := by
  intro eta heta
  refine ⟨Nat.ceil ((2 : ℝ) / eta), ?_⟩
  intro T W hT hsep hcontained
  let R : ℝ := (W.card : ℝ)
  let E : ℝ := (sourceApproximateAdditiveEnergy W : ℝ)
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hRnonneg : 0 ≤ R := by positivity
  have hE0 : 0 ≤ E := by positivity
  have hcard : R ≤ 2 * T := by
    obtain ⟨a, ha⟩ := hcontained
    have hpack := GuthMaynardLemma118.card_cast_le_one_add_div
      W a T 1 (by norm_num) (by linarith) ha hsep
    dsimp [R]
    norm_num at hpack
    linarith
  have hpow : T ^ (2 : ℕ) ≤ Real.rpow T eta ^ Nat.ceil ((2 : ℝ) / eta) :=
    power_tail_rpow_lower heta hT
  have hpowpos : 0 < Real.rpow T eta ^ Nat.ceil ((2 : ℝ) / eta) := by
    exact pow_pos (Real.rpow_pos_of_pos hTpos eta) _
  have hT2pos : 0 < T ^ (2 : ℕ) := by positivity
  have hinv :
      (Real.rpow T eta ^ Nat.ceil ((2 : ℝ) / eta))⁻¹ ≤
        (T ^ (2 : ℕ))⁻¹ :=
    (inv_le_inv₀ hpowpos hT2pos).2 hpow
  have htail :
      R ^ 3 * (Real.rpow T eta ^ Nat.ceil ((2 : ℝ) / eta))⁻¹ ≤
        R ^ 3 * (T ^ (2 : ℕ))⁻¹ :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  by_cases hWne : W.Nonempty
  · have hRpos : 0 < R := by
      dsimp [R]
      exact_mod_cast (Finset.card_pos.mpr hWne)
    have hRone : 1 ≤ R := by
      dsimp [R]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hWne))
    have hEdiag : R ^ 2 ≤ E := by
      dsimp [R, E]
      exact sourceApproximateAdditiveEnergy_ge_card_sq W
    have hR2 : R ^ 2 ≤ 4 * T ^ 2 := by
      calc
        R ^ 2 ≤ (2 * T) ^ 2 :=
          (sq_le_sq₀ hRnonneg (by positivity)).2 hcard
        _ = 4 * T ^ 2 := by ring
    have hratio : R ^ 2 / T ^ 2 ≤ 4 := by
      apply (div_le_iff₀ (by positivity : 0 < T ^ 2)).2
      exact hR2
    have hsqrtE : R ≤ Real.sqrt E := by
      apply (Real.le_sqrt hRnonneg hE0).2
      exact hEdiag
    have hsqrtR : 1 ≤ Real.sqrt R :=
      (Real.one_le_sqrt).2 hRone
    have hprod : R ≤ Real.sqrt R * Real.sqrt E := by
      have hmul := mul_le_mul_of_nonneg_right hsqrtR (Real.sqrt_nonneg E)
      have hE_le : Real.sqrt E ≤ Real.sqrt R * Real.sqrt E := by
        simpa using hmul
      exact hsqrtE.trans hE_le
    have hcore : R ^ 3 / T ^ 2 ≤ 4 * Real.sqrt R * Real.sqrt E := by
      calc
        R ^ 3 / T ^ 2 = R * (R ^ 2 / T ^ 2) := by ring
        _ ≤ R * 4 := mul_le_mul_of_nonneg_left hratio hRnonneg
        _ = 4 * R := by ring
        _ ≤ 4 * (Real.sqrt R * Real.sqrt E) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
        _ = 4 * Real.sqrt R * Real.sqrt E := by ring
    calc
      R ^ 3 * (Real.rpow T eta ^ Nat.ceil ((2 : ℝ) / eta))⁻¹ ≤
          R ^ 3 * (T ^ (2 : ℕ))⁻¹ := htail
      _ = R ^ 3 / T ^ 2 := by rw [div_eq_mul_inv]
      _ ≤ 4 * Real.sqrt R * Real.sqrt E := hcore
  · have hWzero : W.card = 0 := Nat.eq_zero_of_not_pos (by
      intro hpos
      exact hWne (Finset.card_pos.mp hpos))
    have hWempty : W = ∅ := Finset.card_eq_zero.mp hWzero
    subst W
    simp [sourceApproximateAdditiveEnergy]

end GuthMaynardEnergy118PowerTail

#print axioms GuthMaynardEnergy118PowerTail.exists_bounded_tail_absorption
