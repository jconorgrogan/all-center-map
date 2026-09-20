import MAPFinishDynamicThreeTypeTrace
import Mathlib.Data.Sym.Card
import MRTLemma215DynamicHighPacketCertificateV3

/-! # Explicit logarithmic bounds for dynamic dyadic index counts -/

namespace MRTLemma215DynamicMultiplicityBoundsV3

open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MAPFinishDynamicThreeTypeTrace
open MAPDynamicHBSourceV3
open MRTLemma215DynamicHighPacketCertificateV3

noncomputable section

/-- A source dyadic partition up to a real cutoff has at most three natural
logarithms many cells. -/
theorem sourceDyadicCount_floor_le
    {X : ℝ} (hX : 3 ≤ X) :
    (sourceDyadicCount ⌊X⌋₊ : ℝ) ≤ 3 * Real.log X := by
  let M := ⌊X⌋₊
  have hM2 : 2 ≤ M := by
    dsimp [M]
    apply Nat.le_floor
    norm_num
    linarith
  have hm1 : 0 < M - 1 := by omega
  have hlogb := Real.log2_le_logb (M - 1)
  have hmono : Real.logb 2 (((M - 1 : ℕ) : ℝ)) ≤
      Real.logb 2 (M : ℝ) :=
    (Real.logb_le_logb (b := 2) (by norm_num)
      (by exact_mod_cast hm1)
      (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM2))).2
        (by exact_mod_cast (Nat.sub_le M 1))
  have hnatlog : (((M - 1).log2 : ℕ) : ℝ) ≤
      Real.logb 2 (M : ℝ) := hlogb.trans hmono
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 :=
    Real.log_two_gt_d9.le.trans' (by norm_num)
  have hinvlog2 : (Real.log 2)⁻¹ ≤ 2 := by
    have hi : (Real.log 2)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ :=
      (inv_le_inv₀ (a := Real.log 2) (b := (1 / 2 : ℝ))
        (Real.log_pos (by norm_num)) (by norm_num)).2 hlog2half
    norm_num at hi ⊢
    exact hi
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hM2)
  have hlogM0 : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hlogbBound : Real.logb 2 (M : ℝ) ≤
      2 * Real.log (M : ℝ) := by
    unfold Real.logb
    rw [div_eq_mul_inv]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hinvlog2 hlogM0
  have hMle : (M : ℝ) ≤ X := by
    dsimp [M]
    exact_mod_cast Nat.floor_le (by linarith : 0 ≤ X)
  have hlogMle : Real.log (M : ℝ) ≤ Real.log X :=
    Real.log_le_log hMpos hMle
  have hL1 : 1 ≤ Real.log X :=
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log X := Real.log_le_log (Real.exp_pos 1)
        (Real.exp_one_lt_three.le.trans hX)
  unfold sourceDyadicCount
  push_cast
  dsimp [M] at hnatlog hlogbBound hlogMle ⊢
  nlinarith

/-- The zeta/log shell family used by the dynamic HB decomposition has at
most six logarithms many dyadic cells. -/
theorem sourceDyadicCount_hbFactorCutoff_le
    {X : ℝ} (hX : 3 ≤ X) :
    (sourceDyadicCount (hbFactorCutoff X) : ℝ) ≤
      6 * Real.log X := by
  have h2X : 3 ≤ 2 * X := by linarith
  have hraw := sourceDyadicCount_floor_le h2X
  have hlog2X : Real.log (2 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : X ≠ 0)]
    have hlog2 : Real.log 2 ≤ Real.log X :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith
  simpa [hbFactorCutoff] using hraw.trans (by linarith)

/-- The low zeta-bag enumerator is the whole symmetric power; its exact
cardinality is the standard stars-and-bars coefficient. -/
theorem dynamicLowZBagSet_card_eq
    (X : ℝ) (branch : ℕ) :
    (dynamicLowZBagSetV3 X branch).card =
      (sourceDyadicCount (hbFactorCutoff X) + branch).choose branch := by
  have hall : dynamicLowZBagSetV3 X branch = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro z
    exact Finset.mem_sym_iff.mpr (fun _ _ ↦ Finset.mem_univ _)
  rw [hall, Finset.card_univ, Sym.card_sym_eq_choose]
  simp

/-- A power bound convenient for later logarithmic absorption. -/
theorem dynamicLowZBagSet_card_le_pow
    (X : ℝ) (branch : ℕ) :
    (dynamicLowZBagSetV3 X branch).card ≤
      (sourceDyadicCount (hbFactorCutoff X) + branch) ^ branch := by
  rw [dynamicLowZBagSet_card_eq]
  exact Nat.choose_le_pow _ _

theorem dynamicLowMBagSet_card_eq
    (X : ℝ) (K branch : ℕ) :
    (dynamicLowMBagSetV3 X K branch).card =
      (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊ + branch + 1).choose
        (branch + 1) := by
  have hall : dynamicLowMBagSetV3 X K branch = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro z
    exact Finset.mem_sym_iff.mpr (fun _ _ ↦ Finset.mem_univ _)
  rw [hall, Finset.card_univ, Sym.card_sym_eq_choose]
  simp only [Fintype.card_option, Fintype.card_fin]
  congr 1
  omega

theorem dynamicLowMBagSet_card_le_pow
    (X : ℝ) (K branch : ℕ) :
    (dynamicLowMBagSetV3 X K branch).card ≤
      (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊ + branch + 1) ^
        (branch + 1) := by
  rw [dynamicLowMBagSet_card_eq]
  exact Nat.choose_le_pow _ _

theorem multiset_countPerms_le_factorial
    {α : Type*} [DecidableEq α] (m : Multiset α) :
    m.countPerms ≤ Nat.factorial m.card := by
  unfold Multiset.countPerms Finsupp.multinomial
  rw [Multiset.toFinsupp_sum_eq]
  exact Nat.div_le_self _ _

/-- Uniform finite bound for the exact HB/binomial/multinomial scalar.  It
depends only on the fixed decomposition order and branch number, not on the
dyadic cell choices or on `X`. -/
theorem norm_dynamicComponentScalarValue_le
    {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    ‖dynamicComponentScalarValue zbag mbag‖ ≤
      ((K ^ (k + 1) * Nat.factorial k * Nat.factorial (k + 1) : ℕ) : ℝ) := by
  unfold dynamicComponentScalarValue
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    Complex.norm_natCast]
  norm_cast
  have hz0 := multiset_countPerms_le_factorial
    (↑zbag : Multiset (Option
      (Fin (sourceDyadicCount (hbFactorCutoff X)))))
  have hz : (↑zbag : Multiset (Option
      (Fin (sourceDyadicCount (hbFactorCutoff X))))).countPerms ≤
      Nat.factorial k := by simpa using hz0
  have hm0 := multiset_countPerms_le_factorial
    (↑mbag : Multiset (Option
      (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))))
  have hm : (↑mbag : Multiset (Option
      (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊)))).countPerms ≤
      Nat.factorial (k + 1) := by simpa using hm0
  have hc := Nat.choose_le_pow K (k + 1)
  gcongr
  simpa using hc

end
end MRTLemma215DynamicMultiplicityBoundsV3

#print axioms MRTLemma215DynamicMultiplicityBoundsV3.sourceDyadicCount_floor_le
#print axioms MRTLemma215DynamicMultiplicityBoundsV3.sourceDyadicCount_hbFactorCutoff_le
#print axioms MRTLemma215DynamicMultiplicityBoundsV3.dynamicLowZBagSet_card_eq
#print axioms MRTLemma215DynamicMultiplicityBoundsV3.dynamicLowMBagSet_card_eq
#print axioms MRTLemma215DynamicMultiplicityBoundsV3.norm_dynamicComponentScalarValue_le
