import MAPDynamicHBSourceV3
import MRTLemma215PreliminaryExpansion

/-!
# Dynamic-order preliminary expansion for MRT Lemma 2.15

This is the exact dyadic expansion of every raw branch of the arbitrary-order
HB source.  The final Type-II/Type-`d_j` labels are deliberately absent: they
are assigned only after the scale list of each preliminary component is
sorted and grouped.
-/

namespace MRTLemma215DynamicPreliminaryV3

open scoped BigOperators ArithmeticFunction
open ArithmeticFunction
open MAPHeathBrownFiniteIdentity MAPHBPerronSourceData
open MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215PreliminaryExpansion

noncomputable section

def dynamicComplexHBSignedArithmetic
    (X : ℝ) (K k : ℕ) : ArithmeticFunction ℂ :=
  complexifyArithmetic
    ((((-1 : ArithmeticFunction ℝ) ^ k *
        (K.choose (k + 1) : ArithmeticFunction ℝ)) *
      (ArithmeticFunction.log *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k *
        realTruncatedMoebius (dynamicHBCutoff X K) ^ (k + 1))))

@[simp] theorem dynamicComplexHBSignedArithmetic_apply
    (X : ℝ) (K k n : ℕ) :
    dynamicComplexHBSignedArithmetic X K k n =
      dynamicHBSignedTerm X K k n := rfl

def dynamicComplexHBScalar (K k : ℕ) : ArithmeticFunction ℂ :=
  complexifyArithmetic
    ((-1 : ArithmeticFunction ℝ) ^ k *
      (K.choose (k + 1) : ArithmeticFunction ℝ))

def dynamicComplexTruncatedMoebiusAF
    (X : ℝ) (K : ℕ) : ArithmeticFunction ℂ :=
  complexifyArithmetic (realTruncatedMoebius (dynamicHBCutoff X K))

theorem dynamicComplexHBSignedArithmetic_eq_factorized
    (X : ℝ) (K k : ℕ) :
    dynamicComplexHBSignedArithmetic X K k =
      dynamicComplexHBScalar K k *
        (complexLogAF * complexZetaAF ^ k *
          dynamicComplexTruncatedMoebiusAF X K ^ (k + 1)) := by
  unfold dynamicComplexHBSignedArithmetic dynamicComplexHBScalar
    dynamicComplexTruncatedMoebiusAF complexLogAF complexZetaAF
  simp only [complexifyArithmetic_mul, complexifyArithmetic_pow]

theorem dynamicComplexTruncatedMoebiusAF_eq_truncation
    {X : ℝ} {K : ℕ} (hX : 0 ≤ X) :
    dynamicComplexTruncatedMoebiusAF X K =
      truncatedComplexArithmetic ⌊dynamicHBCutoff X K⌋₊
        (dynamicComplexTruncatedMoebiusAF X K) := by
  have hcut : 0 ≤ dynamicHBCutoff X K :=
    Real.rpow_nonneg (by positivity) _
  ext n
  change dynamicComplexTruncatedMoebiusAF X K n =
    if 1 ≤ n ∧ n ≤ ⌊dynamicHBCutoff X K⌋₊ then
      dynamicComplexTruncatedMoebiusAF X K n else 0
  by_cases hn0 : n = 0
  · subst n
    exact (dynamicComplexTruncatedMoebiusAF X K).map_zero'.trans
      (truncatedComplexArithmetic ⌊dynamicHBCutoff X K⌋₊
        (dynamicComplexTruncatedMoebiusAF X K)).map_zero'.symm
  by_cases hn : n ≤ ⌊dynamicHBCutoff X K⌋₊
  · rw [if_pos ⟨Nat.one_le_iff_ne_zero.mpr hn0, hn⟩]
  · rw [if_neg (fun h => hn h.2)]
    unfold dynamicComplexTruncatedMoebiusAF complexifyArithmetic
    change (((if (n : ℝ) ≤ dynamicHBCutoff X K then
      (ArithmeticFunction.moebius n : ℝ) else 0 : ℝ)) : ℂ) = 0
    rw [if_neg]
    · norm_num
    · exact fun h => hn ((Nat.le_floor_iff hcut).2 h)

def dynamicDyadicHBMoebius (X : ℝ) (K : ℕ) : ArithmeticFunction ℂ :=
  truncatedComplexArithmetic ⌊dynamicHBCutoff X K⌋₊
    (dynamicComplexTruncatedMoebiusAF X K)

def dynamicExpandedHBSignedArithmetic
    (X : ℝ) (K k : ℕ) : ArithmeticFunction ℂ :=
  dynamicComplexHBScalar K k *
    (dyadicHBLog X * dyadicHBZeta X ^ k *
      dynamicDyadicHBMoebius X K ^ (k + 1))

theorem dynamicComplexHBSignedArithmetic_apply_eq_expanded
    {X : ℝ} (hX : 0 ≤ X) (K k : ℕ) {n : ℕ}
    (hn1 : 1 ≤ n) (hnX : n ≤ hbFactorCutoff X) :
    dynamicComplexHBSignedArithmetic X K k n =
      dynamicExpandedHBSignedArithmetic X K k n := by
  rw [dynamicComplexHBSignedArithmetic_eq_factorized]
  unfold dynamicExpandedHBSignedArithmetic dyadicHBLog dyadicHBZeta
    dynamicDyadicHBMoebius
  apply mul_apply_congr_on_divisors
  · intro d hd
    rfl
  · intro d hd
    apply mul_apply_congr_on_divisors
    · intro e he
      apply mul_apply_congr_on_divisors
      · intro a ha
        by_cases ha0 : a = 0
        · subst a
          exact complexLogAF.map_zero'.trans
            (truncatedComplexArithmetic (hbFactorCutoff X)
              complexLogAF).map_zero'.symm
        · exact (truncatedComplexArithmetic_apply_of_mem complexLogAF
            (Nat.one_le_iff_ne_zero.mpr ha0)
            (ha.trans (he.trans (hd.trans hnX)))).symm
      · intro a ha
        apply pow_apply_congr_on_divisors
        intro b hb
        by_cases hb0 : b = 0
        · subst b
          exact complexZetaAF.map_zero'.trans
            (truncatedComplexArithmetic (hbFactorCutoff X)
              complexZetaAF).map_zero'.symm
        · exact (truncatedComplexArithmetic_apply_of_mem complexZetaAF
            (Nat.one_le_iff_ne_zero.mpr hb0)
            (hb.trans (ha.trans (he.trans (hd.trans hnX))))).symm
    · intro a ha
      apply pow_apply_congr_on_divisors
      intro b hb
      rw [← dynamicComplexTruncatedMoebiusAF_eq_truncation hX]

def dynamicHBMoebiusUnit (X : ℝ) (K : ℕ) : ArithmeticFunction ℂ :=
  sourceUnitArithmetic ⌊dynamicHBCutoff X K⌋₊
    (dynamicComplexTruncatedMoebiusAF X K)

def dynamicHBMoebiusShell (X : ℝ) (K : ℕ) :
    Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊) →
      ArithmeticFunction ℂ :=
  sourceDyadicArithmetic ⌊dynamicHBCutoff X K⌋₊
    (dynamicComplexTruncatedMoebiusAF X K)

theorem dynamicHBMoebiusUnit_eq_one
    {X : ℝ} {K : ℕ} (hX : 1 ≤ X) (hK : 1 ≤ K) :
    dynamicHBMoebiusUnit X K = 1 := by
  have hbase : (1 : ℝ) ≤ 2 * X := by linarith
  have hcut : (1 : ℝ) ≤ dynamicHBCutoff X K := by
    unfold dynamicHBCutoff
    exact Real.one_le_rpow hbase (by positivity)
  have hfloor : 1 ≤ ⌊dynamicHBCutoff X K⌋₊ :=
    Nat.le_floor (by exact_mod_cast hcut)
  ext n
  by_cases hn : n = 1
  · subst n
    simp [dynamicHBMoebiusUnit, sourceUnitArithmetic, sourceUnitCoeff,
      hfloor, dynamicComplexTruncatedMoebiusAF, complexifyArithmetic,
      realTruncatedMoebius, hcut]
  · simp [dynamicHBMoebiusUnit, sourceUnitArithmetic, sourceUnitCoeff, hn]

/-- Unit-plus-shell form of one dynamic raw branch. -/
theorem dynamicExpandedHBSignedArithmetic_eq_unit_shell_form
    {X : ℝ} (K k : ℕ) :
    dynamicExpandedHBSignedArithmetic X K k =
      dynamicComplexHBScalar K k *
        ((hbLogUnit X + ∑ j, hbLogShell X j) *
          (hbZetaUnit X + ∑ j, hbZetaShell X j) ^ k *
          (dynamicHBMoebiusUnit X K +
            ∑ j, dynamicHBMoebiusShell X K j) ^ (k + 1)) := by
  unfold dynamicExpandedHBSignedArithmetic dyadicHBLog dyadicHBZeta
    dynamicDyadicHBMoebius hbLogUnit hbLogShell hbZetaUnit hbZetaShell
    dynamicHBMoebiusUnit dynamicHBMoebiusShell
  rw [truncatedComplexArithmetic_eq_unit_add_sum,
    truncatedComplexArithmetic_eq_unit_add_sum,
    truncatedComplexArithmetic_eq_unit_add_sum]

/-- Exact finite multinomial expansion of one dynamic raw HB branch. -/
def dynamicPreliminaryHBShellExpansion
    (X : ℝ) (K k : ℕ) : ArithmeticFunction ℂ :=
  dynamicComplexHBScalar K k *
    ((∑ c : Option (Fin (sourceDyadicCount (hbFactorCutoff X))),
        shellChoice (hbLogUnit X) (hbLogShell X) c) *
      shellPowerExpansion (hbZetaUnit X) (hbZetaShell X) k *
      shellPowerExpansion (dynamicHBMoebiusUnit X K)
        (dynamicHBMoebiusShell X K) (k + 1))

def dynamicPreliminaryHBShellComponentSum
    (X : ℝ) (K k : ℕ) : ArithmeticFunction ℂ :=
  ∑ c : Option (Fin (sourceDyadicCount (hbFactorCutoff X))),
    ∑ zbag ∈ (Finset.univ : Finset
        (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))).sym k,
      ∑ mbag ∈ (Finset.univ : Finset
          (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊)))).sym
            (k + 1),
        dynamicComplexHBScalar K k *
          (shellChoice (hbLogUnit X) (hbLogShell X) c *
            shellPowerTerm (hbZetaUnit X) (hbZetaShell X) k zbag *
            shellPowerTerm (dynamicHBMoebiusUnit X K)
              (dynamicHBMoebiusShell X K) (k + 1) mbag)

theorem dynamicPreliminaryHBShellExpansion_eq_componentSum
    (X : ℝ) (K k : ℕ) :
    dynamicPreliminaryHBShellExpansion X K k =
      dynamicPreliminaryHBShellComponentSum X K k := by
  unfold dynamicPreliminaryHBShellExpansion
    dynamicPreliminaryHBShellComponentSum shellPowerExpansion
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_mul, Finset.mul_sum]

theorem dynamicExpandedHBSignedArithmetic_eq_preliminary
    {X : ℝ} (K k : ℕ) :
    dynamicExpandedHBSignedArithmetic X K k =
      dynamicPreliminaryHBShellExpansion X K k := by
  rw [dynamicExpandedHBSignedArithmetic_eq_unit_shell_form]
  unfold dynamicPreliminaryHBShellExpansion
  rw [sum_shellChoice_eq, add_sum_pow_eq_shellPowerExpansion,
    add_sum_pow_eq_shellPowerExpansion]

def maskedDynamicPreliminaryHBShellComponentSum
    (X : ℝ) (K k n : ℕ) : ℂ :=
  if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then
    dynamicPreliminaryHBShellComponentSum X K k n else 0

/-- Exact raw-branch coefficient identity at arbitrary HB order. -/
theorem dynamicHBBranchCoeff_eq_maskedPreliminaryComponentSum
    {X : ℝ} (hX : 0 ≤ X) {K : ℕ}
    (branch : Fin K) (n : ℕ) :
    dynamicHBBranchCoeff X K branch n =
      maskedDynamicPreliminaryHBShellComponentSum X K branch n := by
  unfold dynamicHBBranchCoeff maskedDynamicPreliminaryHBShellComponentSum
  by_cases hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊
  · rw [if_pos hn, if_pos hn]
    have hnBounds := Finset.mem_Ioc.mp hn
    have hn1 : 1 ≤ n := by omega
    have hnN : n ≤ hbFactorCutoff X := hnBounds.2
    calc
      dynamicHBSignedTerm X K branch n =
          dynamicComplexHBSignedArithmetic X K branch n := by
        rw [dynamicComplexHBSignedArithmetic_apply]
      _ = dynamicExpandedHBSignedArithmetic X K branch n :=
        dynamicComplexHBSignedArithmetic_apply_eq_expanded
          hX K branch hn1 hnN
      _ = dynamicPreliminaryHBShellExpansion X K branch n := by
        rw [dynamicExpandedHBSignedArithmetic_eq_preliminary]
      _ = dynamicPreliminaryHBShellComponentSum X K branch n := by
        rw [dynamicPreliminaryHBShellExpansion_eq_componentSum]
  · rw [if_neg hn, if_neg hn]

end
end MRTLemma215DynamicPreliminaryV3

#print axioms MRTLemma215DynamicPreliminaryV3.dynamicComplexHBSignedArithmetic_apply_eq_expanded
#print axioms MRTLemma215DynamicPreliminaryV3.dynamicPreliminaryHBShellExpansion_eq_componentSum
#print axioms MRTLemma215DynamicPreliminaryV3.dynamicHBBranchCoeff_eq_maskedPreliminaryComponentSum
