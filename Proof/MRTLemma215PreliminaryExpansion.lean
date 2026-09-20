import MRTLemma215HBExpansion

/-!
# Flattened finite shell expansion for MRT Lemma 2.15

`Finset.sum_pow` retains the exact multinomial coefficient of every repeated
shell choice.  Thus the preliminary HB expansion below loses neither signs nor
combinatorial multiplicities.  The next source step is the paper's scale-based
grouping of these finite terms into Type II and Type `d_j` families.
-/

namespace MRTLemma215PreliminaryExpansion

open scoped BigOperators ArithmeticFunction
open ArithmeticFunction
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MAPHBPerronSourceData
open MAPMRTCorollary25Instantiation
open MAPHeathBrownFiniteIdentity

noncomputable section

def shellChoice {ι : Type*}
    (unit : ArithmeticFunction ℂ) (shell : ι → ArithmeticFunction ℂ) :
    Option ι → ArithmeticFunction ℂ
  | none => unit
  | some i => shell i

theorem sum_shellChoice_eq
    {ι : Type*} [Fintype ι]
    (unit : ArithmeticFunction ℂ) (shell : ι → ArithmeticFunction ℂ) :
    (∑ c : Option ι, shellChoice unit shell c) = unit + ∑ i : ι, shell i := by
  rw [Fintype.sum_option]
  rfl

def shellPowerTerm {ι : Type*} [DecidableEq ι]
    (unit : ArithmeticFunction ℂ) (shell : ι → ArithmeticFunction ℂ)
    (k : ℕ) (bag : Sym (Option ι) k) : ArithmeticFunction ℂ :=
  ((↑bag : Multiset (Option ι)).countPerms : ArithmeticFunction ℂ) *
    (Multiset.map (shellChoice unit shell) (↑bag : Multiset (Option ι))).prod

def shellPowerExpansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (unit : ArithmeticFunction ℂ) (shell : ι → ArithmeticFunction ℂ)
    (k : ℕ) : ArithmeticFunction ℂ :=
  ∑ bag ∈ (Finset.univ : Finset (Option ι)).sym k,
    shellPowerTerm unit shell k bag

/-- Exact multinomial expansion with the source coefficient retained. -/
theorem add_sum_pow_eq_shellPowerExpansion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (unit : ArithmeticFunction ℂ) (shell : ι → ArithmeticFunction ℂ)
    (k : ℕ) :
    (unit + ∑ i : ι, shell i) ^ k = shellPowerExpansion unit shell k := by
  rw [← sum_shellChoice_eq]
  unfold shellPowerExpansion shellPowerTerm
  exact Finset.sum_pow (shellChoice unit shell) k

def hbLogUnit (X : ℝ) : ArithmeticFunction ℂ :=
  sourceUnitArithmetic (hbFactorCutoff X) complexLogAF

def hbLogShell (X : ℝ) :
    Fin (sourceDyadicCount (hbFactorCutoff X)) → ArithmeticFunction ℂ :=
  sourceDyadicArithmetic (hbFactorCutoff X) complexLogAF

def hbZetaUnit (X : ℝ) : ArithmeticFunction ℂ :=
  sourceUnitArithmetic (hbFactorCutoff X) complexZetaAF

def hbZetaShell (X : ℝ) :
    Fin (sourceDyadicCount (hbFactorCutoff X)) → ArithmeticFunction ℂ :=
  sourceDyadicArithmetic (hbFactorCutoff X) complexZetaAF

def hbMoebiusUnit (X : ℝ) : ArithmeticFunction ℂ :=
  sourceUnitArithmetic ⌊hbCutoff X⌋₊ (complexTruncatedMoebiusAF X)

def hbMoebiusShell (X : ℝ) :
    Fin (sourceDyadicCount ⌊hbCutoff X⌋₊) → ArithmeticFunction ℂ :=
  sourceDyadicArithmetic ⌊hbCutoff X⌋₊ (complexTruncatedMoebiusAF X)

theorem hbLogUnit_eq_zero (X : ℝ) : hbLogUnit X = 0 := by
  ext n
  by_cases hn : n = 1
  · subst n
    simp [hbLogUnit, sourceUnitArithmetic, sourceUnitCoeff,
      complexLogAF, complexifyArithmetic]
  · simp [hbLogUnit, sourceUnitArithmetic, sourceUnitCoeff, hn]

theorem hbZetaUnit_eq_one {X : ℝ} (hX : 1 ≤ X) : hbZetaUnit X = 1 := by
  have hfloor : 1 ≤ hbFactorCutoff X := by
    unfold hbFactorCutoff
    apply Nat.le_floor
    norm_num
    linarith
  ext n
  by_cases hn : n = 1
  · subst n
    simp [hbZetaUnit, sourceUnitArithmetic, sourceUnitCoeff, hfloor,
      complexZetaAF, complexifyArithmetic]
  · simp [hbZetaUnit, sourceUnitArithmetic, sourceUnitCoeff, hn]

theorem hbMoebiusUnit_eq_one {X : ℝ} (hX : 1 ≤ X) :
    hbMoebiusUnit X = 1 := by
  have hbase : (1 : ℝ) ≤ 2 * X := by linarith
  have hcut : (1 : ℝ) ≤ hbCutoff X := by
    unfold hbCutoff
    exact Real.one_le_rpow hbase (by norm_num)
  have hcutCast : ((1 : ℕ) : ℝ) ≤ hbCutoff X := by
    exact_mod_cast hcut
  have hfloor : 1 ≤ ⌊hbCutoff X⌋₊ := Nat.le_floor hcutCast
  ext n
  by_cases hn : n = 1
  · subst n
    simp [hbMoebiusUnit, sourceUnitArithmetic, sourceUnitCoeff, hfloor,
      complexTruncatedMoebiusAF, complexifyArithmetic,
      realTruncatedMoebius, hcut]
  · simp [hbMoebiusUnit, sourceUnitArithmetic, sourceUnitCoeff, hn]

/-- One signed HB term after exact multinomial expansion of the zeta and
Möbius powers.  The remaining product of three finite sums is intentionally
not classified by scale here. -/
def preliminaryHBShellExpansion (X : ℝ) (k : ℕ) : ArithmeticFunction ℂ :=
  complexHBScalar k *
    ((∑ c : Option (Fin (sourceDyadicCount (hbFactorCutoff X))),
        shellChoice (hbLogUnit X) (hbLogShell X) c) *
      shellPowerExpansion (hbZetaUnit X) (hbZetaShell X) k *
      shellPowerExpansion (hbMoebiusUnit X) (hbMoebiusShell X) (k + 1))

/-- The literal finite list of preliminary components before scale grouping. -/
def preliminaryHBShellComponentSum (X : ℝ) (k : ℕ) : ArithmeticFunction ℂ :=
  ∑ c : Option (Fin (sourceDyadicCount (hbFactorCutoff X))),
    ∑ zbag ∈ (Finset.univ : Finset
        (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))).sym k,
      ∑ mbag ∈ (Finset.univ : Finset
          (Option (Fin (sourceDyadicCount ⌊hbCutoff X⌋₊)))).sym (k + 1),
        complexHBScalar k *
          (shellChoice (hbLogUnit X) (hbLogShell X) c *
            shellPowerTerm (hbZetaUnit X) (hbZetaShell X) k zbag *
            shellPowerTerm (hbMoebiusUnit X) (hbMoebiusShell X) (k + 1) mbag)

theorem preliminaryHBShellExpansion_eq_componentSum (X : ℝ) (k : ℕ) :
    preliminaryHBShellExpansion X k = preliminaryHBShellComponentSum X k := by
  unfold preliminaryHBShellExpansion preliminaryHBShellComponentSum
    shellPowerExpansion
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_mul, Finset.mul_sum]

theorem expandedHBSignedArithmetic_eq_preliminaryHBShellExpansion
    {X : ℝ} (hX : 0 ≤ X) (k : ℕ) :
    expandedHBSignedArithmetic X k = preliminaryHBShellExpansion X k := by
  rw [expandedHBSignedArithmetic_eq_unit_shell_form hX]
  unfold preliminaryHBShellExpansion hbLogUnit hbLogShell hbZetaUnit
    hbZetaShell hbMoebiusUnit hbMoebiusShell
  rw [sum_shellChoice_eq,
    add_sum_pow_eq_shellPowerExpansion,
    add_sum_pow_eq_shellPowerExpansion]

def maskedPreliminaryHBShellComponentSum
    (X : ℝ) (k : ℕ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then
    preliminaryHBShellComponentSum X k n else 0

/-- Exact coefficient identity from the raw signed HB branch to the complete
finite preliminary shell list.  This still uses the source's open lower
endpoint; the later Corollary 2.5 closed-endpoint correction belongs to the
`smallTerm` remainder. -/
theorem hbBranchCoeff_eq_maskedPreliminaryComponentSum
    {X : ℝ} (hX : 0 ≤ X) (branch : CutoffBranch) (n : ℕ) :
    hbBranchCoeff X branch n =
      maskedPreliminaryHBShellComponentSum X (cutoffBranchIndex branch) n := by
  unfold hbBranchCoeff maskedHBSignedTerm
    maskedPreliminaryHBShellComponentSum
  by_cases hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊
  · rw [if_pos hn, if_pos hn]
    have hnBounds := Finset.mem_Ioc.mp hn
    have hn1 : 1 ≤ n := by omega
    have hnN : n ≤ hbFactorCutoff X := by
      exact hnBounds.2
    calc
      hbSignedTerm X (cutoffBranchIndex branch) n =
          complexHBSignedArithmetic X (cutoffBranchIndex branch) n := by
        rw [complexHBSignedArithmetic_apply]
      _ = expandedHBSignedArithmetic X (cutoffBranchIndex branch) n :=
        complexHBSignedArithmetic_apply_eq_expanded hX _ hn1 hnN
      _ = preliminaryHBShellExpansion X (cutoffBranchIndex branch) n := by
        rw [expandedHBSignedArithmetic_eq_preliminaryHBShellExpansion hX]
      _ = preliminaryHBShellComponentSum X (cutoffBranchIndex branch) n := by
        rw [preliminaryHBShellExpansion_eq_componentSum]
  · rw [if_neg hn, if_neg hn]

end
end MRTLemma215PreliminaryExpansion

#print axioms MRTLemma215PreliminaryExpansion.add_sum_pow_eq_shellPowerExpansion
#print axioms MRTLemma215PreliminaryExpansion.expandedHBSignedArithmetic_eq_preliminaryHBShellExpansion
#print axioms MRTLemma215PreliminaryExpansion.preliminaryHBShellExpansion_eq_componentSum
#print axioms MRTLemma215PreliminaryExpansion.hbBranchCoeff_eq_maskedPreliminaryComponentSum
