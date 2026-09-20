import RamachandraShiftedDirectFullBudget

/-!
# Canonical truncation parameters for the shifted direct series

The source-scale choice below is `M = ceil(X (log X)^16)` and `Y=2M`.
This file certifies the exact finite-shell legality required by the direct
moment theorem.  Analytic absorption of its explicit cost is kept separate.
-/

namespace RamachandraShiftedDirectParameters

open MRTLemma215DyadicPartition

noncomputable section

/-- Ramachandra direct-series cutoff at scale `X`. -/
def directTruncation (X : ℝ) : ℕ :=
  ⌈X * Real.log X ^ 16⌉₊

/-- Common coefficient-energy ceiling for every dyadic shell. -/
def directEnergyCeiling (X : ℝ) : ℝ :=
  (2 * directTruncation X : ℕ)

theorem one_lt_log_of_three_le {X : ℝ} (hX : 3 ≤ X) :
    (1 : ℝ) < Real.log X := by
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_one_lt_three
  exact hlog3.trans_le (Real.log_le_log (by norm_num) hX)

theorem directTruncation_pos {X : ℝ} (hX : 3 ≤ X) :
    0 < directTruncation X := by
  rw [directTruncation, Nat.ceil_pos]
  have hlog := one_lt_log_of_three_le hX
  positivity

theorem three_le_directTruncation {X : ℝ} (hX : 3 ≤ X) :
    3 ≤ directTruncation X := by
  have hlog := one_lt_log_of_three_le hX
  have hraw : (3 : ℝ) ≤ X * Real.log X ^ 16 := by
    have hp : 1 ≤ Real.log X ^ 16 := one_le_pow₀ hlog.le
    nlinarith
  have hceil := Nat.le_ceil (X * Real.log X ^ 16)
  exact_mod_cast hraw.trans hceil

theorem directTruncation_lower {X : ℝ} :
    X * Real.log X ^ 16 ≤ (directTruncation X : ℝ) := by
  exact Nat.le_ceil _

theorem directTruncation_upper {X : ℝ} (hX : 3 ≤ X) :
    (directTruncation X : ℝ) < X * Real.log X ^ 16 + 1 := by
  exact Nat.ceil_lt_add_one (by
    have hlog := one_lt_log_of_three_le hX
    positivity)

/-- Every standard shell in `[1,M]` lies below `Y=2M`; this discharges the
exact `hNY` hypothesis of the full direct-series budget. -/
theorem sourceShell_le_directEnergyCeiling
    {X : ℝ} (hX : 3 ≤ X)
    (j : Fin (sourceDyadicCount (directTruncation X))) :
    ((2 * 2 ^ (j : ℕ) : ℕ) : ℝ) ≤ directEnergyCeiling X := by
  let M := directTruncation X
  have hM3 : 3 ≤ M := three_le_directTruncation hX
  have hm1 : M - 1 ≠ 0 := by omega
  have hj : (j : ℕ) ≤ (M - 1).log2 := by
    have hjlt := j.isLt
    change (j : ℕ) < sourceDyadicCount M at hjlt
    unfold sourceDyadicCount at hjlt
    omega
  have hpj : 2 ^ (j : ℕ) ≤ 2 ^ (M - 1).log2 :=
    Nat.pow_le_pow_right (by norm_num) hj
  have hpow : 2 ^ (M - 1).log2 ≤ M - 1 := Nat.log2_self_le hm1
  have hnat : 2 * 2 ^ (j : ℕ) ≤ 2 * M := by
    omega
  change ((2 * 2 ^ (j : ℕ) : ℕ) : ℝ) ≤ ((2 * M : ℕ) : ℝ)
  exact_mod_cast hnat

end
end RamachandraShiftedDirectParameters

#print axioms RamachandraShiftedDirectParameters.one_lt_log_of_three_le
#print axioms RamachandraShiftedDirectParameters.sourceShell_le_directEnergyCeiling
