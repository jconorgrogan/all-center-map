import RamachandraLongDyadicScalarSummability

/-!
# Real-scale adapter for the exact long-tail dyadic cutoff

For `X ≥ 3`, the canonical cutoff `K = log₂ floor(X)` kills every earlier
shell.  The first active geometric factor is bounded by `4 X^{-1/4}`, while
`(K+2)^2` costs at most `16 log(X)^2`.  These are the exact scale relations
needed to recover `dT` after the long-contour Minkowski square.
-/

namespace RamachandraLongDyadicCutoff

open Real
open RamachandraLongDyadicScalarSummability

noncomputable section

/-- Canonical first potentially active dyadic cell. -/
def longDyadicCutoff (X : ℝ) : ℕ := (Nat.floor X).log2

private theorem floor_ne_zero_of_three_le {X : ℝ} (hX : 3 ≤ X) :
    Nat.floor X ≠ 0 := by
  have hfloor : 3 ≤ Nat.floor X := Nat.le_floor (by exact_mod_cast hX)
  omega

/-- Every cell strictly before the canonical cutoff has upper endpoint at
most `X`, hence is killed by the literal tail mask. -/
theorem dyadic_upper_le_of_lt_longDyadicCutoff
    {X : ℝ} (hX : 3 ≤ X) {j : ℕ} (hj : j < longDyadicCutoff X) :
    ((2 ^ (j + 1) : ℕ) : ℝ) ≤ X := by
  let M : ℕ := Nat.floor X
  let K : ℕ := M.log2
  have hM : M ≠ 0 := by
    dsimp [M]
    exact floor_ne_zero_of_three_le hX
  have hjK : j + 1 ≤ K := by
    change j < K at hj
    omega
  have hpowM : 2 ^ (j + 1) ≤ M :=
    (Nat.le_log2 hM).mp hjK
  have hfloor : (M : ℝ) ≤ X := by
    dsimp [M]
    exact Nat.floor_le (by linarith)
  exact (by exact_mod_cast hpowM : ((2 ^ (j + 1) : ℕ) : ℝ) ≤ M).trans hfloor

theorem X_lt_four_mul_pow_cutoff
    {X : ℝ} (hX : 3 ≤ X) :
    X < 4 * ((2 ^ longDyadicCutoff X : ℕ) : ℝ) := by
  let M : ℕ := Nat.floor X
  let K : ℕ := M.log2
  have hM : M ≠ 0 := by
    dsimp [M]
    exact floor_ne_zero_of_three_le hX
  have hloglt : M < 2 ^ (K + 1) :=
    (Nat.log2_lt hM).mp (Nat.lt_succ_self K)
  have hXfloor : X < (M : ℝ) + 1 := by
    dsimp [M]
    exact Nat.lt_floor_add_one X
  have hpow1 : (1 : ℝ) ≤ ((2 ^ (K + 1) : ℕ) : ℝ) := by
    exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)))
  have hcastlt : (M : ℝ) < ((2 ^ (K + 1) : ℕ) : ℝ) := by
    exact_mod_cast hloglt
  have hmain : X < 2 * ((2 ^ (K + 1) : ℕ) : ℝ) := by
    nlinarith
  change X < 4 * ((2 ^ K : ℕ) : ℝ)
  have heq : 2 * ((2 ^ (K + 1) : ℕ) : ℝ) =
      4 * ((2 ^ K : ℕ) : ℝ) := by
    norm_num [pow_succ]
    ring
  rwa [heq] at hmain

/-- The first active geometric factor has the sharp `X^{-1/4}` scale, up to
an absolute factor four. -/
theorem cutoff_geometric_le_four_mul_rpow
    {X : ℝ} (hX : 3 ≤ X) :
    (Real.rpow 2 (-(1 / 4 : ℝ))) ^ longDyadicCutoff X ≤
      4 * Real.rpow X (-(1 / 4 : ℝ)) := by
  let K := longDyadicCutoff X
  have hXpos : 0 < X := by linarith
  have hpowpos : 0 < (((2 ^ K : ℕ) : ℝ)) := by positivity
  have hquarter : 0 < X / 4 := div_pos hXpos (by norm_num)
  have hbase : X / 4 < ((2 ^ K : ℕ) : ℝ) := by
    have h := X_lt_four_mul_pow_cutoff hX
    dsimp [K]
    linarith
  have hneg := Real.rpow_lt_rpow_of_neg hquarter hbase
    (by norm_num : (-(1 / 4 : ℝ)) < 0)
  have hdyadic : Real.rpow (((2 ^ K : ℕ) : ℝ)) (-(1 / 4 : ℝ)) =
      (Real.rpow 2 (-(1 / 4 : ℝ))) ^ K := by
    rw [show (((2 ^ K : ℕ) : ℝ)) = (2 : ℝ) ^ K by norm_num]
    exact (Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)
      (-(1 / 4 : ℝ)) K).symm
  have hstep : (Real.rpow 2 (-(1 / 4 : ℝ))) ^ K <
      Real.rpow (X / 4) (-(1 / 4 : ℝ)) := hdyadic.symm.trans_lt hneg
  calc
    (Real.rpow 2 (-(1 / 4 : ℝ))) ^ longDyadicCutoff X =
        (Real.rpow 2 (-(1 / 4 : ℝ))) ^ K := rfl
    _ ≤ Real.rpow (X / 4) (-(1 / 4 : ℝ)) := hstep.le
    _ = Real.rpow X (-(1 / 4 : ℝ)) /
        Real.rpow 4 (-(1 / 4 : ℝ)) := by
      exact Real.div_rpow hXpos.le (by norm_num : (0 : ℝ) ≤ 4) _
    _ = Real.rpow X (-(1 / 4 : ℝ)) * Real.rpow 4 (1 / 4 : ℝ) := by
      have h4neg : Real.rpow 4 (-(1 / 4 : ℝ)) =
          (Real.rpow 4 (1 / 4 : ℝ))⁻¹ := by
        exact Real.rpow_neg (x := (4 : ℝ))
          (by norm_num : (0 : ℝ) ≤ 4) (1 / 4 : ℝ)
      rw [h4neg]
      simp only [div_eq_mul_inv, inv_inv]
    _ ≤ Real.rpow X (-(1 / 4 : ℝ)) * 4 := by
      apply mul_le_mul_of_nonneg_left
      · have h := Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 4)
          (by norm_num : (1 / 4 : ℝ) ≤ 1)
        simpa only [Real.rpow_one] using! h
      · exact Real.rpow_nonneg hXpos.le _
    _ = 4 * Real.rpow X (-(1 / 4 : ℝ)) := by ring

private theorem half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have hepos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  have hesq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]
    norm_num
  have heone : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hehalf : Real.exp (1 / 2 : ℝ) < 2 := by
    nlinarith
  exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)).2 hehalf

/-- The cutoff index costs only two logarithms. -/
theorem cutoff_quadratic_le_sixteen_log_sq
    {X : ℝ} (hX : 3 ≤ X) :
    ((longDyadicCutoff X : ℝ) + 2) ^ 2 ≤ 16 * Real.log X ^ 2 := by
  let M : ℕ := Nat.floor X
  let K : ℕ := M.log2
  have hM : M ≠ 0 := by
    dsimp [M]
    exact floor_ne_zero_of_three_le hX
  have hpowM : 2 ^ K ≤ M := (Nat.le_log2 hM).mp le_rfl
  have hfloor : (M : ℝ) ≤ X := by
    dsimp [M]
    exact Nat.floor_le (by linarith)
  have hpowX : ((2 ^ K : ℕ) : ℝ) ≤ X :=
    (by exact_mod_cast hpowM : ((2 ^ K : ℕ) : ℝ) ≤ M).trans hfloor
  have hXpos : 0 < X := by linarith
  have hpowpos : (0 : ℝ) < ((2 ^ K : ℕ) : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) K)
  have hlogmono : Real.log (((2 ^ K : ℕ) : ℝ)) ≤ Real.log X :=
    Real.strictMonoOn_log.monotoneOn hpowpos hXpos hpowX
  have hlogpow : Real.log (((2 ^ K : ℕ) : ℝ)) =
      (K : ℝ) * Real.log 2 := by
    rw [show (((2 ^ K : ℕ) : ℝ)) = (2 : ℝ) ^ K by norm_num,
      Real.log_pow]
  rw [hlogpow] at hlogmono
  have hKlog : (K : ℝ) / 2 ≤ Real.log X := by
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith [mul_le_mul_of_nonneg_left half_lt_log_two.le hK0]
  have hlogone : 1 ≤ Real.log X := by
    have hlogthree : 1 < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
    have := Real.strictMonoOn_log.monotoneOn (by norm_num : (0 : ℝ) < 3)
      hXpos hX
    linarith
  have hlinear : (K : ℝ) + 2 ≤ 4 * Real.log X := by linarith
  have hnonneg : 0 ≤ (K : ℝ) + 2 := by positivity
  have hsq := pow_le_pow_left₀ hnonneg hlinear 2
  dsimp [K, M, longDyadicCutoff] at hsq ⊢
  nlinarith

/-- Source-scale shifted root-cost bound with `D=2X`.  Unlike the generic
tail estimate, this uses that every active cell already has size comparable
to `X`, so the conductor term introduces no `sqrt X` loss. -/
theorem tsum_longDyadicRootCost_twoX_natAdd_cutoff_le
    {X : ℝ} (hX : 3 ≤ X) :
    (∑' k : ℕ, longDyadicRootCost (2 * X)
        (k + longDyadicCutoff X)) ≤
      Real.sqrt (8 + 8 * Real.pi) *
        ((longDyadicCutoff X : ℝ) + 2) ^ 2 *
        (Real.rpow 2 (-(1 / 4 : ℝ))) ^ longDyadicCutoff X *
        longDyadicTailMass := by
  let K := longDyadicCutoff X
  let r : ℝ := Real.rpow 2 (-(1 / 4 : ℝ))
  let C : ℝ := Real.sqrt (8 + 8 * Real.pi) * ((K : ℝ) + 2) ^ 2 * r ^ K
  have hD : 0 ≤ 2 * X := by positivity
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hroot : Summable (fun k : ℕ => longDyadicRootCost (2 * X) (k + K)) :=
    (summable_nat_add_iff K).2 (summable_longDyadicRootCost hD)
  have htail : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * r ^ k) := by
    simpa only [r] using
      RamachandraLongDyadicScalarSummability.summable_longDyadicTailMajorant
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hmajor : Summable (fun k : ℕ => C * (((k : ℝ) + 1) ^ 2 * r ^ k)) :=
    htail.mul_left C
  have hpoint (k : ℕ) :
      longDyadicRootCost (2 * X) (k + K) ≤
        C * (((k : ℝ) + 1) ^ 2 * r ^ k) := by
    have hpowK : ((2 ^ K : ℕ) : ℝ) ≤ ((2 ^ (k + K) : ℕ) : ℝ) := by
      exact_mod_cast (pow_le_pow_right₀ (by norm_num : 0 < (2 : ℕ))
        (Nat.le_add_left K k))
    have hXpow := (X_lt_four_mul_pow_cutoff hX).le
    have hscale : 2 * X ≤ 8 * ((2 ^ (k + K) : ℕ) : ℝ) := by
      nlinarith
    have hbase := longDyadicRootCost_le_geometric_of_le_mul_pow
      hD (by norm_num : (0 : ℝ) ≤ 8) (k + K) hscale
    have hpoly : (((k + K : ℕ) : ℝ) + 2) ≤
        ((K : ℝ) + 2) * ((k : ℝ) + 1) := by
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      nlinarith [mul_nonneg hk0 hK0]
    have hpoly2 : (((k + K : ℕ) : ℝ) + 2) ^ 2 ≤
        (((K : ℝ) + 2) * ((k : ℝ) + 1)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hpoly 2
    calc
      longDyadicRootCost (2 * X) (k + K) ≤
          Real.sqrt (8 + 8 * Real.pi) *
            (((k + K : ℕ) : ℝ) + 2) ^ 2 * r ^ (k + K) := by
        simpa only [r] using hbase
      _ ≤ Real.sqrt (8 + 8 * Real.pi) *
            (((K : ℝ) + 2) * ((k : ℝ) + 1)) ^ 2 * r ^ (k + K) := by
        gcongr
      _ = C * (((k : ℝ) + 1) ^ 2 * r ^ k) := by
        dsimp [C]
        rw [pow_add]
        ring
  calc
    (∑' k : ℕ, longDyadicRootCost (2 * X) (k + K)) ≤
        ∑' k : ℕ, C * (((k : ℝ) + 1) ^ 2 * r ^ k) :=
      hroot.tsum_le_tsum hpoint hmajor
    _ = C * (∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * r ^ k) := by
      rw [tsum_mul_left]
    _ = Real.sqrt (8 + 8 * Real.pi) * ((K : ℝ) + 2) ^ 2 *
        r ^ K * longDyadicTailMass := by rfl
    _ = _ := by rfl

end
end RamachandraLongDyadicCutoff

#print axioms RamachandraLongDyadicCutoff.cutoff_geometric_le_four_mul_rpow
#print axioms RamachandraLongDyadicCutoff.cutoff_quadratic_le_sixteen_log_sq
