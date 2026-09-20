import ShiuClassIBound

/-!
# Rounded scale inequalities for Shiu Section 5

This extension module isolates the eventual-scale arithmetic needed to apply
Shiu's certified Lemma 2 on every class-I canonical-prefix fiber.  It uses the
literal rounded choice `ceil (Y^(1/30))` from `ShiuClassIBound`.
-/

namespace ShiuClassIBound

open ArithmeticFunction MixedMellinCert ShiuFoundation ShiuSection5Split
  ShiuSection5Structure
open scoped ArithmeticFunction.zeta BigOperators

noncomputable section

/-- A concrete (deliberately non-optimized) endpoint threshold.  Its only role
is to force `4^30 < Y` from `X < Y^3`. -/
def sectionFiveScaleThreshold : ℕ := ((4 : ℕ) ^ 30) ^ 3

/-- Explicit common endpoint for the later logarithm and square-error
absorptions. -/
def sectionFiveFinalAbsorptionThreshold : ℕ := ((9 : ℕ) ^ 30) ^ 3

/-- Above the common endpoint threshold, the legal short-interval condition
forces the base scale needed to absorb the ceiling in `sectionFiveZ`. -/
theorem four_pow_thirty_lt_Y_of_scale
    {X Y : ℕ} (hX : sectionFiveScaleThreshold ≤ X) (hXY : X < Y ^ 3) :
    (4 : ℕ) ^ 30 < Y := by
  by_contra hnot
  have hY : Y ≤ (4 : ℕ) ^ 30 := Nat.le_of_not_gt hnot
  have hcubes : Y ^ 3 ≤ ((4 : ℕ) ^ 30) ^ 3 :=
    Nat.pow_le_pow_left hY 3
  unfold sectionFiveScaleThreshold at hX
  omega

/-- The real thirtieth root is at least four once `Y ≥ 4^30`. -/
lemma four_le_thirtiethRoot {Y : ℕ} (hY : (4 : ℕ) ^ 30 ≤ Y) :
    (4 : ℝ) ≤ (Y : ℝ) ^ (1 / 30 : ℝ) := by
  have hcast : ((4 : ℝ) ^ 30) ≤ (Y : ℝ) := by
    exact_mod_cast hY
  have hr := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ 30)
    hcast (by norm_num : (0 : ℝ) ≤ 1 / 30)
  have hleft : (((4 : ℝ) ^ 30) ^ (1 / 30 : ℝ)) = 4 := by
    convert Real.pow_rpow_inv_natCast (show (0 : ℝ) ≤ 4 by norm_num)
      (by decide : (30 : ℕ) ≠ 0) using 1 <;> norm_num
  calc
    (4 : ℝ) = (((4 : ℝ) ^ 30) ^ (1 / 30 : ℝ)) := hleft.symm
    _ ≤ (Y : ℝ) ^ (1 / 30 : ℝ) := hr

/-- The corresponding lower bound at nine. -/
lemma nine_le_thirtiethRoot {Y : ℕ} (hY : (9 : ℕ) ^ 30 ≤ Y) :
    (9 : ℝ) ≤ (Y : ℝ) ^ (1 / 30 : ℝ) := by
  have hcast : ((9 : ℝ) ^ 30) ≤ (Y : ℝ) := by
    exact_mod_cast hY
  have hr := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (9 : ℝ) ^ 30)
    hcast (by norm_num : (0 : ℝ) ≤ 1 / 30)
  have hleft : (((9 : ℝ) ^ 30) ^ (1 / 30 : ℝ)) = 9 := by
    convert Real.pow_rpow_inv_natCast (show (0 : ℝ) ≤ 9 by norm_num)
      (by decide : (30 : ℕ) ≠ 0) using 1 <;> norm_num
  calc
    (9 : ℝ) = (((9 : ℝ) ^ 30) ^ (1 / 30 : ℝ)) := hleft.symm
    _ ≤ (Y : ℝ) ^ (1 / 30 : ℝ) := hr

/-- The ceiling is dominated by the real sixth root.  The wide exponent gap
`1/30 < 1/6` absorbs the single rounding unit. -/
theorem sectionFiveZ_cast_lt_sixthRoot
    {Y : ℕ} (hY : (4 : ℕ) ^ 30 ≤ Y) :
    (sectionFiveZ Y : ℝ) < (Y : ℝ) ^ (1 / 6 : ℝ) := by
  let u : ℝ := (Y : ℝ) ^ (1 / 30 : ℝ)
  have hYone : (1 : ℝ) ≤ (Y : ℝ) := by
    exact_mod_cast (show 1 ≤ Y from (by omega))
  have hu4 : (4 : ℝ) ≤ u := by
    simpa [u] using four_le_thirtiethRoot hY
  have hceil : (sectionFiveZ Y : ℝ) < u + 1 := by
    simpa [sectionFiveZ, u] using
      (Nat.ceil_lt_add_one
        (Real.rpow_nonneg (Nat.cast_nonneg Y) (1 / 30 : ℝ)))
  have hu_nonneg : 0 ≤ u :=
    Real.rpow_nonneg (Nat.cast_nonneg Y) (1 / 30 : ℝ)
  have huplus : u + 1 ≤ u ^ 5 := by
    have hu2 : u + 1 ≤ u ^ 2 := by nlinarith
    have hu2le : u ^ 2 ≤ u ^ 5 := by
      have hu1 : 1 ≤ u := hu4.trans' (by norm_num)
      exact pow_le_pow_right₀ hu1 (by norm_num)
    exact hu2.trans hu2le
  have hroot : u ^ 5 = (Y : ℝ) ^ (1 / 6 : ℝ) := by
    dsimp [u]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (Nat.cast_nonneg Y)]
    norm_num
  exact hceil.trans_le (huplus.trans_eq hroot)

/-- The rounded parameter has a sixth power strictly below `Y`.  This is the
source-faithful slack that simultaneously handles the sieve-level and quotient
length floors. -/
theorem sectionFiveZ_pow_six_lt
    {Y : ℕ} (hY : (4 : ℕ) ^ 30 ≤ Y) :
    sectionFiveZ Y ^ 6 < Y := by
  have hz := sectionFiveZ_cast_lt_sixthRoot hY
  have hpow := pow_lt_pow_left₀ hz (by positivity : (0 : ℝ) ≤ sectionFiveZ Y)
    (by decide : (6 : ℕ) ≠ 0)
  have hright : (((Y : ℝ) ^ (1 / 6 : ℝ)) ^ 6) = (Y : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (Nat.cast_nonneg Y)]
    norm_num [Real.rpow_one]
  rw [hright] at hpow
  exact_mod_cast hpow

/-- The rounded parameter remains below the interval length. -/
theorem sectionFiveZ_le_Y
    {Y : ℕ} (hY : (4 : ℕ) ^ 30 ≤ Y) :
    sectionFiveZ Y ≤ Y := by
  have hz6 := sectionFiveZ_pow_six_lt hY
  have hzle : sectionFiveZ Y ≤ sectionFiveZ Y ^ 6 :=
    Nat.le_pow (by norm_num : 0 < (6 : ℕ))
  exact hzle.trans hz6.le

/-- The rounded parameter is positive in the eventual Section-5 range. -/
theorem one_le_sectionFiveZ
    {Y : ℕ} (hY : (4 : ℕ) ^ 30 ≤ Y) :
    1 ≤ sectionFiveZ Y := by
  have hu4 := four_le_thirtiethRoot hY
  have hceil := Nat.le_ceil ((Y : ℝ) ^ (1 / 30 : ℝ))
  have hfourR : (4 : ℝ) ≤ (sectionFiveZ Y : ℝ) := hu4.trans hceil
  have hfour : 4 ≤ sectionFiveZ Y := by exact_mod_cast hfourR
  omega

/-- Ceiling also preserves the lower scale used in the class-I suffix bound:
`Y^3 ≤ Z^90`. -/
theorem cube_le_sectionFiveZ_pow_ninety_local (Y : ℕ) :
    Y ^ 3 ≤ sectionFiveZ Y ^ 90 := by
  have hbase : (Y : ℝ) ^ (1 / 30 : ℝ) ≤ (sectionFiveZ Y : ℝ) :=
    Nat.le_ceil _
  have hpow := Real.rpow_le_rpow
    (Real.rpow_nonneg (Nat.cast_nonneg Y) (1 / 30 : ℝ))
    hbase (show (0 : ℝ) ≤ 90 by norm_num)
  have hleft :
      (((Y : ℝ) ^ (1 / 30 : ℝ)) ^ (90 : ℝ)) = (Y : ℝ) ^ 3 := by
    rw [← Real.rpow_mul (Nat.cast_nonneg Y)]
    norm_num [Real.rpow_natCast]
  have hright :
      (((sectionFiveZ Y : ℕ) : ℝ) ^ (90 : ℝ)) =
        ((sectionFiveZ Y ^ 90 : ℕ) : ℝ) := by
    calc
      (((sectionFiveZ Y : ℕ) : ℝ) ^ (90 : ℝ)) =
          (((sectionFiveZ Y : ℕ) : ℝ) ^ (90 : ℕ)) :=
        Real.rpow_natCast _ 90
      _ = ((sectionFiveZ Y ^ 90 : ℕ) : ℝ) := by norm_num
  rw [hleft, hright] at hpow
  exact_mod_cast hpow

/-- Exact short-range bridge for the fixed suffix exponent 179. -/
theorem shortRange_lt_sectionFiveZ_pow_ninety
    {X Y : ℕ} (hXY : X < Y ^ 3) :
    X < sectionFiveZ Y ^ 90 :=
  hXY.trans_le (cube_le_sectionFiveZ_pow_ninety_local Y)

/-- Class-I membership itself excludes the suffix `1`; no artificial
separation condition such as `Z < X-Y` is needed. -/
theorem canonicalD_ne_one_of_mem_classI_from_classifier
    {X Y modulus residue Z cutoff n : ℕ}
    (hZ : 1 ≤ Z)
    (hn : n ∈ classSet FourClass.I X Y modulus residue Z cutoff) :
    canonicalD n Z ≠ 1 := by
  intro hd
  have hclass := (mem_class_I_iff.mp hn).2
  rw [hd] at hclass
  simp [leastPrimeFactor] at hclass
  omega

/-- The certified Selberg lemma's lower sieve-level condition holds. -/
theorem two_le_classISieveLevel_sectionFiveZ
    {Y : ℕ} (hY : (4 : ℕ) ^ 30 ≤ Y) :
    2 ≤ classISieveLevel (sectionFiveZ Y) := by
  rw [classISieveLevel, Nat.le_sqrt]
  have hu4 := four_le_thirtiethRoot hY
  have hceil := Nat.le_ceil ((Y : ℝ) ^ (1 / 30 : ℝ))
  have hfourR : (4 : ℝ) ≤ (sectionFiveZ Y : ℝ) := hu4.trans hceil
  exact_mod_cast hfourR

/-- At the final threshold the sieve denominator logarithm is at least one. -/
theorem one_le_log_classISieveLevel_sectionFiveZ
    {Y : ℕ} (hY : (9 : ℕ) ^ 30 ≤ Y) :
    (1 : ℝ) ≤ Real.log (classISieveLevel (sectionFiveZ Y) : ℝ) := by
  have hroot9 := nine_le_thirtiethRoot hY
  have hceil := Nat.le_ceil ((Y : ℝ) ^ (1 / 30 : ℝ))
  have hz9 : 9 ≤ sectionFiveZ Y := by
    exact_mod_cast hroot9.trans hceil
  have hsqrt3 : 3 ≤ classISieveLevel (sectionFiveZ Y) := by
    rw [classISieveLevel, Nat.le_sqrt]
    norm_num
    exact hz9
  have hsqrtpos : (0 : ℝ) < (classISieveLevel (sectionFiveZ Y) : ℝ) := by
    exact_mod_cast (show 0 < classISieveLevel (sectionFiveZ Y) by omega)
  rw [Real.le_log_iff_exp_le hsqrtpos]
  calc
    Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
    _ ≤ 3 := by norm_num
    _ ≤ (classISieveLevel (sectionFiveZ Y) : ℝ) := by exact_mod_cast hsqrt3

/-- Strong ceiling slack: eight times the cube of every admissible canonical
prefix is still strictly below `Y`. -/
theorem eight_mul_prefix_cube_lt_Y
    {Y Z b : ℕ} (hY : (4 : ℕ) ^ 30 ≤ Y)
    (hZ : Z = sectionFiveZ Y) (hb : b ≤ Z) :
    8 * b ^ 3 < Y := by
  subst Z
  have hz6 := sectionFiveZ_pow_six_lt hY
  have hz4R := four_le_thirtiethRoot hY
  have hceil := Nat.le_ceil ((Y : ℝ) ^ (1 / 30 : ℝ))
  have hz4 : 4 ≤ sectionFiveZ Y := by
    exact_mod_cast hz4R.trans hceil
  have hb3 : b ^ 3 ≤ sectionFiveZ Y ^ 3 := Nat.pow_le_pow_left hb 3
  have h8z : 8 * sectionFiveZ Y ^ 3 ≤ sectionFiveZ Y ^ 6 := by
    have h64 : 64 ≤ sectionFiveZ Y ^ 3 := by
      calc
        64 = 4 ^ 3 := by norm_num
        _ ≤ sectionFiveZ Y ^ 3 := Nat.pow_le_pow_left hz4 3
    have h8 : 8 ≤ sectionFiveZ Y ^ 3 := (by omega)
    calc
      8 * sectionFiveZ Y ^ 3 ≤ sectionFiveZ Y ^ 3 * sectionFiveZ Y ^ 3 := by
        gcongr
      _ = sectionFiveZ Y ^ 6 := by ring
  exact (Nat.mul_le_mul_left 8 hb3).trans_lt (h8z.trans_lt hz6)

/-- The modulus is strictly below the literal rounded quotient length on every
canonical-prefix fiber.  The proof preserves both floors: it first shows
`modulus < Y / b`, hence also `modulus < X / b` and `modulus < Y / b + 1`.
-/
theorem modulus_lt_quotientLength_sectionFiveZ
    {X Y modulus Z b : ℕ}
    (hY : (4 : ℕ) ^ 30 ≤ Y) (hYX : Y ≤ X)
    (hmodulus : 0 < modulus) (hmodcube : modulus ^ 3 < Y ^ 2)
    (hZ : Z = sectionFiveZ Y) (hbpos : 0 < b) (hb : b ≤ Z) :
    modulus < quotientLength X Y b := by
  have h8b : 8 * b ^ 3 < Y := eight_mul_prefix_cube_lt_Y hY hZ hb
  have htwoCube : (2 * modulus * b) ^ 3 < Y ^ 3 := by
    calc
      (2 * modulus * b) ^ 3 = 8 * (modulus ^ 3) * (b ^ 3) := by ring
      _ < 8 * (Y ^ 2) * (b ^ 3) := by
        gcongr
      _ = Y ^ 2 * (8 * b ^ 3) := by ring
      _ < Y ^ 2 * Y := by
        gcongr
      _ = Y ^ 3 := by ring
  have htwomul : 2 * modulus * b < Y :=
    (Nat.pow_lt_pow_iff_left (by decide : (3 : ℕ) ≠ 0)).mp htwoCube
  have hone : (modulus + 1) * b ≤ 2 * modulus * b := by
    nlinarith
  have hsuccMul : (modulus + 1) * b ≤ Y :=
    hone.trans (Nat.le_of_lt htwomul)
  have hsuccDiv : modulus + 1 ≤ Y / b :=
    (Nat.le_div_iff_mul_le hbpos).2 hsuccMul
  have hmodYdiv : modulus < Y / b := by omega
  have hYdivXdiv : Y / b ≤ X / b := Nat.div_le_div_right hYX
  have hmodXdiv : modulus < X / b := hmodYdiv.trans_le hYdivXdiv
  simp only [quotientLength, lt_min_iff]
  exact ⟨hmodYdiv.trans (Nat.lt_succ_self _), hmodXdiv⟩

/-- The Selberg square-error term is absorbed by the interval length. -/
theorem modulus_mul_sectionFiveZ_sq_le_Y
    {Y modulus : ℕ} (hY : (4 : ℕ) ^ 30 ≤ Y)
    (hmodcube : modulus ^ 3 < Y ^ 2) :
    modulus * sectionFiveZ Y ^ 2 ≤ Y := by
  have hz6 := sectionFiveZ_pow_six_lt hY
  have hz6pos : 0 < sectionFiveZ Y ^ 6 := by
    exact pow_pos (show 0 < sectionFiveZ Y by
      have hz1 := one_le_sectionFiveZ hY
      omega) _
  have hcubes : (modulus * sectionFiveZ Y ^ 2) ^ 3 < Y ^ 3 := by
    calc
      (modulus * sectionFiveZ Y ^ 2) ^ 3 =
          modulus ^ 3 * sectionFiveZ Y ^ 6 := by ring
      _ < Y ^ 2 * sectionFiveZ Y ^ 6 :=
        Nat.mul_lt_mul_of_pos_right hmodcube hz6pos
      _ < Y ^ 2 * Y := by
        exact Nat.mul_lt_mul_of_pos_left hz6 (by
          have hYpos : 0 < Y := by omega
          positivity)
      _ = Y ^ 3 := by ring
  exact ((Nat.pow_lt_pow_iff_left (by decide : (3 : ℕ) ≠ 0)).mp hcubes).le

/-- Complete eventual scale package in exactly the legal target variables.
Unlike the false statement `Z < X-Y` (the target permits `Y=X`), this gives
the precise interval-length inequality actually consumed by certified Lemma 2.
-/
theorem sectionFive_classI_scale_package
    {X Y modulus : ℕ}
    (hX : sectionFiveScaleThreshold ≤ X) (hYX : Y ≤ X)
    (hXY : X < Y ^ 3) (hmodulus : 0 < modulus)
    (hmodcube : modulus ^ 3 < Y ^ 2) :
    let Z := sectionFiveZ Y
    1 ≤ Z ∧ X < Z ^ 90 ∧ 2 ≤ classISieveLevel Z ∧
      ∀ b ∈ classIOuterPrefixes Z modulus,
        modulus < quotientLength X Y b := by
  have hYstrict := four_pow_thirty_lt_Y_of_scale hX hXY
  have hYbase : (4 : ℕ) ^ 30 ≤ Y := hYstrict.le
  dsimp only
  refine ⟨one_le_sectionFiveZ hYbase,
    shortRange_lt_sectionFiveZ_pow_ninety hXY,
    two_le_classISieveLevel_sectionFiveZ hYbase, ?_⟩
  intro b hb
  have hbData := Finset.mem_filter.mp hb
  have hbIcc := Finset.mem_Icc.mp hbData.1
  exact modulus_lt_quotientLength_sectionFiveZ hYbase hYX hmodulus
    hmodcube rfl (by omega) hbIcc.2

/-- The three later class-I absorption leaves at one common explicit endpoint
threshold. -/
theorem sectionFive_classI_final_absorption_package
    {X Y modulus : ℕ}
    (hX : sectionFiveFinalAbsorptionThreshold ≤ X)
    (hXY : X < Y ^ 3) (hmodcube : modulus ^ 3 < Y ^ 2) :
    let Z := sectionFiveZ Y
    Z ≤ Y ∧
      (1 : ℝ) ≤ Real.log (classISieveLevel Z : ℝ) ∧
      modulus * Z ^ 2 ≤ Y := by
  have hY9 : (9 : ℕ) ^ 30 < Y := by
    by_contra hnot
    have hYle : Y ≤ (9 : ℕ) ^ 30 := Nat.le_of_not_gt hnot
    have hcubes : Y ^ 3 ≤ ((9 : ℕ) ^ 30) ^ 3 :=
      Nat.pow_le_pow_left hYle 3
    unfold sectionFiveFinalAbsorptionThreshold at hX
    omega
  have h4pow : (4 : ℕ) ^ 30 ≤ (9 : ℕ) ^ 30 :=
    Nat.pow_le_pow_left (by norm_num) 30
  have hY4 : (4 : ℕ) ^ 30 ≤ Y := h4pow.trans hY9.le
  dsimp only
  exact ⟨sectionFiveZ_le_Y hY4,
    one_le_log_classISieveLevel_sectionFiveZ hY9.le,
    modulus_mul_sectionFiveZ_sq_le_Y hY4 hmodcube⟩

end

end ShiuClassIBound
