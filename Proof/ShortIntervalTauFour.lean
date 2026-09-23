import ShiuClassIFinal
import ShiuClassIIIII
import ShiuClassIVFinal
import RamanujanWindowAbsorption

/-!
# The one-eighth short-interval fourth-divisor moment

This file reuses the fully certified Section-5 class estimates at an arbitrary
legal scale.  The old public wrapper fixed `Z = ceil (Y^(1/30))`, hence the
unnecessarily restrictive condition `X < Y^3`.  For the major-arc Ramanujan
tail the modulus is one and the divisor order is four.  We may instead take

`Z = ceil (Y^(1/10))`.

Then `X < Y^8` implies `X < Z^90`, while eventually `Z^2 <= Y`; these are the
only changed scale facts needed by the already-certified class-I, class-II/III,
and class-IV analytic estimates.
-/

namespace MAPShortIntervalTauFour

open scoped BigOperators ArithmeticFunction.zeta
open ArithmeticFunction MixedMellinCert ShiuFoundation
open ShiuSection5Split ShiuSection5Structure ShiuClassIBound

noncomputable section

/-- The enlarged Section-5 splitting scale used for intervals above the
one-eighth-power threshold. -/
def shortSectionZ (Y : ℕ) : ℕ :=
  ⌈(Y : ℝ) ^ (1 / 10 : ℝ)⌉₊

/-- A concrete scale at which the tenth root is at least nine. -/
def shortScaleThreshold : ℕ := ((9 : ℕ) ^ 10) ^ 8

theorem nine_pow_ten_lt_Y_of_scale
    {X Y : ℕ} (hX : shortScaleThreshold ≤ X) (hXY : X < Y ^ 8) :
    (9 : ℕ) ^ 10 < Y := by
  by_contra hnot
  have hY : Y ≤ (9 : ℕ) ^ 10 := Nat.le_of_not_gt hnot
  have hpows : Y ^ 8 ≤ ((9 : ℕ) ^ 10) ^ 8 := Nat.pow_le_pow_left hY 8
  unfold shortScaleThreshold at hX
  omega

theorem nine_le_tenthRoot {Y : ℕ} (hY : (9 : ℕ) ^ 10 ≤ Y) :
    (9 : ℝ) ≤ (Y : ℝ) ^ (1 / 10 : ℝ) := by
  have hcast : ((9 : ℝ) ^ 10) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hr := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (9 : ℝ) ^ 10)
    hcast (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hleft : (((9 : ℝ) ^ 10) ^ (1 / 10 : ℝ)) = 9 := by
    convert Real.pow_rpow_inv_natCast (show (0 : ℝ) ≤ 9 by norm_num)
      (by decide : (10 : ℕ) ≠ 0) using 1 <;> norm_num
  exact hleft ▸ hr

/-- The rounded tenth root is below the real fifth root. -/
theorem shortSectionZ_cast_lt_fifthRoot
    {Y : ℕ} (hY : (9 : ℕ) ^ 10 ≤ Y) :
    (shortSectionZ Y : ℝ) < (Y : ℝ) ^ (1 / 5 : ℝ) := by
  let u : ℝ := (Y : ℝ) ^ (1 / 10 : ℝ)
  have hu9 : (9 : ℝ) ≤ u := by simpa [u] using nine_le_tenthRoot hY
  have hceil : (shortSectionZ Y : ℝ) < u + 1 := by
    simpa [shortSectionZ, u] using
      (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg Y) (1 / 10 : ℝ)))
  have hu0 : 0 ≤ u := Real.rpow_nonneg (Nat.cast_nonneg Y) (1 / 10 : ℝ)
  have huplus : u + 1 ≤ u ^ 2 := by nlinarith
  have hroot : u ^ 2 = (Y : ℝ) ^ (1 / 5 : ℝ) := by
    dsimp [u]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (Nat.cast_nonneg Y)]
    norm_num
  exact hceil.trans_le (huplus.trans_eq hroot)

theorem one_le_shortSectionZ
    {Y : ℕ} (hY : (9 : ℕ) ^ 10 ≤ Y) :
    1 ≤ shortSectionZ Y := by
  have hroot := nine_le_tenthRoot hY
  have hceil := Nat.le_ceil ((Y : ℝ) ^ (1 / 10 : ℝ))
  have : (9 : ℝ) ≤ (shortSectionZ Y : ℝ) := hroot.trans hceil
  exact_mod_cast (show (1 : ℕ) ≤ 9 from by norm_num).trans (by exact_mod_cast this)

theorem nine_le_shortSectionZ
    {Y : ℕ} (hY : (9 : ℕ) ^ 10 ≤ Y) :
    9 ≤ shortSectionZ Y := by
  have hroot := nine_le_tenthRoot hY
  have hceil := Nat.le_ceil ((Y : ℝ) ^ (1 / 10 : ℝ))
  exact_mod_cast hroot.trans hceil

/-- The enlarged scale still has a square error smaller than the interval
length. -/
theorem shortSectionZ_sq_lt_Y
    {Y : ℕ} (hY : (9 : ℕ) ^ 10 ≤ Y) :
    shortSectionZ Y ^ 2 < Y := by
  have hz := shortSectionZ_cast_lt_fifthRoot hY
  have hz0 : (0 : ℝ) ≤ shortSectionZ Y := by positivity
  have hpow := pow_lt_pow_left₀ hz hz0 (by decide : (5 : ℕ) ≠ 0)
  have hright : (((Y : ℝ) ^ (1 / 5 : ℝ)) ^ 5) = (Y : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (Nat.cast_nonneg Y)]
    norm_num [Real.rpow_one]
  rw [hright] at hpow
  have hz1 : 1 ≤ shortSectionZ Y := one_le_shortSectionZ hY
  have htwofive : shortSectionZ Y ^ 2 ≤ shortSectionZ Y ^ 5 :=
    Nat.pow_le_pow_right hz1 (by norm_num)
  have hpowNat : shortSectionZ Y ^ 5 < Y := by exact_mod_cast hpow
  exact htwofive.trans_lt hpowNat

theorem shortSectionZ_le_Y
    {Y : ℕ} (hY : (9 : ℕ) ^ 10 ≤ Y) :
    shortSectionZ Y ≤ Y := by
  have hz1 := one_le_shortSectionZ hY
  exact (show shortSectionZ Y ≤ shortSectionZ Y ^ 2 from
    Nat.le_pow (by norm_num)).trans (shortSectionZ_sq_lt_Y hY).le

/-- The lower scale needed by all existing arbitrary-`Z` class estimates. -/
theorem X_lt_shortSectionZ_pow_ninety
    {X Y : ℕ} (hXY : X < Y ^ 8) :
    X < shortSectionZ Y ^ 90 := by
  have hbase : (Y : ℝ) ^ (1 / 10 : ℝ) ≤ (shortSectionZ Y : ℝ) := Nat.le_ceil _
  have hpow := Real.rpow_le_rpow
    (Real.rpow_nonneg (Nat.cast_nonneg Y) (1 / 10 : ℝ)) hbase
    (show (0 : ℝ) ≤ 80 by norm_num)
  have hleft : (((Y : ℝ) ^ (1 / 10 : ℝ)) ^ (80 : ℝ)) = (Y : ℝ) ^ 8 := by
    rw [← Real.rpow_mul (Nat.cast_nonneg Y)]
    norm_num [Real.rpow_natCast]
  have hright : (((shortSectionZ Y : ℕ) : ℝ) ^ (80 : ℝ)) =
      ((shortSectionZ Y ^ 80 : ℕ) : ℝ) := by
    calc
      (((shortSectionZ Y : ℕ) : ℝ) ^ (80 : ℝ)) =
          (((shortSectionZ Y : ℕ) : ℝ) ^ (80 : ℕ)) :=
        Real.rpow_natCast _ 80
      _ = ((shortSectionZ Y ^ 80 : ℕ) : ℝ) := by norm_num
  rw [hleft, hright] at hpow
  have hyNat : Y ^ 8 ≤ shortSectionZ Y ^ 80 := by exact_mod_cast hpow
  have hz1 : 1 ≤ shortSectionZ Y := by
    have hYpos : 0 < Y := by
      by_contra hnot
      have : Y = 0 := Nat.eq_zero_of_not_pos hnot
      simp [this] at hXY
    apply Nat.ceil_pos.mpr
    exact Real.rpow_pos_of_pos (by exact_mod_cast hYpos) _
  have hpows : shortSectionZ Y ^ 80 ≤ shortSectionZ Y ^ 90 :=
    Nat.pow_le_pow_right hz1 (by norm_num)
  exact hXY.trans_le (hyNat.trans hpows)

/-- At modulus one, every prefix up to `Z` has a quotient interval of length
strictly larger than the modulus. -/
theorem one_lt_quotientLength_of_prefix
    {X Y Z b : ℕ} (hYX : Y ≤ X) (hZ9 : 9 ≤ Z)
    (hZsq : Z ^ 2 ≤ Y) (hb : b ∈ classIOuterPrefixes Z 1) :
    1 < quotientLength X Y b := by
  have hbIcc : b ∈ Finset.Icc 1 Z := by
    exact (Finset.mem_filter.mp hb).1
  have hbBounds := Finset.mem_Icc.mp hbIcc
  have hbpos : 0 < b := by omega
  have htwoZ : 2 * Z ≤ Z ^ 2 := by nlinarith
  have htwoB : 2 * b ≤ Y :=
    (Nat.mul_le_mul_left 2 hbBounds.2).trans (htwoZ.trans hZsq)
  have hYdiv : 2 ≤ Y / b := (Nat.le_div_iff_mul_le hbpos).2 (by simpa using htwoB)
  have hXdiv : 2 ≤ X / b := hYdiv.trans (Nat.div_le_div_right hYX)
  simp only [quotientLength, lt_min_iff]
  omega

theorem one_le_log_classISieveLevel_shortSectionZ
    {Y : ℕ} (hY : (9 : ℕ) ^ 10 ≤ Y) :
    (1 : ℝ) ≤ Real.log (classISieveLevel (shortSectionZ Y) : ℝ) := by
  have hz9 := nine_le_shortSectionZ hY
  have hsqrt3 : 3 ≤ classISieveLevel (shortSectionZ Y) := by
    rw [classISieveLevel, Nat.le_sqrt]
    norm_num
    exact hz9
  have hsqrtpos : (0 : ℝ) < (classISieveLevel (shortSectionZ Y) : ℝ) := by
    exact_mod_cast (show 0 < classISieveLevel (shortSectionZ Y) by omega)
  rw [Real.le_log_iff_exp_le hsqrtpos]
  calc
    Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
    _ ≤ 3 := by norm_num
    _ ≤ (classISieveLevel (shortSectionZ Y) : ℝ) := by exact_mod_cast hsqrt3

/-- The arbitrary-scale certified Section-5 machinery closes the order-four
moment in all intervals satisfying `X < Y^8`. -/
theorem certified_tauFourSquare_shortInterval :
    ∃ C : ℝ, 0 < C ∧
      ∃ X₀ : ℕ, 3 ≤ X₀ ∧
        ∀ X Y : ℕ,
          X₀ ≤ X → Y ≤ X → X < Y ^ 8 →
          (progressionSum ((tauAF 4).pmul (tauAF 4)) X Y 1 0 : ℝ) ≤
            C * (Y : ℝ) * (Real.log (X : ℝ)) ^ 16 := by
  obtain ⟨Cweight, Ctail, hCweight, hCtail, Z₀, hZ₀, hIIraw⟩ :=
    ShiuClassIIIII.exists_classIIIII56_raw 4 (by norm_num)
  let KI : ℝ :=
    3 * (((4 * 4) ^ 179 : ℕ) : ℝ) * classISelbergConstant *
      Real.exp (((4 * 4 : ℕ) : ℝ) * (5 + 2 * Real.log 4))
  let KII : ℝ := Cweight * (4 + 2 * Ctail)
  let KIV : ℝ :=
    (5 * classISelbergConstant *
      ShiuFiniteEulerDistortion.explicitEulerDistortionConstant 4 *
      Real.exp (((4 * 4 : ℕ) : ℝ) * (5 + 2 * Real.log 4))) *
      (∑' r : ℕ, ShiuClassIVBound.classIVSeriesTerm
        (ShiuClassIVBound.classIVSuffixBase 4 : ℝ) r)
  let C : ℝ := KI + KII + KIV
  let X₀ : ℕ := max sectionFiveFinalAbsorptionThreshold
    (max shortScaleThreshold ((Z₀ ^ 10) ^ 8))
  have hKI : 0 < KI := by
    dsimp [KI]
    have hnum : 0 < (3 : ℝ) * (((4 * 4) ^ 179 : ℕ) : ℝ) := by positivity
    exact mul_pos (mul_pos hnum classISelbergConstant_pos) (Real.exp_pos _)
  have hKII : 0 < KII := by dsimp [KII]; positivity
  have hApos : 0 < (ShiuClassIVBound.classIVSuffixBase 4 : ℝ) := by
    dsimp [ShiuClassIVBound.classIVSuffixBase]
    positivity
  have hseries0 : 0 ≤ ∑' r : ℕ, ShiuClassIVBound.classIVSeriesTerm
      (ShiuClassIVBound.classIVSuffixBase 4 : ℝ) r :=
    tsum_nonneg (fun r => ShiuClassIVBound.classIVSeriesTerm_nonneg hApos.le r)
  have hKIV : 0 ≤ KIV := by
    dsimp [KIV]
    have hcoef : 0 ≤
        5 * classISelbergConstant *
          ShiuFiniteEulerDistortion.explicitEulerDistortionConstant 4 *
          Real.exp (((4 * 4 : ℕ) : ℝ) * (5 + 2 * Real.log 4)) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) classISelbergConstant_pos.le)
          (ShiuFiniteEulerDistortion.explicitEulerDistortionConstant_pos 4).le)
        (Real.exp_pos _).le
    exact mul_nonneg hcoef hseries0
  have hC : 0 < C := by dsimp [C]; linarith
  have hX₀ : 3 ≤ X₀ := by
    exact (show 3 ≤ sectionFiveFinalAbsorptionThreshold by
      norm_num [sectionFiveFinalAbsorptionThreshold]).trans
        (le_max_left _ _)
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro X Y hX hYX hXY
  let Z := shortSectionZ Y
  let cutoff := ShiuEndToEnd.smoothCutoff X
  have hShortScale : shortScaleThreshold ≤ X :=
    (le_max_of_le_right (le_max_left _ _)).trans hX
  have hY9strict : (9 : ℕ) ^ 10 < Y :=
    nine_pow_ten_lt_Y_of_scale hShortScale hXY
  have hY9 : (9 : ℕ) ^ 10 ≤ Y := hY9strict.le
  have hZ9 : 9 ≤ Z := by simpa [Z] using nine_le_shortSectionZ hY9
  have hZ3 : 3 ≤ Z := by omega
  have hZ1 : 1 ≤ Z := by omega
  have hZsq : Z ^ 2 ≤ Y := by
    exact (by simpa [Z] using (shortSectionZ_sq_lt_Y hY9).le)
  have hZY : Z ≤ Y := by simpa [Z] using shortSectionZ_le_Y hY9
  have hZX : Z ≤ X := hZY.trans hYX
  have hXZ : X < Z ^ 90 := by simpa [Z] using X_lt_shortSectionZ_pow_ninety hXY
  have hXfinal : sectionFiveFinalAbsorptionThreshold ≤ X :=
    (le_max_left _ _).trans hX
  have hX3 : 3 ≤ X := hX₀.trans hX
  have hZ₀pow : (Z₀ ^ 10) ^ 8 ≤ X :=
    (le_max_of_le_right (le_max_right _ _)).trans hX
  have hZ₀powY : (Z₀ ^ 10) ^ 8 < Y ^ 8 := hZ₀pow.trans_lt hXY
  have hZ₀tenY : Z₀ ^ 10 < Y :=
    (Nat.pow_lt_pow_iff_left (by decide : (8 : ℕ) ≠ 0)).mp hZ₀powY
  have hZ₀root : (Z₀ : ℝ) ≤ (Y : ℝ) ^ (1 / 10 : ℝ) := by
    rw [show (1 / 10 : ℝ) = (10 : ℝ)⁻¹ by norm_num]
    apply (Real.le_rpow_inv_iff_of_pos
      (show (0 : ℝ) ≤ Z₀ by positivity)
      (show (0 : ℝ) ≤ Y by positivity)
      (show (0 : ℝ) < 10 by norm_num)).2
    exact_mod_cast hZ₀tenY.le
  have hZ₀Z : Z₀ ≤ Z := by
    have hceil := Nat.le_ceil ((Y : ℝ) ^ (1 / 10 : ℝ))
    exact_mod_cast hZ₀root.trans hceil
  have hsieve : 2 ≤ classISieveLevel Z := by
    rw [classISieveLevel, Nat.le_sqrt]
    norm_num
    omega
  have hlog : (1 : ℝ) ≤ Real.log (classISieveLevel Z : ℝ) := by
    simpa [Z] using one_le_log_classISieveLevel_shortSectionZ hY9
  have hmodLength : ∀ b ∈ classIOuterPrefixes Z 1,
      1 < quotientLength X Y b := by
    intro b hb
    exact one_lt_quotientLength_of_prefix hYX hZ9 hZsq hb
  have hlogcutoff : Real.log (Z : ℝ) <
      (cutoff : ℝ) * Real.log (cutoff : ℝ) := by
    simpa [cutoff] using
      ShiuClassIVBound.smoothCutoff_log_dominates hXfinal hZ1 hZX
  have hcutoff2 : 2 ≤ cutoff := by
    by_contra hnot
    have hcutle : cutoff ≤ 1 := by omega
    have hnonpos : Real.log (cutoff : ℝ) ≤ 0 :=
      Real.log_nonpos (by positivity) (by exact_mod_cast hcutle)
    have hprod : (cutoff : ℝ) * Real.log (cutoff : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hnonpos
    have hlogZpos : 0 < Real.log (Z : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
    linarith
  have hI := modulus_mul_classIMass_cast_le_logPow
    4 X Y 1 0 Z cutoff (by norm_num) hZ1 hYX hXZ hZY hZX
      (by norm_num) (by norm_num) (by norm_num) hsieve hmodLength hlog
      (by simpa using hZsq) hX3 (by omega)
  have hII0 := hIIraw X Y 1 0 Z hZ₀Z hZX hXZ (by norm_num)
    (by norm_num) hYX
  have hIIabs := ShiuClassIIIII.classIIIII_raw_expression_absorption
    (z := (Z : ℝ)) (q := (1 : ℝ)) (y := (Y : ℝ))
    (Cweight := Cweight) (Ctail := Ctail)
    (by exact_mod_cast hZ1) (by norm_num) (by positivity)
    hCweight.le hCtail.le (by norm_num; exact_mod_cast hZsq)
  have hII :
      ShiuClassIIIII.exceptionalMass 4 X Y 1 0 Z
          (ShiuLemma1ClassIII.classIIICutoff X) ≤ KII * (Y : ℝ) := by
    calc
      _ ≤ Cweight * (Z : ℝ) ^ (1 / 8 : ℝ) *
          ((((Z : ℕ) : ℝ) +
              Ctail * ((Y : ℝ) / (1 : ℝ) * (Z : ℝ) ^ (-1 / 4 : ℝ) +
                (Z : ℝ) ^ (1 / 2 : ℝ))) +
            (((Z : ℕ) : ℝ) + (Z : ℝ) ^ (1 / 4 : ℝ) *
              ((Y : ℝ) / ((1 : ℝ) * (Z : ℝ) ^ (1 / 2 : ℝ)) + 1))) := by
        simpa using hII0
      _ ≤ KII * (Y : ℝ) := by simpa [KII] using hIIabs
  have hIV := ShiuClassIVBound.modulus_mul_classIVMass_cast_le_logPow
    4 X Y 1 0 Z cutoff (by norm_num) hX3 hZ3 hcutoff2 hlogcutoff
      hYX hXZ hZY (by norm_num) (by omega) (by norm_num) (by norm_num)
      (by simpa using hZsq) (by
        intro r b hb
        have hbIcc := ShiuClassIVBound.activePrefix_mem_Icc hb
        have hbCop := (ShiuClassIVBound.activePrefix_mem_tauSquareSmoothTailSupport
          hZ3 (by omega : 1 ≤ cutoff) (by norm_num) hb).2.2
        have hbOuter : b ∈ classIOuterPrefixes Z 1 :=
          Finset.mem_filter.mpr ⟨hbIcc, hbCop⟩
        exact hmodLength b hbOuter)
  let massIIIII : ℕ :=
    ShiuEndToEnd.classMass 4 X Y 1 0 Z cutoff FourClass.II +
      ShiuEndToEnd.classMass 4 X Y 1 0 Z cutoff FourClass.III
  have hmassIIIII : (massIIIII : ℝ) =
      ShiuClassIIIII.exceptionalMass 4 X Y 1 0 Z
        (ShiuLemma1ClassIII.classIIICutoff X) := by
    simp [massIIIII, ShiuEndToEnd.classMass,
      ShiuClassIIIII.exceptionalMass, cutoff,
      ShiuEndToEnd.smoothCutoff, ShiuClassIBound.smoothCutoff,
      ShiuLemma1ClassIII.classIIICutoff]
  have hlogone : (1 : ℝ) ≤ Real.log (X : ℝ) := by
    have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
    rw [Real.le_log_iff_exp_le hXpos]
    calc
      Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
      _ ≤ 3 := by norm_num
      _ ≤ (X : ℝ) := by exact_mod_cast hX3
  have hlogpow1 : (1 : ℝ) ≤ Real.log (X : ℝ) ^ 16 :=
    one_le_pow₀ hlogone
  have hIIlog : (massIIIII : ℝ) ≤
      KII * (Y : ℝ) * Real.log (X : ℝ) ^ 16 := by
    rw [hmassIIIII]
    calc
      _ ≤ KII * (Y : ℝ) := hII
      _ ≤ KII * (Y : ℝ) * Real.log (X : ℝ) ^ 16 := by
        have : 0 ≤ KII * (Y : ℝ) := by positivity
        nlinarith
  have hpartition := ShiuEndToEnd.progressionSum_eq_fourClassMass
    4 X Y 1 0 Z cutoff
  have htotalCast :
      (progressionSum ((tauAF 4).pmul (tauAF 4)) X Y 1 0 : ℝ) =
        (ShiuEndToEnd.classMass 4 X Y 1 0 Z cutoff FourClass.I : ℝ) +
        (massIIIII : ℝ) +
        (ShiuEndToEnd.classMass 4 X Y 1 0 Z cutoff FourClass.IV : ℝ) := by
    have hpR := congrArg (fun n : ℕ => (n : ℝ)) hpartition
    norm_num at hpR
    simpa [massIIIII, add_assoc] using hpR
  rw [htotalCast]
  have hlog0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hY0 : (0 : ℝ) ≤ Y := by positivity
  calc
    (ShiuEndToEnd.classMass 4 X Y 1 0 Z cutoff FourClass.I : ℝ) +
        (massIIIII : ℝ) +
        (ShiuEndToEnd.classMass 4 X Y 1 0 Z cutoff FourClass.IV : ℝ) ≤
      KI * (Y : ℝ) * Real.log (X : ℝ) ^ 16 +
        KII * (Y : ℝ) * Real.log (X : ℝ) ^ 16 +
        KIV * (Y : ℝ) * Real.log (X : ℝ) ^ 16 := by
      have hI' :
          (ShiuEndToEnd.classMass 4 X Y 1 0 Z cutoff FourClass.I : ℝ) ≤
            KI * (Y : ℝ) * Real.log (X : ℝ) ^ 16 := by
        simpa [KI] using! hI
      have hIV' :
          (ShiuEndToEnd.classMass 4 X Y 1 0 Z cutoff FourClass.IV : ℝ) ≤
            KIV * (Y : ℝ) * Real.log (X : ℝ) ^ 16 := by
        simpa [KIV] using hIV
      exact add_le_add (add_le_add hI' hIIlog) hIV'
    _ = C * (Y : ℝ) * Real.log (X : ℝ) ^ 16 := by
      dsimp [C]
      ring

/-- Modulus one removes the progression mask, exposing the literal finite
short-interval moment used by the Ramanujan-tail energy. -/
theorem certified_tauFourSquare_Ioc_shortInterval :
    ∃ C : ℝ, 0 < C ∧
      ∃ X₀ : ℕ, 3 ≤ X₀ ∧
        ∀ X Y : ℕ,
          X₀ ≤ X → Y ≤ X → X < Y ^ 8 →
          (∑ n ∈ Finset.Ioc (X - Y) X, (tauAF 4 n : ℝ) ^ 2) ≤
            C * (Y : ℝ) * (Real.log (X : ℝ)) ^ 16 := by
  obtain ⟨C, hC, X₀, hX₀, hbound⟩ := certified_tauFourSquare_shortInterval
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro X Y hX hYX hXY
  have h := hbound X Y hX hYX hXY
  simpa [progressionSum, ArithmeticFunction.pmul_apply, pow_two,
    Nat.ModEq, Nat.mod_one] using h

/-! ## Exact signed translated-window envelope -/

/-- A ceiling-safe integer length covering a closed real interval of radius
`H`.  The extra two units absorb both closed endpoints and the ceiling. -/
def translatedEnvelopeLength (H : ℝ) : ℕ := ⌈2 * H⌉₊ + 2

/-- A common positive endpoint containing the absolute values of all shifts.
Taking the maximum with the length handles windows crossing zero. -/
def translatedEnvelopeUpper (H h₀ : ℝ) : ℕ :=
  max ⌈|h₀| + H⌉₊ (translatedEnvelopeLength H)

/-- Positive and negative integer fibers are separately injective under
`natAbs`; hence an arbitrary signed set costs at most two copies of one
positive interval. -/
theorem sum_int_natAbs_nonzero_le_two_sum_Ioc
    (s : Finset ℤ) (U Y : ℕ) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n)
    (hmem : ∀ z ∈ s, z ≠ 0 → z.natAbs ∈ Finset.Ioc (U - Y) U) :
    (∑ z ∈ s, if z = 0 then 0 else f z.natAbs) ≤
      2 * ∑ n ∈ Finset.Ioc (U - Y) U, f n := by
  classical
  let s0 : Finset ℤ := s.filter (fun z => z ≠ 0)
  let sp : Finset ℤ := s0.filter (fun z => 0 < z)
  let sn : Finset ℤ := s0.filter (fun z => ¬ 0 < z)
  have hzero :
      (∑ z ∈ s, if z = 0 then 0 else f z.natAbs) =
        ∑ z ∈ s0, f z.natAbs := by
    simp only [s0, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hz0 : z = 0 <;> simp [hz0]
  have hsplit :
      (∑ z ∈ s0, f z.natAbs) =
        (∑ z ∈ sp, f z.natAbs) + ∑ z ∈ sn, f z.natAbs := by
    simpa [sp, sn] using
      (Finset.sum_filter_add_sum_filter_not s0 (fun z : ℤ => 0 < z)
        (fun z => f z.natAbs)).symm
  have hposinj : Set.InjOn Int.natAbs (sp : Set ℤ) := by
    intro a ha b hb hab
    have ha' : a ∈ s0 ∧ 0 < a := by simpa [sp] using ha
    have hb' : b ∈ s0 ∧ 0 < b := by simpa [sp] using hb
    exact (Int.natAbs_inj_of_nonneg_of_nonneg ha'.2.le hb'.2.le).mp hab
  have hneginj : Set.InjOn Int.natAbs (sn : Set ℤ) := by
    intro a ha b hb hab
    have ha' : a ∈ s0 ∧ ¬ 0 < a := by simpa [sn] using ha
    have hb' : b ∈ s0 ∧ ¬ 0 < b := by simpa [sn] using hb
    exact (Int.natAbs_inj_of_nonpos_of_nonpos
      (le_of_not_gt ha'.2) (le_of_not_gt hb'.2)).mp hab
  have hpossub : sp.image Int.natAbs ⊆ Finset.Ioc (U - Y) U := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
    have hz' : z ∈ s0 ∧ 0 < z := by simpa [sp] using hz
    have hzs : z ∈ s ∧ z ≠ 0 := by simpa [s0] using hz'.1
    exact hmem z hzs.1 hzs.2
  have hnegsub : sn.image Int.natAbs ⊆ Finset.Ioc (U - Y) U := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
    have hz' : z ∈ s0 ∧ ¬ 0 < z := by simpa [sn] using hz
    have hzs : z ∈ s ∧ z ≠ 0 := by simpa [s0] using hz'.1
    exact hmem z hzs.1 hzs.2
  have hpos : (∑ z ∈ sp, f z.natAbs) ≤
      ∑ n ∈ Finset.Ioc (U - Y) U, f n := by
    rw [← Finset.sum_image hposinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpossub
      (fun n hn hnot => hf n)
  have hneg : (∑ z ∈ sn, f z.natAbs) ≤
      ∑ n ∈ Finset.Ioc (U - Y) U, f n := by
    rw [← Finset.sum_image hneginj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hnegsub
      (fun n hn hnot => hf n)
  rw [hzero, hsplit]
  linarith

/-- Every nonzero member of the literal floor/ceiling translated window lies
in the common positive Ioc envelope. -/
theorem natAbs_mem_translatedEnvelope
    {H h₀ : ℝ} (hH : 0 ≤ H) {h : ℤ}
    (hh : h ∈ PrimePairEndpoints.translatedWindow H h₀) (hh0 : h ≠ 0) :
    h.natAbs ∈ Finset.Ioc
      (translatedEnvelopeUpper H h₀ - translatedEnvelopeLength H)
      (translatedEnvelopeUpper H h₀) := by
  let W := translatedEnvelopeLength H
  let A : ℕ := ⌈|h₀| + H⌉₊
  let U := max A W
  have hbounds := PrimePairEndpoints.mem_translatedWindow_iff_real_bounds.mp hh
  have habsUpper : |(h : ℝ)| ≤ |h₀| + H := by
    rw [abs_le]
    constructor
    · have hh0le : -h₀ ≤ |h₀| := by
        simpa using neg_le_abs h₀
      linarith
    · have hh0le : h₀ ≤ |h₀| := le_abs_self h₀
      linarith
  have hnatAbsCast : (h.natAbs : ℝ) = |(h : ℝ)| := by
    rw [← Int.cast_abs]
    norm_num
  have hAupper : h.natAbs ≤ A := by
    have hceil : |h₀| + H ≤ (A : ℝ) := by
      simpa [A] using (Nat.le_ceil (|h₀| + H))
    have hcast : (h.natAbs : ℝ) ≤ (A : ℝ) := by
      rw [hnatAbsCast]
      exact habsUpper.trans hceil
    exact_mod_cast hcast
  have hUpper : h.natAbs ≤ U := hAupper.trans (le_max_left A W)
  have hLowerAbs : |h₀| - H ≤ |(h : ℝ)| := by
    by_cases hh₀ : 0 ≤ h₀
    · rw [abs_of_nonneg hh₀]
      exact hbounds.1.trans (le_abs_self (h : ℝ))
    · rw [abs_of_neg (lt_of_not_ge hh₀)]
      have hn := neg_le_abs (h : ℝ)
      linarith [hbounds.2]
  have hLower : U - W < h.natAbs := by
    by_cases hUA : U = W
    · rw [hUA, Nat.sub_self]
      exact Int.natAbs_pos.mpr hh0
    · have hUeq : U = A := by
        dsimp [U]
        rw [max_eq_left]
        by_contra hnot
        have hAW : A < W := lt_of_not_ge hnot
        have : max A W = W := max_eq_right hAW.le
        exact hUA this
      have hWA : W ≤ A := by simpa [U, hUeq] using le_max_right A W
      have hceilA : (A : ℝ) < |h₀| + H + 1 := by
        simpa [A] using
          Nat.ceil_lt_add_one (show 0 ≤ |h₀| + H by positivity)
      have hceilW : 2 * H ≤ ((⌈2 * H⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have hWcast : 2 * H + 2 ≤ (W : ℝ) := by
        dsimp [W, translatedEnvelopeLength]
        norm_num
        linarith
      have hsubCast : ((A - W : ℕ) : ℝ) = (A : ℝ) - (W : ℝ) := by
        rw [Nat.cast_sub hWA]
      have hreal : ((A - W : ℕ) : ℝ) < |(h : ℝ)| := by
        rw [hsubCast]
        linarith
      rw [hUeq]
      have hcast : ((A - W : ℕ) : ℝ) < (h.natAbs : ℝ) := by
        rw [hnatAbsCast]
        exact hreal
      exact_mod_cast hcast
  change h.natAbs ∈ Finset.Ioc (U - W) U
  exact Finset.mem_Ioc.mpr ⟨hLower, hUpper⟩

theorem translatedEnvelopeLength_cast_le_five_mul
    {H : ℝ} (hH : 1 ≤ H) :
    (translatedEnvelopeLength H : ℝ) ≤ 5 * H := by
  have hceil : ((⌈2 * H⌉₊ : ℕ) : ℝ) < 2 * H + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  dsimp [translatedEnvelopeLength]
  norm_num
  linarith

/-- Deterministic public signed-window adapter.  The three explicit envelope
hypotheses are precisely what remains to be derived from `LegalParameters`. -/
theorem certified_tauFourSquare_translatedWindow_of_envelope :
    ∃ C : ℝ, 0 < C ∧
      ∃ U₀ : ℕ, 3 ≤ U₀ ∧
        ∀ X H h₀ : ℝ,
          3 ≤ X → 1 ≤ H →
          let W := translatedEnvelopeLength H
          let U := translatedEnvelopeUpper H h₀
          U₀ ≤ U → W ≤ U → U < W ^ 8 →
          (U : ℝ) ≤ 3 * X →
          (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
              if h = 0 then 0 else (tauAF 4 h.natAbs : ℝ) ^ 2) ≤
            C * H * (Real.log X) ^ 16 := by
  obtain ⟨C₀, hC₀, U₀, hU₀, hIoc⟩ :=
    certified_tauFourSquare_Ioc_shortInterval
  let C : ℝ := 10 * C₀ * (2 : ℝ) ^ 16
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, U₀, hU₀, ?_⟩
  intro X H h₀ hX hH
  dsimp only
  intro hU₀U hWU hUW hUX
  let W := translatedEnvelopeLength H
  let U := translatedEnvelopeUpper H h₀
  have hsigned := sum_int_natAbs_nonzero_le_two_sum_Ioc
    (PrimePairEndpoints.translatedWindow H h₀) U W
    (fun n => (tauAF 4 n : ℝ) ^ 2) (fun n => sq_nonneg _)
    (fun h hh hh0 => by
      simpa [U, W] using natAbs_mem_translatedEnvelope (show 0 ≤ H by linarith) hh hh0)
  have hU₀U' : U₀ ≤ U := by simpa [U] using hU₀U
  have hIoc' := hIoc U W hU₀U'
    (by simpa [U, W] using hWU) (by simpa [U, W] using hUW)
  have hU3 : 3 ≤ U := hU₀.trans hU₀U'
  have hUpos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast (show 0 < U by omega)
  have h3Xpos : 0 < 3 * X := by positivity
  have hlogUX0 : Real.log (U : ℝ) ≤ Real.log (3 * X) :=
    Real.log_le_log hUpos (by simpa [U] using hUX)
  have hlog3X := SupportBoundaryQuantitative.log_three_mul_le_two_log hX
  have hlogUX : Real.log (U : ℝ) ≤ 2 * Real.log X :=
    hlogUX0.trans hlog3X
  have hlogU0 : 0 ≤ Real.log (U : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ U by omega))
  have hlogX0 : 0 ≤ Real.log X :=
    Real.log_nonneg (by linarith)
  have hpow : Real.log (U : ℝ) ^ 16 ≤
      (2 * Real.log X) ^ 16 :=
    pow_le_pow_left₀ hlogU0 hlogUX 16
  have hWcast := translatedEnvelopeLength_cast_le_five_mul hH
  calc
    (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
        if h = 0 then 0 else (tauAF 4 h.natAbs : ℝ) ^ 2) ≤
      2 * ∑ n ∈ Finset.Ioc (U - W) U, (tauAF 4 n : ℝ) ^ 2 := hsigned
    _ ≤ 2 * (C₀ * (W : ℝ) * Real.log (U : ℝ) ^ 16) := by
      gcongr
    _ ≤ 2 * (C₀ * (5 * H) * (2 * Real.log X) ^ 16) := by
      have hleft0 : 0 ≤ C₀ * (W : ℝ) := by positivity
      have hright0 : 0 ≤ (2 * Real.log X) ^ 16 := by positivity
      gcongr
    _ = C * H * (Real.log X) ^ 16 := by
      dsimp [C]
      ring

/-- Fully public all-center short-interval moment.  No theorem-valued premise
remains: the envelope inequalities are derived from the literal
`LegalParameters` range, including both ceiling units. -/
theorem certified_tauFourSquare_legalTranslatedWindow
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧
      ∀ X H h₀ : ℝ, X₀ ≤ X →
        PrimePairEndpoints.LegalParameters ε X H h₀ →
        (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
            if h = 0 then 0 else (tauAF 4 h.natAbs : ℝ) ^ 2) ≤
          C * H * (Real.log X) ^ 16 := by
  obtain ⟨C, hC, U₀, hU₀, hdet⟩ :=
    certified_tauFourSquare_translatedWindow_of_envelope
  let a : ℝ := 2 / 15 + ε
  let δ : ℝ := 8 * a - 1
  have ha : 0 < a := by dsimp [a]; linarith
  have hδ : 0 < δ := by dsimp [δ, a]; linarith
  have hUevent : ∀ᶠ X : ℝ in Filter.atTop,
      (U₀ : ℝ) ≤ Real.rpow X a :=
    (tendsto_rpow_atTop ha).eventually (Filter.eventually_ge_atTop (U₀ : ℝ))
  have hgapEvent : ∀ᶠ X : ℝ in Filter.atTop,
      3 < Real.rpow X δ :=
    (tendsto_rpow_atTop hδ).eventually (Filter.eventually_gt_atTop 3)
  have hevent : ∀ᶠ X : ℝ in Filter.atTop,
      3 ≤ X ∧ (U₀ : ℝ) ≤ Real.rpow X a ∧
        3 * X < Real.rpow X (8 * a) := by
    filter_upwards [Filter.eventually_ge_atTop (3 : ℝ), hUevent, hgapEvent]
      with X hX hU hgap
    have hXpos : 0 < X := by linarith
    have hmul : 3 * X < Real.rpow X δ * X :=
      mul_lt_mul_of_pos_right hgap hXpos
    have hrewrite : Real.rpow X δ * X = Real.rpow X (8 * a) := by
      calc
        Real.rpow X δ * X = Real.rpow X δ * Real.rpow X 1 := by simp
        _ = Real.rpow X (δ + 1) := (Real.rpow_add hXpos δ 1).symm
        _ = Real.rpow X (8 * a) := by dsimp [δ]; ring_nf
    exact ⟨hX, hU, hmul.trans_eq hrewrite⟩
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hevent
  let X₀ : ℝ := max 3 T
  have hX₀ : 3 ≤ X₀ := le_max_left _ _
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X H h₀ hX hlegal
  have hTX : T ≤ X := (le_max_right 3 T).trans hX
  obtain ⟨hX3, hUscale, hgap⟩ := hT X hTX
  have hXone : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hH : 1 ≤ H :=
    (Real.one_le_rpow hXone ha.le).trans (by simpa [a] using hlegal.1)
  let W := translatedEnvelopeLength H
  let A : ℕ := ⌈|h₀| + H⌉₊
  let U := translatedEnvelopeUpper H h₀
  have hW2 : 2 ≤ W := by dsimp [W, translatedEnvelopeLength]; omega
  have hWU : W ≤ U := by
    dsimp [U, translatedEnvelopeUpper]
    exact le_max_right _ _
  have hWcastLower : H ≤ (W : ℝ) := by
    have hc : 2 * H ≤ ((⌈2 * H⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    dsimp [W, translatedEnvelopeLength]
    norm_num
    linarith
  have hU₀U : U₀ ≤ U := by
    have hUreal : (U₀ : ℝ) ≤ (W : ℝ) := by
      calc
        (U₀ : ℝ) ≤ Real.rpow X a := hUscale
        _ ≤ H := by simpa [a] using hlegal.1
        _ ≤ (W : ℝ) := hWcastLower
    have hU₀W : U₀ ≤ W := by exact_mod_cast hUreal
    exact hU₀W.trans hWU
  have hrpowUpper : Real.rpow X (1 - ε) ≤ X := by
    calc
      Real.rpow X (1 - ε) ≤ Real.rpow X 1 :=
        Real.rpow_le_rpow_of_exponent_le hXone (by linarith)
      _ = X := by simp
  have hAcast : (A : ℝ) ≤ 3 * X := by
    have hceil : (A : ℝ) < |h₀| + H + 1 := by
      simpa [A] using Nat.ceil_lt_add_one
        (show 0 ≤ |h₀| + H by positivity)
    have hh₀abs : |h₀| = h₀ := abs_of_nonneg hlegal.2.2.1
    rw [hh₀abs] at hceil
    have hh₀up := hlegal.2.2.2
    have hHup := hlegal.2.1
    linarith
  have hWcast : (W : ℝ) ≤ 3 * X := by
    have hceil : ((⌈2 * H⌉₊ : ℕ) : ℝ) < 2 * H + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hHup := hlegal.2.1
    dsimp [W, translatedEnvelopeLength]
    norm_num
    linarith
  have hUcast : (U : ℝ) ≤ 3 * X := by
    have hcastMax : (U : ℝ) = max (A : ℝ) (W : ℝ) := by
      dsimp [U, A, W, translatedEnvelopeUpper]
      norm_num
    rw [hcastMax]
    exact max_le hAcast hWcast
  have hbasePow : Real.rpow X (8 * a) ≤ (W : ℝ) ^ 8 := by
    have hLower : Real.rpow X a ≤ H := by simpa [a] using hlegal.1
    have hlow : Real.rpow X a ≤ (W : ℝ) := hLower.trans hWcastLower
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg hXpos.le a)
      hlow (8 : ℕ)
    have hleft : (Real.rpow X a) ^ 8 = Real.rpow X (8 * a) := by
      calc
        (Real.rpow X a) ^ 8 = Real.rpow X (a * 8) :=
          (Real.rpow_mul_natCast hXpos.le a 8).symm
        _ = Real.rpow X (8 * a) := by ring_nf
    calc
      Real.rpow X (8 * a) = (Real.rpow X a) ^ 8 := hleft.symm
      _ ≤ (W : ℝ) ^ 8 := hp
  have hA_lt : A < W ^ 8 := by
    have hreal : (A : ℝ) < ((W ^ 8 : ℕ) : ℝ) := by
      calc
        (A : ℝ) ≤ 3 * X := hAcast
        _ < Real.rpow X (8 * a) := hgap
        _ ≤ (W : ℝ) ^ 8 := hbasePow
        _ = ((W ^ 8 : ℕ) : ℝ) := by norm_num
    exact_mod_cast hreal
  have hW_lt : W < W ^ 8 := by
    calc
      W = W ^ 1 := by simp
      _ < W ^ 8 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hU_lt : U < W ^ 8 := by
    dsimp [U, translatedEnvelopeUpper]
    rw [max_lt_iff]
    exact ⟨by simpa [A] using hA_lt, by simpa [W] using hW_lt⟩
  exact hdet X H h₀ hX3 hH hU₀U hWU hU_lt hUcast

/-- Selectable Ramanujan-truncation remainder on every legal translated
window.  The numerator is now the aperture `H`, not the global shift radius;
the only denominator is the certified pointwise `Q+1`. -/
theorem certified_legalRamanujanTailEnergy
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧
      ∀ X H h₀ : ℝ, ∀ Q : ℕ, X₀ ≤ X →
        PrimePairEndpoints.LegalParameters ε X H h₀ →
        MAPRamanujanWindowAbsorption.ramanujanTailEnergy H h₀ Q ≤
          (C * H * (Real.log X) ^ 16) / (Q + 1 : ℕ) := by
  obtain ⟨C₀, X₀, hC₀, hX₀, hmoment⟩ :=
    certified_tauFourSquare_legalTranslatedWindow ε hε
  let C : ℝ :=
    (MAPRamanujanTailWeighted.basePrimeMassConstant ^ 2 + 1) * C₀
  have hC : 0 < C := by
    dsimp [C]
    have hbase0 : 0 ≤ MAPRamanujanTailWeighted.basePrimeMassConstant ^ 2 :=
      sq_nonneg _
    positivity
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X H h₀ Q hX hlegal
  have hM := hmoment X H h₀ hX hlegal
  let c : ℝ := MAPRamanujanTailWeighted.basePrimeMassConstant ^ 2 /
    (Q + 1 : ℕ)
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hpoint :
      MAPRamanujanWindowAbsorption.ramanujanTailEnergy H h₀ Q ≤
        ∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
          if h = 0 then 0 else c * (tauAF 4 h.natAbs : ℝ) ^ 2 := by
    unfold MAPRamanujanWindowAbsorption.ramanujanTailEnergy
    apply Finset.sum_le_sum
    intro h hh
    by_cases hh0 : h = 0
    · simp [hh0]
    · rw [if_neg hh0, if_neg hh0]
      have ht :=
        MAPRamanujanWindowAbsorption.norm_truncatedSingularCoefficient_sub_singular_sq_le_tauAF_four
          hh0 Q
      simpa [c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using ht
  have hfactor :
      (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
          if h = 0 then 0 else c * (tauAF 4 h.natAbs : ℝ) ^ 2) =
        c * (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
          if h = 0 then 0 else (tauAF 4 h.natAbs : ℝ) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    by_cases hh0 : h = 0 <;> simp [hh0]
  have hbaseC :
      MAPRamanujanTailWeighted.basePrimeMassConstant ^ 2 * C₀ ≤ C := by
    dsimp [C]
    nlinarith [sq_nonneg MAPRamanujanTailWeighted.basePrimeMassConstant]
  have hX3 : 3 ≤ X := hX₀.trans hX
  have hXone : 1 ≤ X := (by norm_num : (1 : ℝ) ≤ 3).trans hX3
  have hH0 : 0 ≤ H := by
    have ha : 0 ≤ 2 / 15 + ε := by linarith
    exact (Real.rpow_nonneg (by linarith) _).trans hlegal.1
  have hlog0 : 0 ≤ Real.log X :=
    Real.log_nonneg hXone
  calc
    MAPRamanujanWindowAbsorption.ramanujanTailEnergy H h₀ Q ≤
        ∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
          if h = 0 then 0 else c * (tauAF 4 h.natAbs : ℝ) ^ 2 := hpoint
    _ = c * (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
          if h = 0 then 0 else (tauAF 4 h.natAbs : ℝ) ^ 2) := hfactor
    _ ≤ c * (C₀ * H * (Real.log X) ^ 16) :=
      mul_le_mul_of_nonneg_left hM hc0
    _ = (MAPRamanujanTailWeighted.basePrimeMassConstant ^ 2 * C₀) *
          H * (Real.log X) ^ 16 / (Q + 1 : ℕ) := by
      dsimp [c]
      ring
    _ ≤ C * H * (Real.log X) ^ 16 / (Q + 1 : ℕ) := by
      gcongr

end
end MAPShortIntervalTauFour

#print axioms MAPShortIntervalTauFour.certified_tauFourSquare_shortInterval
#print axioms MAPShortIntervalTauFour.certified_tauFourSquare_Ioc_shortInterval
#print axioms MAPShortIntervalTauFour.certified_tauFourSquare_legalTranslatedWindow
#print axioms MAPShortIntervalTauFour.certified_legalRamanujanTailEnergy
