import RamachandraShortContourFamilyMoment
import RamachandraGammaWeightUniformMass
import MRTLemma215ScaleClassifierV3

/-!
# Source-range logarithmic absorption for the literal short contour

The analytic short-contour estimate has already been proved in the preceding
modules.  This file performs only deterministic dyadic and logarithmic
bookkeeping and constructs the actual source moment/continuity packages.
-/

namespace RamachandraShortContourSourcePackage

open scoped BigOperators Interval
open Complex MeasureTheory
open RamachandraPrimitiveShiftedContourReduction
open RamachandraPrimitiveShiftedPackageAdapter
open RamachandraShortContourFamilyMoment
open RamachandraShortContourContinuity
open RamachandraShortHeadFamilyBudget
open RamachandraShortFunctionalFactorMomentEnvelope
open RamachandraGammaWeightIntegrability
open RamachandraGammaWeightUniformMass
open RamachandraShiftedDirectParameters
open MRTLemma215DyadicPartition
open MRTLemma215ScaleClassifierV3

noncomputable section

set_option maxHeartbeats 1000000

variable {d : ℕ} [NeZero d]

private theorem log_two_le_log {X : ℝ} (hX : 3 ≤ X) :
    Real.log 2 ≤ Real.log X :=
  Real.log_le_log (by norm_num) (by linarith)

private theorem sourceDyadicCount_floor_le
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
  have hnatlog : (((M - 1).log2 : ℕ) : ℝ) ≤ Real.logb 2 (M : ℝ) :=
    hlogb.trans hmono
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 :=
    Real.log_two_gt_d9.le.trans' (by norm_num)
  have hinvlog2 : (Real.log 2)⁻¹ ≤ 2 := by
    have hi : (Real.log 2)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ :=
      (inv_le_inv₀ (a := Real.log 2) (b := (1 / 2 : ℝ))
        (Real.log_pos (by norm_num)) (by norm_num)).2 hlog2half
    norm_num at hi ⊢
    exact hi
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM2)
  have hlogM0 : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hlogbBound : Real.logb 2 (M : ℝ) ≤ 2 * Real.log (M : ℝ) := by
    unfold Real.logb
    rw [div_eq_mul_inv]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hinvlog2 hlogM0
  have hMle : (M : ℝ) ≤ X := by
    dsimp [M]
    exact_mod_cast Nat.floor_le (by linarith : 0 ≤ X)
  have hlogMle : Real.log (M : ℝ) ≤ Real.log X :=
    Real.log_le_log hMpos hMle
  have hL1 : 1 ≤ Real.log X :=
    (one_lt_log_of_three_le (by linarith)).le
  unfold sourceDyadicCount
  push_cast
  dsimp [M] at hnatlog hlogbBound hlogMle ⊢
  nlinarith

private theorem sourceHead_harmonic_le
    {X : ℝ} (hX : 3 ≤ X)
    (j : Fin (sourceDyadicCount ⌊X⌋₊)) :
    (harmonic (2 * 2 ^ (j : ℕ)) : ℝ) ≤ 3 * Real.log X := by
  let M := ⌊X⌋₊
  have hM2 : 2 ≤ M := by
    dsimp [M]
    apply Nat.le_floor
    norm_num
    linarith
  have hNleNat : 2 ^ (j : ℕ) ≤ M := by
    simpa [M] using sourceDyadicBase_le_cutoff hM2 j
  have hMle : (M : ℝ) ≤ X := by
    dsimp [M]
    exact_mod_cast Nat.floor_le (by linarith : 0 ≤ X)
  have htwoNpos : (0 : ℝ) < (2 * 2 ^ (j : ℕ) : ℕ) := by positivity
  have htwoNle : ((2 * 2 ^ (j : ℕ) : ℕ) : ℝ) ≤ 2 * X := by
    have hNleCast : ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast hNleNat
    have hNle : ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ X := hNleCast.trans hMle
    calc
      ((2 * 2 ^ (j : ℕ) : ℕ) : ℝ) =
          2 * ((2 ^ (j : ℕ) : ℕ) : ℝ) := by norm_num
      _ ≤ 2 * X := mul_le_mul_of_nonneg_left hNle (by norm_num)
  have hlogle : Real.log ((2 * 2 ^ (j : ℕ) : ℕ) : ℝ) ≤
      Real.log (2 * X) := Real.log_le_log htwoNpos htwoNle
  have hlogsplit : Real.log (2 * X) = Real.log 2 + Real.log X := by
    rw [Real.log_mul (by norm_num) (by linarith : X ≠ 0)]
  have hlog2 := log_two_le_log hX
  have hL1 : 1 ≤ Real.log X :=
    (one_lt_log_of_three_le (by linarith)).le
  calc
    (harmonic (2 * 2 ^ (j : ℕ)) : ℝ) ≤
        1 + Real.log ((2 * 2 ^ (j : ℕ) : ℕ) : ℝ) :=
      harmonic_le_one_add_log _
    _ ≤ 1 + Real.log (2 * X) := add_le_add_right hlogle _
    _ ≤ 3 * Real.log X := by rw [hlogsplit]; linarith

private theorem shortHeadSourceShellCost_le
    (d : ℕ) [NeZero d] {T : ℝ} (hT : 3 ≤ T)
    (j : Fin (sourceDyadicCount ⌊primitiveShiftedScale d T⌋₊)) :
    shortHeadSourceShellCost d ⌊primitiveShiftedScale d T⌋₊ T j ≤
      3000 * primitiveShiftedScale d T *
        Real.log (primitiveShiftedScale d T) ^ 4 := by
  let X := primitiveShiftedScale d T
  let M := ⌊X⌋₊
  have hX : 3 ≤ X := by
    dsimp [X, primitiveShiftedScale]
    have hd : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
    nlinarith
  have hM2 : 2 ≤ M := by
    dsimp [M]
    apply Nat.le_floor
    norm_num
    linarith
  have hNleNat : 2 ^ (j : ℕ) ≤ M := by
    simpa [M, X] using sourceDyadicBase_le_cutoff hM2 j
  have hMle : (M : ℝ) ≤ X := by
    dsimp [M]
    exact_mod_cast Nat.floor_le (by linarith : 0 ≤ X)
  have hNleCast : ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hNleNat
  have hNle : ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ X := hNleCast.trans hMle
  have hharm := sourceHead_harmonic_le hX j
  have hpi : Real.pi ≤ 4 := by linarith [Real.pi_le_four]
  have hL0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlen : (d : ℝ) * (2 * T) +
      8 * Real.pi * ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ 34 * X := by
    have hident : (d : ℝ) * (2 * T) = 2 * X := by
      dsimp [X, primitiveShiftedScale]
      ring
    rw [hident]
    have hpN : Real.pi * ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ 4 * X :=
      mul_le_mul hpi hNle (by positivity) (by norm_num)
    nlinarith
  unfold shortHeadSourceShellCost
  change ((d : ℝ) * (2 * T) + 8 * Real.pi * ((2 ^ (j : ℕ) : ℕ) : ℝ)) *
      (harmonic (2 * 2 ^ (j : ℕ)) : ℝ) ^ 4 ≤ _
  have hharm0 : 0 ≤ (harmonic (2 * 2 ^ (j : ℕ)) : ℝ) := by
    exact_mod_cast (harmonic_pos (by positivity : 2 * 2 ^ (j : ℕ) ≠ 0)).le
  have hh4 := pow_le_pow_left₀ hharm0 hharm 4
  calc
    _ ≤ (34 * X) * (3 * Real.log X) ^ 4 :=
      mul_le_mul hlen hh4 (by positivity) (by positivity)
    _ ≤ 3000 * X * Real.log X ^ 4 := by
      ring_nf
      gcongr
      norm_num

/-- The finite reflected head has source cost `X log(X)^6`. -/
theorem shortHeadAllCharacterMellinMoment_le_log7
    (d : ℕ) [NeZero d] {T sigma : ℝ}
    (hT : 3 ≤ T) (hX : 6 ≤ primitiveShiftedScale d T)
    (hline : 1 / 2 ≤ 1 - sigma +
      (Real.log (primitiveShiftedScale d T))⁻¹) :
    shortHeadAllCharacterMellinMoment d (primitiveShiftedScale d T) T sigma ≤
      (gammaPolynomialAbsoluteMass * (1 + shortGammaPoleGap⁻¹)) *
        100000 * primitiveShiftedScale d T *
          Real.log (primitiveShiftedScale d T) ^ 7 := by
  let X := primitiveShiftedScale d T
  let J := sourceDyadicCount ⌊X⌋₊
  let W := ∫ v : ℝ, gammaPolynomialWeight (-(Real.log X)⁻¹) v
  have hX3 : 3 ≤ X := by dsimp [X]; linarith
  have hL1 : 1 ≤ Real.log X := (one_lt_log_of_three_le hX3).le
  have hJ : (J : ℝ) ≤ 3 * Real.log X := by
    simpa [J] using sourceDyadicCount_floor_le (X := X) (by linarith)
  have hshell (j : Fin J) : shortHeadSourceShellCost d ⌊X⌋₊ T j ≤
      3000 * X * Real.log X ^ 4 := by
    simpa [X, J] using shortHeadSourceShellCost_le d hT j
  have hsum : (∑ j : Fin J, shortHeadSourceShellCost d ⌊X⌋₊ T j) ≤
      (J : ℝ) * (3000 * X * Real.log X ^ 4) := by
    calc
      _ ≤ ∑ _j : Fin J, (3000 * X * Real.log X ^ 4) :=
        Finset.sum_le_sum (fun j _ => hshell j)
      _ = _ := by simp
  have hbracket : 4 * (d : ℝ) * T + 2 * (J : ℝ) *
      ∑ j : Fin J, shortHeadSourceShellCost d ⌊X⌋₊ T j ≤
      100000 * X * Real.log X ^ 6 := by
    have hX0 : 0 ≤ X := by linarith
    have hJ0 : 0 ≤ (J : ℝ) := by positivity
    have hL0 : 0 ≤ Real.log X := by linarith
    have hident : 4 * (d : ℝ) * T = 4 * X := by
      dsimp [X, primitiveShiftedScale]
      ring
    rw [hident]
    calc
      4 * X + 2 * (J : ℝ) *
          ∑ j : Fin J, shortHeadSourceShellCost d ⌊X⌋₊ T j ≤
          4 * X + 2 * (J : ℝ) * ((J : ℝ) *
            (3000 * X * Real.log X ^ 4)) := by gcongr
      _ ≤ 4 * X + 2 * (3 * Real.log X) * ((3 * Real.log X) *
            (3000 * X * Real.log X ^ 4)) := by gcongr
      _ ≤ 100000 * X * Real.log X ^ 6 := by
        have hpow1 : 1 ≤ Real.log X ^ 6 := one_le_pow₀ hL1
        nlinarith
  have hhead := shortHeadAllCharacterMellinMoment_le d
    (X := X) (T := T) (sigma := sigma)
    (by linarith : 0 ≤ T) (by simpa [X] using hX) (by simpa [X] using hline)
  have hW := integral_gammaPolynomialWeight_short_le_log hX3
  have hW0 : 0 ≤ W := integral_nonneg (fun _ => gammaPolynomialWeight_nonneg _ _)
  have hC0 : 0 ≤ gammaPolynomialAbsoluteMass * (1 + shortGammaPoleGap⁻¹) := by
    exact mul_nonneg gammaPolynomialAbsoluteMass_nonneg
      (add_nonneg (by norm_num) (inv_nonneg.mpr shortGammaPoleGap_pos.le))
  calc
    _ ≤ W * (4 * (d : ℝ) * T + 2 * (J : ℝ) *
        ∑ j : Fin J, shortHeadSourceShellCost d ⌊X⌋₊ T j) := by
      simpa [X, J, W] using hhead
    _ ≤ W * (100000 * X * Real.log X ^ 6) :=
      mul_le_mul_of_nonneg_left hbracket hW0
    _ ≤ ((gammaPolynomialAbsoluteMass * (1 + shortGammaPoleGap⁻¹)) *
          Real.log X) * (100000 * X * Real.log X ^ 6) :=
      mul_le_mul_of_nonneg_right hW (by positivity)
    _ = _ := by ring

def shortSourceMomentConstant : ℝ :=
  100000 * shortFunctionalMomentConstant *
    (gammaPolynomialAbsoluteMass * (1 + shortGammaPoleGap⁻¹)) ^ 2 + 1

theorem shortSourceMomentConstant_pos : 0 < shortSourceMomentConstant := by
  unfold shortSourceMomentConstant
  have hC : 0 ≤ shortFunctionalMomentConstant := shortFunctionalMomentConstant_nonneg
  positivity

/-- The actual literal short contour satisfies the exact source-range
`log^200` moment package. -/
noncomputable def primitiveShiftedShortSourceMomentPackage :
    PrimitiveShiftedSourceMomentPackage primitiveFamilyShortContourSecondMoment := by
  refine {
    C := shortSourceMomentConstant
    C_pos := shortSourceMomentConstant_pos
    bound := ?_ }
  intro q d _ _ T sigma hdq hT hstrip hrange
  let X := primitiveShiftedScale d T
  have hdle : d ≤ q := Nat.le_of_dvd (NeZero.pos q) hdq
  have hdpos : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hTpos : 0 < T := by linarith
  have hX : 6 ≤ X := by
    rcases hrange with hd | hT9
    · have hd0 : d ≠ 0 := NeZero.ne d
      have hd2 : 2 ≤ d := by omega
      dsimp [X, primitiveShiftedScale]
      have hd2r : (2 : ℝ) ≤ d := by exact_mod_cast hd2
      nlinarith
    · dsimp [X, primitiveShiftedScale]
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
      nlinarith
  have hXle : X ≤ (q : ℝ) * T := by
    dsimp [X, primitiveShiftedScale]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdle) hTpos.le
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogQT : 0 < Real.log ((q : ℝ) * T) :=
    Real.log_pos (by nlinarith [show (1 : ℝ) ≤ q by exact_mod_cast NeZero.pos q])
  have hlogle : Real.log X ≤ Real.log ((q : ℝ) * T) :=
    Real.log_le_log (by linarith) hXle
  have hinvle : (100 * Real.log ((q : ℝ) * T))⁻¹ ≤
      (100 * Real.log X)⁻¹ := by
    exact (inv_le_inv₀ (by positivity : 0 < 100 * Real.log ((q : ℝ) * T))
      (by positivity : 0 < 100 * Real.log X)).2
        (mul_le_mul_of_nonneg_left hlogle (by norm_num))
  have hstripX : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log X)⁻¹ := hstrip.trans hinvle
  have hline : 1 / 2 ≤ 1 - sigma + (Real.log X)⁻¹ := by
    have hsigma : sigma ≤ 1 / 2 + (100 * Real.log X)⁻¹ := by
      linarith [(abs_le.mp hstripX).2]
    have hi : (100 * Real.log X)⁻¹ ≤ (Real.log X)⁻¹ := by
      exact (inv_le_inv₀ (by positivity : 0 < 100 * Real.log X)
        hlogX).2 (by nlinarith)
    linarith
  have hfamily := primitiveFamilyShortContourSecondMoment_le_headMoment d
    hT (by simpa [X] using hX) (by simpa [X] using hstripX)
      (by simpa [X] using hline)
  have hhead := shortHeadAllCharacterMellinMoment_le_log7 d hT
    (by simpa [X] using hX) (by simpa [X] using hline)
  have hW := integral_gammaPolynomialWeight_short_le_log (by linarith : 3 ≤ X)
  let G := gammaPolynomialAbsoluteMass * (1 + shortGammaPoleGap⁻¹)
  have hW0 : 0 ≤ ∫ v : ℝ, gammaPolynomialWeight (-(Real.log X)⁻¹) v :=
    integral_nonneg (fun _ => gammaPolynomialWeight_nonneg _ _)
  have hgap0 : 0 ≤ 1 + shortGammaPoleGap⁻¹ := by
    exact add_nonneg (by norm_num) (inv_nonneg.mpr shortGammaPoleGap_pos.le)
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg gammaPolynomialAbsoluteMass_nonneg hgap0
  have hC0 : 0 ≤ shortFunctionalMomentConstant := shortFunctionalMomentConstant_nonneg
  have hhead0 : 0 ≤ shortHeadAllCharacterMellinMoment d X T sigma := by
    unfold shortHeadAllCharacterMellinMoment
    apply integral_nonneg
    intro v
    apply mul_nonneg (gammaPolynomialWeight_nonneg _ _)
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hL1 : 1 ≤ Real.log X := (one_lt_log_of_three_le (by linarith)).le
  have hp : Real.log X ^ 8 ≤ Real.log X ^ 200 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  calc
    primitiveFamilyShortContourSecondMoment d T sigma ≤
        (∫ v : ℝ, gammaPolynomialWeight (-(Real.log X)⁻¹) v) *
          shortFunctionalMomentConstant *
          shortHeadAllCharacterMellinMoment d X T sigma := by simpa [X] using hfamily
    _ ≤ (G * Real.log X) * shortFunctionalMomentConstant *
          (G * 100000 * X * Real.log X ^ 7) := by gcongr
    _ = (100000 * shortFunctionalMomentConstant * G ^ 2) *
          X * Real.log X ^ 8 := by ring
    _ ≤ shortSourceMomentConstant * X * Real.log X ^ 200 := by
      unfold shortSourceMomentConstant
      have hbase : 0 ≤ 100000 * shortFunctionalMomentConstant * G ^ 2 := by positivity
      have hconst : 100000 * shortFunctionalMomentConstant * G ^ 2 ≤
          100000 * shortFunctionalMomentConstant *
            (gammaPolynomialAbsoluteMass * (1 + shortGammaPoleGap⁻¹)) ^ 2 + 1 := by
        dsimp [G]
        linarith
      calc
        _ ≤ (100000 * shortFunctionalMomentConstant * G ^ 2) *
            X * Real.log X ^ 200 := by gcongr
        _ ≤ _ := by gcongr
    _ = shortSourceMomentConstant * ((d : ℝ) * T) *
          Real.log ((d : ℝ) * T) ^ 200 := by rfl

/-- Continuity package for the literal normalized short contour. -/
theorem primitiveShiftedShortSourcePieceContinuity :
    PrimitiveShiftedSourcePieceContinuity
      (fun psi T sigma t => primitiveShiftedShortContour psi T sigma t) := by
  intro q d _ _ T sigma hdq hT hstrip hrange psi
  let X := primitiveShiftedScale d T
  have hdle : d ≤ q := Nat.le_of_dvd (NeZero.pos q) hdq
  have hTpos : 0 < T := by linarith
  have hX : 6 ≤ X := by
    rcases hrange with hd | hT9
    · have hd0 : d ≠ 0 := NeZero.ne d
      have hd2 : 2 ≤ d := by omega
      dsimp [X, primitiveShiftedScale]
      have hd2r : (2 : ℝ) ≤ d := by exact_mod_cast hd2
      nlinarith
    · dsimp [X, primitiveShiftedScale]
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
      nlinarith
  have hXle : X ≤ (q : ℝ) * T := by
    dsimp [X, primitiveShiftedScale]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdle) hTpos.le
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogQT : 0 < Real.log ((q : ℝ) * T) := Real.log_pos (by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    nlinarith)
  have hlogle : Real.log X ≤ Real.log ((q : ℝ) * T) :=
    Real.log_le_log (by linarith) hXle
  have hinvle : (100 * Real.log ((q : ℝ) * T))⁻¹ ≤
      (100 * Real.log X)⁻¹ := by
    exact (inv_le_inv₀ (by positivity : 0 < 100 * Real.log ((q : ℝ) * T))
      (by positivity : 0 < 100 * Real.log X)).2
        (mul_le_mul_of_nonneg_left hlogle (by norm_num))
  have hstripX : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log X)⁻¹ := hstrip.trans hinvle
  exact (continuous_primitiveShiftedShortContour psi
    hT (by simpa [X] using hX) (by simpa [X] using hstripX)).norm.pow 2

end
end RamachandraShortContourSourcePackage

#print axioms RamachandraShortContourSourcePackage.shortHeadAllCharacterMellinMoment_le_log7
#print axioms RamachandraShortContourSourcePackage.primitiveShiftedShortSourceMomentPackage
