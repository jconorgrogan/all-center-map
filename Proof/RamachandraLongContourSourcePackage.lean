import RamachandraLongContourMomentExtraction
import RamachandraLongGammaUniformMass
import RamachandraPrimitiveShiftedPackageAdapter
import RamachandraLongSourceExponentAbsorption

/-!
# Source-range package for Ramachandra's literal long contour

This file performs the final scalar absorption after the exact product-family
Minkowski estimate.  It also exports the continuity package consumed by the
shifted long/short contour adapter.
-/

namespace RamachandraLongContourSourcePackage

open Complex MeasureTheory
open RamachandraPrimitiveShiftedContourReduction
open RamachandraPrimitiveShiftedPackageAdapter
open RamachandraLongContourMomentExtraction
open RamachandraLongContourContinuity
open RamachandraLongGammaUniformMass
open RamachandraLongDyadicCutoff
open RamachandraLongDyadicScalarSummability
open RamachandraShiftedFunctionalFactorMomentEnvelope
open RamachandraShiftedDirectParameters
open RamachandraLongSourceExponentAbsorption

noncomputable section

set_option maxHeartbeats 1000000

/-- A deliberately generous source-independent constant.  Keeping the two
non-elementary masses symbolic avoids any numerical integration in the final
source-scale bookkeeping. -/
def longSourceMomentConstant : ℝ :=
  100000 *
    ((∫ v : ℝ, longGammaWeightEnvelope v) + 1) ^ 2 *
    (longFunctionalMomentConstant + 1) *
    (Real.sqrt (8 + 8 * Real.pi) + 1) ^ 2 *
    (longDyadicTailMass + 1) ^ 2

theorem longSourceMomentConstant_pos : 0 < longSourceMomentConstant := by
  have hG : 0 ≤ ∫ v : ℝ, longGammaWeightEnvelope v :=
    integral_nonneg fun v => by unfold longGammaWeightEnvelope; positivity
  have hF : 0 ≤ longFunctionalMomentConstant :=
    longFunctionalMomentConstant_nonneg
  have hD : 0 ≤ longDyadicTailMass := longDyadicTailMass_nonneg
  unfold longSourceMomentConstant
  positivity

private theorem source_rpow_shift_absorption
    (q d : ℕ) [NeZero q] [NeZero d] {T sigma : ℝ}
    (hdq : d ∣ q) (hT : 3 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹) :
    Real.rpow ((d : ℝ) * T) (-2 * (sigma + 1 / 4)) ≤
      3 * Real.rpow ((d : ℝ) * T) (-3 / 2) := by
  let X : ℝ := (d : ℝ) * T
  let R : ℝ := (q : ℝ) * T
  have hdle : d ≤ q := Nat.le_of_dvd (NeZero.pos q) hdq
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hTpos : 0 < T := by linarith
  have hX : 3 ≤ X := by dsimp [X]; nlinarith
  have hR : 3 ≤ R := by dsimp [R]; nlinarith
  have hXR : X ≤ R := by
    dsimp [X, R]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdle) hTpos.le
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  have hlogle : Real.log X ≤ Real.log R :=
    Real.log_le_log (by linarith) hXR
  have hinvle : (100 * Real.log R)⁻¹ ≤ (100 * Real.log X)⁻¹ := by
    exact (inv_le_inv₀ (by positivity : 0 < 100 * Real.log R)
      (by positivity : 0 < 100 * Real.log X)).2
        (mul_le_mul_of_nonneg_left hlogle (by norm_num))
  have hdelta : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log X)⁻¹ := by simpa [R] using hstrip.trans hinvle
  have hsigma : (1 / 2 : ℝ) - (100 * Real.log X)⁻¹ ≤ sigma :=
    by linarith [(abs_le.mp hdelta).1]
  have hexponent : -2 * (sigma + 1 / 4) ≤
      -3 / 2 + 2 * (100 * Real.log X)⁻¹ := by linarith
  have hrpowexp := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ X) hexponent
  have hsmall : Real.rpow X (2 * (100 * Real.log X)⁻¹) ≤ 3 := by
    change X ^ (2 * (100 * Real.log X)⁻¹) ≤ 3
    rw [Real.rpow_def_of_pos (by linarith : 0 < X)]
    have harg : Real.log X * (2 * (100 * Real.log X)⁻¹) ≤ 1 := by
      field_simp
      norm_num
    exact (Real.exp_le_exp.mpr harg).trans Real.exp_one_lt_three.le
  calc
    Real.rpow ((d : ℝ) * T) (-2 * (sigma + 1 / 4)) =
        Real.rpow X (-2 * (sigma + 1 / 4)) := rfl
    _ ≤ Real.rpow X (-3 / 2 + 2 * (100 * Real.log X)⁻¹) := hrpowexp
    _ = Real.rpow X (-3 / 2) * Real.rpow X (2 * (100 * Real.log X)⁻¹) := by
      exact Real.rpow_add (by linarith : 0 < X) _ _
    _ ≤ Real.rpow X (-3 / 2) * 3 := by
      exact mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg (by linarith) _)
    _ = 3 * Real.rpow ((d : ℝ) * T) (-3 / 2) := by rw [mul_comm]

/-- The exact long-contour cutoff majorant has source size
`O(sqrt(X) log(X)^2)`; this squared form is what the family moment consumes. -/
theorem longSourceCutoffMajorant_sq_le_log200
    (q d : ℕ) [NeZero q] [NeZero d] {T sigma : ℝ}
    (hdq : d ∣ q) (hT : 3 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹)
    (hrange : d ≠ 1 ∨ 9 ≤ T) :
    longSourceCutoffMajorant d ((d : ℝ) * T) T sigma ^ 2 ≤
      longSourceMomentConstant * ((d : ℝ) * T) *
        Real.log ((d : ℝ) * T) ^ 200 := by
  let X : ℝ := (d : ℝ) * T
  let W : ℝ := ∫ v : ℝ, longGammaWeightEnvelope v
  let F : ℝ := longFunctionalMomentConstant
  let Q : ℝ := Real.sqrt (8 + 8 * Real.pi)
  let D : ℝ := longDyadicTailMass
  let L : ℝ := Real.log X
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  have hTpos : 0 < T := by linarith
  have hX : 6 ≤ X := by
    rcases hrange with hd | hT9
    · have hdpos : 0 < d := NeZero.pos d
      have hd2 : 2 ≤ d := by omega
      dsimp [X]
      have hd2r : (2 : ℝ) ≤ d := by exact_mod_cast hd2
      nlinarith
    · dsimp [X]
      nlinarith
  have hXpos : 0 < X := by linarith
  have hL1 : 1 ≤ L := by
    dsimp [L]
    exact (one_lt_log_of_three_le (by linarith : 3 ≤ X)).le
  have hW0 : 0 ≤ W := by
    dsimp [W]
    exact integral_nonneg fun v => by
      unfold longGammaWeightEnvelope
      positivity
  have hF0 : 0 ≤ F := by
    exact longFunctionalMomentConstant_nonneg
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  have hD0 : 0 ≤ D := longDyadicTailMass_nonneg
  have hgamma :
      (∫ v : ℝ, RamachandraGammaWeightIntegrability.gammaPolynomialWeight
        (-(sigma + 1 / 4)) v) ≤ W := by
    simpa [W] using integral_gammaPolynomialWeight_long_le_uniformMass hT hstrip
  have hrpow := source_rpow_shift_absorption q d hdq hT hstrip
  have hTone : 1 + T ≤ 2 * T := by linarith
  have hTcube : (1 + T) ^ 3 ≤ (2 * T) ^ 3 := by
    exact pow_le_pow_left₀ (by positivity) hTone 3
  have hscale :
      F * (d : ℝ) ^ 3 * Real.rpow X (-2 * (sigma + 1 / 4)) *
          (1 + T) ^ 3 ≤
        24 * (F + 1) * Real.rpow X (3 / 2) := by
    have hcube : (d : ℝ) ^ 3 * T ^ 3 = X ^ 3 := by
      dsimp [X]
      ring
    have hpow : X ^ 3 * Real.rpow X (-3 / 2) =
        Real.rpow X (3 / 2) := by
      calc
        X ^ 3 * Real.rpow X (-3 / 2) =
            Real.rpow X (3 : ℝ) * Real.rpow X (-3 / 2) := by
          congr 1
          exact (Real.rpow_natCast X 3).symm
        _ = Real.rpow X ((3 : ℝ) + (-3 / 2)) :=
          (Real.rpow_add hXpos _ _).symm
        _ = Real.rpow X (3 / 2) := by norm_num
    calc
      F * (d : ℝ) ^ 3 * Real.rpow X (-2 * (sigma + 1 / 4)) *
          (1 + T) ^ 3 ≤
          (F + 1) * (d : ℝ) ^ 3 *
            Real.rpow X (-2 * (sigma + 1 / 4)) * (1 + T) ^ 3 := by
        gcongr
        all_goals first | linarith | exact Real.rpow_nonneg hXpos.le _
      _ ≤ (F + 1) * (d : ℝ) ^ 3 *
            (3 * Real.rpow X (-3 / 2)) * (1 + T) ^ 3 := by
        gcongr
      _ ≤ (F + 1) * (d : ℝ) ^ 3 *
            (3 * Real.rpow X (-3 / 2)) * (2 * T) ^ 3 := by
        exact mul_le_mul_of_nonneg_left hTcube <| by
          exact mul_nonneg
            (mul_nonneg (by linarith) (by positivity))
            (mul_nonneg (by norm_num) (Real.rpow_nonneg hXpos.le _))
      _ = 24 * (F + 1) *
          ((d : ℝ) ^ 3 * T ^ 3 * Real.rpow X (-3 / 2)) := by ring
      _ = 24 * (F + 1) * Real.rpow X (3 / 2) := by
        rw [hcube, hpow]
  have hcutoff :
      Q * ((longDyadicCutoff X : ℝ) + 2) ^ 2 *
          (Real.rpow 2 (-(1 / 4 : ℝ))) ^ longDyadicCutoff X * D ≤
        64 * (Q + 1) * (D + 1) * L ^ 2 * Real.rpow X (-1 / 4) := by
    have hquad := cutoff_quadratic_le_sixteen_log_sq (by linarith : 3 ≤ X)
    have hgeom := cutoff_geometric_le_four_mul_rpow (by linarith : 3 ≤ X)
    have hgeom' :
        (Real.rpow 2 (-(1 / 4 : ℝ))) ^ longDyadicCutoff X ≤
          4 * Real.rpow X (-1 / 4) := by
      convert hgeom using 1 <;> ring
    calc
      Q * ((longDyadicCutoff X : ℝ) + 2) ^ 2 *
          (Real.rpow 2 (-(1 / 4 : ℝ))) ^ longDyadicCutoff X * D ≤
          (Q + 1) * ((longDyadicCutoff X : ℝ) + 2) ^ 2 *
            (Real.rpow 2 (-(1 / 4 : ℝ))) ^ longDyadicCutoff X * D := by
        gcongr
        all_goals first | linarith |
          exact pow_nonneg (Real.rpow_nonneg (by norm_num) _) _
      _ ≤ (Q + 1) * (16 * L ^ 2) *
            (Real.rpow 2 (-(1 / 4 : ℝ))) ^ longDyadicCutoff X * D := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hquad
              (add_nonneg hQ0 (by norm_num)))
            (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)) hD0
      _ ≤ (Q + 1) * (16 * L ^ 2) *
            (4 * Real.rpow X (-1 / 4)) * D := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hgeom' <| by
            exact mul_nonneg (add_nonneg hQ0 (by norm_num)) (by positivity)) hD0
      _ ≤ (Q + 1) * (16 * L ^ 2) *
            (4 * Real.rpow X (-1 / 4)) * (D + 1) := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        exact mul_nonneg
          (mul_nonneg (by linarith) (by positivity))
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hXpos.le _))
      _ = 64 * (Q + 1) * (D + 1) * L ^ 2 *
          Real.rpow X (-1 / 4) := by ring
  let B : ℝ := F * (d : ℝ) ^ 3 *
    Real.rpow X (-2 * (sigma + 1 / 4)) * (1 + T) ^ 3
  let B' : ℝ := 24 * (F + 1) * Real.rpow X (3 / 2)
  let E : ℝ := Q * ((longDyadicCutoff X : ℝ) + 2) ^ 2 *
    (Real.rpow 2 (-(1 / 4 : ℝ))) ^ longDyadicCutoff X * D
  let E' : ℝ := 64 * (Q + 1) * (D + 1) * L ^ 2 *
    Real.rpow X (-1 / 4)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB'0 : 0 ≤ B' := by dsimp [B']; positivity
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hE'0 : 0 ≤ E' := by dsimp [E']; positivity
  have hmajor : longSourceCutoffMajorant d X T sigma ≤
      (W + 1) * Real.sqrt B' * E' := by
    unfold longSourceCutoffMajorant
    change
      (∫ v : ℝ, RamachandraGammaWeightIntegrability.gammaPolynomialWeight
          (-(sigma + 1 / 4)) v) * Real.sqrt B * E ≤ _
    have hW : (∫ v : ℝ,
        RamachandraGammaWeightIntegrability.gammaPolynomialWeight
          (-(sigma + 1 / 4)) v) ≤ W + 1 := hgamma.trans (by linarith)
    have hsqrt : Real.sqrt B ≤ Real.sqrt B' :=
      Real.sqrt_le_sqrt (by simpa [B, B'] using hscale)
    have hE : E ≤ E' := by simpa [E, E'] using hcutoff
    gcongr
  have hcombine : Real.rpow X (3 / 2) *
      Real.rpow X (-1 / 4) ^ 2 = X := by
    have hsquare : Real.rpow X (-1 / 4) ^ 2 =
        Real.rpow X (-1 / 2) := by
      calc
        Real.rpow X (-1 / 4) ^ 2 =
            Real.rpow (Real.rpow X (-1 / 4)) (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = Real.rpow X ((-1 / 4 : ℝ) * 2) :=
          (Real.rpow_mul hXpos.le _ _).symm
        _ = Real.rpow X (-1 / 2) := by norm_num
    rw [hsquare]
    calc
      Real.rpow X (3 / 2) * Real.rpow X (-1 / 2) =
          Real.rpow X ((3 / 2 : ℝ) + (-1 / 2)) :=
        (Real.rpow_add hXpos _ _).symm
      _ = X := by norm_num [Real.rpow_one]
  have hsquared := pow_le_pow_left₀
    (longSourceCutoffMajorant_nonneg d X T sigma) hmajor 2
  have hlogpow : L ^ 4 ≤ L ^ 200 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  calc
    longSourceCutoffMajorant d ((d : ℝ) * T) T sigma ^ 2 =
        longSourceCutoffMajorant d X T sigma ^ 2 := rfl
    _ ≤ ((W + 1) * Real.sqrt B' * E') ^ 2 := hsquared
    _ = (W + 1) ^ 2 * B' * E' ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hB'0]
    _ = 98304 * (W + 1) ^ 2 * (F + 1) * (Q + 1) ^ 2 *
        (D + 1) ^ 2 * L ^ 4 * X := by
      dsimp [B', E']
      simp only [mul_pow]
      calc
        (W + 1) ^ 2 * (24 * (F + 1) * Real.rpow X (3 / 2)) *
            (64 ^ 2 * (Q + 1) ^ 2 * (D + 1) ^ 2 *
              (L ^ 2) ^ 2 * Real.rpow X (-1 / 4) ^ 2) =
            98304 * (W + 1) ^ 2 * (F + 1) * (Q + 1) ^ 2 *
              (D + 1) ^ 2 * L ^ 4 *
                (Real.rpow X (3 / 2) * Real.rpow X (-1 / 4) ^ 2) := by ring
        _ = _ := by rw [hcombine]
    _ ≤ 100000 * (W + 1) ^ 2 * (F + 1) * (Q + 1) ^ 2 *
        (D + 1) ^ 2 * L ^ 200 * X := by
      gcongr <;> norm_num
    _ = longSourceMomentConstant * ((d : ℝ) * T) *
          Real.log ((d : ℝ) * T) ^ 200 := by
      dsimp [longSourceMomentConstant, W, F, Q, D, L, X]
      ring

/-- Premise-free source-range moment package for the literal long contour. -/
noncomputable def primitiveShiftedLongSourceMomentPackage :
    PrimitiveShiftedSourceMomentPackage primitiveFamilyLongContourSecondMoment := by
  refine ⟨longSourceMomentConstant, longSourceMomentConstant_pos, ?_⟩
  intro q d _ _ T sigma hdq hT hstrip hrange
  obtain ⟨hbetaLo, hbetaHi⟩ := longBeta_mem_uniformInterval hT hstrip
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  have hX3 : 3 ≤ (d : ℝ) * T := by nlinarith
  exact (primitiveFamilyLongContourSecondMoment_le_cutoffMajorant_sq d rfl
    hX3
    (by linarith) (by linarith) (by linarith)).trans
      (longSourceCutoffMajorant_sq_le_log200 q d hdq hT hstrip hrange)

/-- Premise-free continuity package for the literal normalized long contour. -/
theorem primitiveShiftedLongSourcePieceContinuity :
    PrimitiveShiftedSourcePieceContinuity
      (fun psi T sigma t => primitiveShiftedLongContour psi T sigma t) := by
  intro q d _ _ T sigma hdq hT hstrip hrange psi
  obtain ⟨hbetaLo, hbetaHi⟩ := longBeta_mem_uniformInterval hT hstrip
  exact continuous_primitiveShiftedLongContour_sq psi (by linarith)
    (by linarith) (by linarith)

end
end RamachandraLongContourSourcePackage

#print axioms RamachandraLongContourSourcePackage.longSourceCutoffMajorant_sq_le_log200
#print axioms RamachandraLongContourSourcePackage.primitiveShiftedLongSourceMomentPackage
#print axioms RamachandraLongContourSourcePackage.primitiveShiftedLongSourcePieceContinuity
