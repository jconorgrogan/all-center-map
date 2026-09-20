import PrimitiveLFixedStripGrowthCertified
import PrimitiveLFixedStripGrowth

/-!
# Premise-free fixed-strip growth connector for Appendices A.4 and A.5

The Phragmén--Lindelöf module proves more than the narrow A.4 interface asks
for: its estimate holds on `-1 ≤ re s ≤ 2`.  This file exports that theorem at
the A.4 interface and spends the stronger strip directly on the explicit
Jensen circle used by A.5.
-/

open Complex Real Set Metric
open scoped Real

namespace MAPAppendixA45GrowthConnector

noncomputable section

/-- The formerly open fixed-strip premise in Appendix A.4. -/
theorem certifiedPrimitiveLPolynomialStripGrowth :
    MAPAppendixA4Detector.PrimitiveLPolynomialStripGrowth :=
  PLInteriorGrowth.primitiveLPolynomialStripGrowth

variable {q : ℕ} [NeZero q]

private theorem abs_im_le_abs_t_add_three {t : ℝ} {z : ℂ}
    (hz : z ∈ sphere (MAPLocalZeroWindow.jensenCenter t)
      |MAPLocalZeroWindow.jensenOuterRadius|) :
    |z.im| ≤ |t| + 3 := by
  have hdist : dist z (MAPLocalZeroWindow.jensenCenter t) = 17 / 10 := by
    rw [mem_sphere] at hz
    norm_num [MAPLocalZeroWindow.jensenOuterRadius] at hz
    exact hz
  have himdiff : |z.im - (t + 1 / 2)| ≤ 17 / 10 := by
    calc
      |z.im - (t + 1 / 2)| = |(z - MAPLocalZeroWindow.jensenCenter t).im| := by
        simp [MAPLocalZeroWindow.jensenCenter]
      _ ≤ ‖z - MAPLocalZeroWindow.jensenCenter t‖ :=
        Complex.abs_im_le_norm _
      _ = 17 / 10 := by simpa [dist_eq_norm] using hdist
  calc
    |z.im| = |(z.im - (t + 1 / 2)) + (t + 1 / 2)| := by ring_nf
    _ ≤ |z.im - (t + 1 / 2)| + |t + 1 / 2| := abs_add_le _ _
    _ ≤ 17 / 10 + (|t| + 1 / 2) := by
      gcongr
      calc
        |t + 1 / 2| ≤ |t| + |(1 / 2 : ℝ)| := abs_add_le _ _
        _ = |t| + 1 / 2 := by norm_num
    _ ≤ |t| + 3 := by linarith

/-- The certified PL estimate supplies the exact left-arc polynomial bound
needed by the Jensen implementation of Appendix A.5. -/
theorem regularizedLFunction_leftArc_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {t : ℝ} {z : ℂ}
    (hz : z ∈ sphere (MAPLocalZeroWindow.jensenCenter t)
      |MAPLocalZeroWindow.jensenOuterRadius|)
    (hzre : z.re < 2) :
    ‖DirichletZeros.regularizedLFunction χ z‖ ≤
      3200 * (MAPLocalZeroWindow.arithmeticScale q t) ^ (2 : ℝ) := by
  have hzrange := MAPPrimitiveLFixedStrip.jensenOuterCircle_re_mem hz
  have hL := PLInteriorGrowth.norm_LFunction_fixedStrip_le χ hχ
    (by linarith [hzrange.1]) hzre.le
  have hreadd : |(z + 3).re| ≤ 5 := by
    rw [abs_of_nonneg]
    · simp
      linarith [hzrange.1]
    · simp
      linarith [hzrange.1]
  have him : |(z + 3).im| ≤ |t| + 3 := by
    simpa using abs_im_le_abs_t_add_three hz
  have hshift : ‖z + 3‖ ≤ 4 * (|t| + 2) := by
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 5 + (|t| + 3) := add_le_add hreadd him
      _ ≤ 4 * (|t| + 2) := by nlinarith [abs_nonneg t]
  have hscale :
      MAPLocalZeroWindow.arithmeticScale q t = (q : ℝ) * (|t| + 2) := by
    rfl
  rw [DirichletZeros.regularizedLFunction, if_neg hχ]
  rw [Real.rpow_two]
  calc
    ‖DirichletCharacter.LFunction χ z‖ ≤
        200 * (q : ℝ) ^ 2 * ‖z + 3‖ ^ 2 := hL
    _ ≤ 200 * (q : ℝ) ^ 2 * (4 * (|t| + 2)) ^ 2 := by
      gcongr
    _ = 3200 * ((q : ℝ) * (|t| + 2)) ^ 2 := by ring
    _ = 3200 * (MAPLocalZeroWindow.arithmeticScale q t) ^ 2 := by
      rw [hscale]

/-- Premise-free multiplicity-aware A.5 unit-window estimate.  The constants
are intentionally coarse; the load-bearing fact is uniform logarithmic growth
in the conductor-height scale. -/
theorem certifiedAppendixA5LocalZeroCount
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ t : ℝ}
    (hσ : 1 / 2 ≤ σ) :
    (MAPLocalZeroWindow.closedUnitWindowCount χ σ t : ℝ) ≤
      (Real.log 3 + Real.log 3200 +
          2 * Real.log (MAPLocalZeroWindow.arithmeticScale q t)) /
        Real.log (MAPLocalZeroWindow.jensenOuterRadius /
          MAPLocalZeroWindow.jensenInnerRadius) := by
  exact MAPPrimitiveLFixedStrip.closedUnitWindowCount_le_of_leftArc_polynomial_growth
    χ hχ hσ (by norm_num) (by norm_num)
    (fun z hz hzre => regularizedLFunction_leftArc_le χ hχ hz hzre)

end

end MAPAppendixA45GrowthConnector

#print axioms MAPAppendixA45GrowthConnector.certifiedPrimitiveLPolynomialStripGrowth
#print axioms MAPAppendixA45GrowthConnector.certifiedAppendixA5LocalZeroCount
