import Mathlib

/-!
# Certified arithmetic for a polylog-conductor zero-density route

Everything in this file is elementary. No zero-density statement is declared
or assumed. The constants are the literal constants used at the `2/15`
short-interval threshold.
-/

namespace ZeroDensityArithmetic

open Filter Asymptotics

noncomputable section

/-- Guth--Maynard's zero-density coefficient. -/
def gmCoeff (σ : ℝ) : ℝ := 15 / (3 + 5 * σ)

/-- Ingham's classical zero-density coefficient. -/
def inghamCoeff (σ : ℝ) : ℝ := 3 / (2 - σ)

/-- The uniform coefficient obtained by switching at `σ = 7/10`. -/
def uniformCoeff : ℝ := 30 / 13

/-- The height exponent used at the `2/15 + ε` short-interval threshold. -/
def heightExponent (ε : ℝ) : ℝ := 13 / 15 - ε / 2

/-- The exact exponent reserve after the uniform `30/13` density bound. -/
def densityReserve (ε : ℝ) : ℝ :=
  2 - uniformCoeff * heightExponent ε

/-- A mesh width small enough for both the low-zero and compact-density ranges. -/
def meshWidth (ε : ℝ) : ℝ :=
  min ((1 - heightExponent ε) / 8) (densityReserve ε / 100)

/-- Ingham is at most `30/13` on the range where it is used. -/
theorem inghamCoeff_le_uniform {σ : ℝ}
    (_hσlow : 1 / 2 ≤ σ) (hσhigh : σ ≤ 7 / 10) :
    inghamCoeff σ ≤ uniformCoeff := by
  unfold inghamCoeff uniformCoeff
  have hden : 0 < 2 - σ := by linarith
  apply (div_le_iff₀ hden).2
  linarith

/-- Guth--Maynard is at most `30/13` from the switching point onward. -/
theorem gmCoeff_le_uniform {σ : ℝ}
    (hσlow : 7 / 10 ≤ σ) (_hσhigh : σ ≤ 4 / 5) :
    gmCoeff σ ≤ uniformCoeff := by
  unfold gmCoeff uniformCoeff
  have hden : 0 < 3 + 5 * σ := by linarith
  apply (div_le_iff₀ hden).2
  linarith

/-- Both estimates meet exactly at the optimizer `σ = 7/10`. -/
theorem optimizer_equalities :
    inghamCoeff (7 / 10 : ℝ) = uniformCoeff ∧
      gmCoeff (7 / 10 : ℝ) = uniformCoeff := by
  constructor <;> norm_num [inghamCoeff, gmCoeff, uniformCoeff]

/-- The `2/15` threshold leaves exactly `(15/13) ε`. -/
theorem densityReserve_eq (ε : ℝ) :
    densityReserve ε = (15 / 13) * ε := by
  unfold densityReserve uniformCoeff heightExponent
  ring

/-- The height exponent is below one for every positive `ε`. -/
theorem heightExponent_lt_one {ε : ℝ} (hε : 0 < ε) :
    heightExponent ε < 1 := by
  unfold heightExponent
  linarith

/-- The compact-density reserve is strictly positive. -/
theorem densityReserve_pos {ε : ℝ} (hε : 0 < ε) :
    0 < densityReserve ε := by
  rw [densityReserve_eq]
  positivity

/-- The chosen mesh width is positive. -/
theorem meshWidth_pos {ε : ℝ} (hε : 0 < ε) :
    0 < meshWidth ε := by
  unfold meshWidth
  exact lt_min
    (div_pos (sub_pos.mpr (heightExponent_lt_one hε)) (by norm_num))
    (div_pos (densityReserve_pos hε) (by norm_num))

theorem meshWidth_le_lowReserve (ε : ℝ) :
    meshWidth ε ≤ (1 - heightExponent ε) / 8 := by
  exact min_le_left _ _

theorem meshWidth_le_densityReserve (ε : ℝ) :
    meshWidth ε ≤ densityReserve ε / 100 := by
  exact min_le_right _ _

/-- The low-zero range has a fixed negative power of `X`. -/
theorem lowRangeExponent_bound {ε δ : ℝ}
    (_hε : 0 < ε) (_hδ : 0 ≤ δ)
    (hδlow : δ ≤ (1 - heightExponent ε) / 8) :
    heightExponent ε - 1 + 2 * δ ≤
      -(3 / 4) * (1 - heightExponent ε) := by
  linarith

/-- Literal exponent bound for one compact mesh cell.

The term `densityReserve ε / 100` is the allotted `T^o(1)`/polylog
absorption. The output `17/100` reserve is the exact paper calculation.
-/
theorem compactMeshExponent_bound {ε δ σ : ℝ}
    (hε : 0 < ε) (_hδ : 0 ≤ δ)
    (hδden : δ ≤ densityReserve ε / 100)
    (hσ : σ ≤ 4 / 5) :
    2 * (σ + δ - 1) +
        uniformCoeff * heightExponent ε * (1 - σ) +
        densityReserve ε / 100 ≤
      -(17 / 100) * densityReserve ε := by
  have hd : 0 < densityReserve ε := densityReserve_pos hε
  have hone : 1 / 5 ≤ 1 - σ := by linarith
  have hid : uniformCoeff * heightExponent ε = 2 - densityReserve ε := by
    unfold densityReserve
    ring
  rw [hid]
  nlinarith

/-- The near-one exponent retains the advertised `1/6` gap once the polylog
conductor contributes at most `1/315` to `log(qT)/log X`. -/
theorem nearOneExponent_bound {ε u : ℝ}
    (hε : 0 ≤ ε) (_hu0 : 0 ≤ u) (hu : u ≤ 1 / 315) :
    1 / 6 ≤ 2 - (21 / 10) * (heightExponent ε + u) := by
  unfold heightExponent
  linarith

/-- Every fixed real power of `log X` is eventually dominated by `X^η`. -/
theorem polylog_absorption (K η : ℝ) (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop,
      Real.rpow (Real.log X) K ≤ Real.rpow X η := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop K hη).eventuallyLE
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with X hX hXone
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hXone
  have hXnonneg : 0 ≤ X := zero_le_one.trans hXone
  simpa [Real.norm_of_nonneg (Real.rpow_nonneg hlog K),
    Real.norm_of_nonneg (Real.rpow_nonneg hXnonneg η)] using hX

/-- A finite family of fixed polylog losses can be absorbed simultaneously. -/
theorem finite_polylog_absorption (S : Finset ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop,
      ∀ K ∈ S, Real.rpow (Real.log X) K ≤ Real.rpow X η := by
  rw [Finset.eventually_all]
  intro K _hK
  exact polylog_absorption K η hη

end
end ZeroDensityArithmetic
