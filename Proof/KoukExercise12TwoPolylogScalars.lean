import KoukExercise12TwoPointwiseZeroSplit
import APLowRangeGlobal
import WeakVKNearDecay

/-!
# Polylogarithmic scalar bounds for Koukoulopoulos, Exercise 12.2(a)

These estimates contain no zero-free input.  They bound the selected contour's
finite divisor count and aperture cost on the polylogarithmic conductor and
height range used by Siegel--Walfisz.
-/

namespace MAPKoukExercise12TwoPolylogScalars

open Set Filter Asymptotics
open DirichletZeros MAPKoukExercise12TwoContourAperture
open MAPKoukExercise12TwoZeroSum

noncomputable section

/-- A deliberately coarse polynomial envelope for the full zero divisor at
the buffered Exercise 12.2(a) height. -/
theorem dirichletZeroCount_polylogHeight_le
    (B D : ℕ) {X : ℝ} (hlog : 2 ≤ Real.log X)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive)
    (hq : (q : ℝ) ≤ (Real.log X) ^ B) :
    (dirichletZeroCount chi 0 ((Real.log X) ^ D + 4) : ℝ) ≤
      5000000 * (Real.log X) ^ (B + 3 * D) := by
  let L := Real.log X
  let H := L ^ D
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hH1 : 1 ≤ H := by
    dsimp [H]
    exact one_le_pow₀ hL1
  have hT0 : 0 ≤ H + 4 := by linarith
  have hrow := MAPAPLowRangeGlobal.dirichletZeroCount_le_uniformRow
    chi hprim hT0
  have hfirst : 1 + 2 * (H + 4) ≤ 11 * H := by nlinarith
  have hscale : (q : ℝ) * ((H + 4) + 4) ≤
      9 * L ^ (B + D) := by
    calc
      (q : ℝ) * ((H + 4) + 4) ≤ L ^ B * (9 * H) := by
        apply mul_le_mul hq (by nlinarith) (by positivity) (pow_nonneg hL0 B)
      _ = 9 * L ^ (B + D) := by
        dsimp [H]
        rw [pow_add]
        ring
  have hscalePos : 0 < (q : ℝ) * ((H + 4) + 4) := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    positivity
  have hlogScale : Real.log ((q : ℝ) * ((H + 4) + 4)) ≤
      9 * L ^ (B + D) := by
    exact (Real.log_le_sub_one_of_pos hscalePos).trans (by linarith)
  have hpowBD1 : 1 ≤ L ^ (B + D) := one_le_pow₀ hL1
  have hmiddle :
      2 * (1 + 1989 * Real.log ((q : ℝ) * ((H + 4) + 4))) ≤
        35804 * L ^ (B + D) := by
    calc
      _ ≤ 2 * (1 + 1989 * (9 * L ^ (B + D))) := by gcongr
      _ ≤ 35804 * L ^ (B + D) := by nlinarith
  have hnPos : (0 : ℝ) < (⌊2 * (H + 4)⌋₊ + 1 : ℕ) := by positivity
  have hharmNat :
      ((harmonic (⌊2 * (H + 4)⌋₊ + 1) : ℚ) : ℝ) ≤
        (⌊2 * (H + 4)⌋₊ + 1 : ℕ) := by
    have hh := harmonic_le_one_add_log (⌊2 * (H + 4)⌋₊ + 1)
    have hl := Real.log_le_sub_one_of_pos hnPos
    exact hh.trans (by linarith)
  have hfloor : ((⌊2 * (H + 4)⌋₊ + 1 : ℕ) : ℝ) ≤ 11 * H := by
    have hf := Nat.floor_le (show 0 ≤ 2 * (H + 4) by positivity)
    push_cast
    nlinarith
  have hharm :
      ((harmonic (⌊2 * (H + 4)⌋₊ + 1) : ℚ) : ℝ) ≤ 11 * H :=
    hharmNat.trans hfloor
  have hharm0 :
      0 ≤ ((harmonic (⌊2 * (H + 4)⌋₊ + 1) : ℚ) : ℝ) := by
    norm_cast
    unfold harmonic
    positivity
  have hmiddle0 :
      0 ≤ 2 * (1 + 1989 * Real.log ((q : ℝ) * ((H + 4) + 4))) := by
    have hscaleOne : 1 ≤ (q : ℝ) * ((H + 4) + 4) := by
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
      nlinarith
    have := Real.log_nonneg hscaleOne
    positivity
  calc
    (dirichletZeroCount chi 0 ((Real.log X) ^ D + 4) : ℝ) ≤
        (1 + 2 * (H + 4)) *
          (2 * (1 + 1989 * Real.log ((q : ℝ) * ((H + 4) + 4))) *
            ((harmonic (⌊2 * (H + 4)⌋₊ + 1) : ℚ) : ℝ)) := by
      simpa only [L, H] using hrow
    _ ≤ (11 * H) *
          (2 * (1 + 1989 * Real.log ((q : ℝ) * ((H + 4) + 4))) *
            ((harmonic (⌊2 * (H + 4)⌋₊ + 1) : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hfirst (mul_nonneg hmiddle0 hharm0)
    _ ≤ (11 * H) * ((35804 * L ^ (B + D)) * (11 * H)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hmiddle hharm hharm0 (by positivity)
    _ = (11 * 35804 * 11) * L ^ (B + 3 * D) := by
      dsimp [H]
      rw [pow_add, pow_add, pow_mul]
      ring
    _ ≤ 5000000 * L ^ (B + 3 * D) := by
      gcongr
      norm_num
    _ = 5000000 * (Real.log X) ^ (B + 3 * D) := by rfl

/-- The aperture and every selected real part have only a fixed polylogarithmic
reciprocal cost. -/
theorem inv_exerciseContourClearance_polylogHeight_le
    (B D : ℕ) {X : ℝ} (hlog : 2 ≤ Real.log X)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive)
    (hq : (q : ℝ) ≤ (Real.log X) ^ B) :
    (exerciseContourClearance chi ((Real.log X) ^ D))⁻¹ ≤
      80000016 * (Real.log X) ^ (B + 3 * D) := by
  have hcount := dirichletZeroCount_polylogHeight_le B D hlog chi hprim hq
  have hinv := inv_exerciseContourClearance_le_count chi ((Real.log X) ^ D)
  have hpow : 1 ≤ (Real.log X) ^ (B + 3 * D) :=
    one_le_pow₀ (by linarith : 1 ≤ Real.log X)
  calc
    _ ≤ 16 * ((dirichletZeroCount chi 0 ((Real.log X) ^ D + 4) : ℝ) + 1) := hinv
    _ ≤ 16 * (5000000 * (Real.log X) ^ (B + 3 * D) + 1) := by gcongr
    _ ≤ 80000016 * (Real.log X) ^ (B + 3 * D) := by nlinarith

private theorem eventually_loglog_le_quarter_log_rpow :
    ∀ᶠ X : ℝ in atTop,
      Real.log (Real.log X) ≤
        Real.rpow (Real.log X) (1 / 4 : ℝ) := by
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 4)).eventuallyLE
  exact Real.tendsto_log_atTop.eventually (by
    filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with L hL hL1
    have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1.le
    have hrpow0 : 0 ≤ Real.rpow L (1 / 4 : ℝ) :=
      Real.rpow_nonneg (zero_lt_one.trans hL1).le _
    have hL' : Real.log L ≤ |Real.rpow L (1 / 4 : ℝ)| := by
      simpa [Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg hlog0] using hL
    rwa [abs_of_nonneg hrpow0] at hL')

/-- At a polylogarithmic selected height, the regular Theorem 12.3 gap is
already a weak-VK gap of exponent `1/4`. -/
theorem eventually_weakGap_le_exercise12TwoGap (B D : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (T : ℝ),
      (q : ℝ) ≤ (Real.log X) ^ B →
      T ∈ Set.Ioo ((Real.log X) ^ D) ((Real.log X) ^ D + 1) →
      (1 / (100000000000 * ((B + D : ℕ) + Real.log 4))) *
          Real.rpow (Real.log X) (-(1 / 4 : ℝ)) ≤
        exercise12TwoGap q T := by
  filter_upwards [eventually_loglog_le_quarter_log_rpow,
      eventually_gt_atTop (Real.exp (Real.exp 1))] with
      X hquarter hX q _inst T hq hT
  let L := Real.log X
  let H := L ^ D
  let C := ((B + D : ℕ) : ℝ) + Real.log 4
  have hXpos : 0 < X := (Real.exp_pos _).trans hX
  have hlogXexp : Real.exp 1 < L := by
    dsimp [L]
    rw [Real.lt_log_iff_exp_lt hXpos]
    exact hX
  have hL1 : 1 < L :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).trans hlogXexp
  have hlogL1 : 1 < Real.log L := by
    rw [Real.lt_log_iff_exp_lt (zero_lt_one.trans hL1)]
    exact hlogXexp
  have hH1 : 1 ≤ H := by
    dsimp [H]
    exact one_le_pow₀ hL1.le
  have hT0 : 0 ≤ T := by linarith [hT.1]
  have hscalePos : 0 < (q : ℝ) * (T + 2) := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    positivity
  have hscale : (q : ℝ) * (T + 2) ≤ 4 * L ^ (B + D) := by
    have hqL : (q : ℝ) ≤ L ^ B := by simpa only [L] using hq
    calc
      (q : ℝ) * (T + 2) ≤ L ^ B * (4 * H) := by
        apply mul_le_mul hqL (by linarith [hT.2]) (by positivity)
          (pow_nonneg (zero_le_one.trans hL1.le) B)
      _ = 4 * L ^ (B + D) := by
        dsimp [H]
        rw [pow_add]
        ring
  have hlogScale : Real.log ((q : ℝ) * (T + 2)) ≤
      C * Real.log L := by
    calc
      Real.log ((q : ℝ) * (T + 2)) ≤
          Real.log (4 * L ^ (B + D)) :=
        Real.log_le_log hscalePos hscale
      _ = Real.log 4 + ((B + D : ℕ) : ℝ) * Real.log L := by
        rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
          (pow_pos (zero_lt_one.trans hL1) _).ne', Real.log_pow]
      _ ≤ C * Real.log L := by
        dsimp [C]
        have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        nlinarith
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hpowPos : 0 < Real.rpow L (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hL1) _
  have hdenUpper :
      100000000000 * Real.log ((q : ℝ) * (T + 2)) ≤
        100000000000 * C * Real.rpow L (1 / 4 : ℝ) := by
    calc
      _ ≤ 100000000000 * (C * Real.log L) :=
        mul_le_mul_of_nonneg_left hlogScale (by norm_num)
      _ ≤ 100000000000 * (C * Real.rpow L (1 / 4 : ℝ)) := by
        gcongr
      _ = _ := by ring
  have hdenPos : 0 < 100000000000 * Real.log ((q : ℝ) * (T + 2)) := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
    exact mul_pos (by norm_num) (Real.log_pos (by nlinarith [hT.1]))
  have hinv :
      1 / (100000000000 * C * Real.rpow L (1 / 4 : ℝ)) ≤
        exercise12TwoGap q T := by
    unfold exercise12TwoGap
    exact one_div_le_one_div_of_le hdenPos hdenUpper
  have hid :
      (1 / (100000000000 * C)) * Real.rpow L (-(1 / 4 : ℝ)) =
        1 / (100000000000 * C * Real.rpow L (1 / 4 : ℝ)) := by
    have hneg := Real.rpow_neg (zero_lt_one.trans hL1).le (1 / 4 : ℝ)
    calc
      (1 / (100000000000 * C)) * Real.rpow L (-(1 / 4 : ℝ)) =
          (1 / (100000000000 * C)) *
            (Real.rpow L (1 / 4 : ℝ))⁻¹ :=
        congrArg (fun z : ℝ => (1 / (100000000000 * C)) * z) hneg
      _ = _ := by field_simp
  change (1 / (100000000000 * C)) * Real.rpow L (-(1 / 4 : ℝ)) ≤ _
  rw [hid]
  exact hinv

#print axioms MAPKoukExercise12TwoPolylogScalars.dirichletZeroCount_polylogHeight_le
#print axioms MAPKoukExercise12TwoPolylogScalars.inv_exerciseContourClearance_polylogHeight_le
#print axioms MAPKoukExercise12TwoPolylogScalars.eventually_weakGap_le_exercise12TwoGap

end

end MAPKoukExercise12TwoPolylogScalars
