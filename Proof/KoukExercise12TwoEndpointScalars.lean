import APPerronEndpointUniformBound
import KoukExercise12TwoPolylogScalars

/-!
# Reusable endpoint scalar bounds for pointwise Exercise 12.2

These lemmas expose the deterministic inequalities needed by both the
principal and nonprincipal pointwise collapses.  They contain no zero-free or
explicit-formula input.
-/

namespace MAPKoukExercise12TwoEndpointScalars

open PrimitiveTruncatedExplicitFormulaBridge PaperEdgePrimitiveComponents

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

/-- Range of the half-integer Perron endpoint attached to `t ∈ [X,2X]`. -/
theorem halfIntegerPoint_floor_range
    {X t : ℝ} (hX : 2 ≤ X) (ht : t ∈ Set.Icc X (2 * X)) :
    1 ≤ ⌊t⌋₊ ∧
      X / 2 ≤ halfIntegerPoint ⌊t⌋₊ ∧
      halfIntegerPoint ⌊t⌋₊ ≤ 3 * X ∧
      (⌊t⌋₊ : ℝ) ≤ 2 * X := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hfloorLe : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
  have htFloor : t < (⌊t⌋₊ : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one t
  have hNpos : 0 < ⌊t⌋₊ := (Nat.floor_pos (R := ℝ)).2 (by
    linarith [ht.1] : (1 : ℝ) ≤ t)
  have hN : 1 ≤ ⌊t⌋₊ := by omega
  refine ⟨hN, ?_, ?_, ?_⟩
  · unfold halfIntegerPoint
    push_cast
    linarith [ht.1]
  · unfold halfIntegerPoint
    push_cast
    linarith [ht.2]
  · exact hfloorLe.trans ht.2

/-- Transfer a weak gap from the dyadic scale `X` to its half-integer Perron
endpoint, with a generous `1/12` reserve in the exponent. -/
theorem halfIntegerPoint_rpow_one_sub_le_weakFactor
    {X t omega : ℝ} (hX : 4 ≤ X) (ht : t ∈ Set.Icc X (2 * X))
    (homega : 0 ≤ omega) :
    Real.rpow (halfIntegerPoint ⌊t⌋₊) (1 - omega) ≤
      3 * X * Real.rpow X (-(omega / 12)) := by
  obtain ⟨hN, hxLower, hxUpper, -⟩ :=
    halfIntegerPoint_floor_range (by linarith) ht
  let x := halfIntegerPoint ⌊t⌋₊
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hxpos : 0 < x := by
    dsimp only [x]
    exact halfIntegerPoint_pos _
  have hsqrt : Real.sqrt X ≤ X / 2 := by
    have hsqrt0 := Real.sqrt_nonneg X
    nlinarith [Real.sq_sqrt hXpos.le]
  have hroot : Real.rpow X (1 / 12 : ℝ) ≤ x := by
    calc
      Real.rpow X (1 / 12 : ℝ) ≤ Real.rpow X (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXone (by norm_num)
      _ = Real.sqrt X := (Real.sqrt_eq_rpow X).symm
      _ ≤ X / 2 := hsqrt
      _ ≤ x := by simpa only [x] using hxLower
  have hneg :
      Real.rpow x (-omega) ≤ Real.rpow X (-(omega / 12)) := by
    calc
      Real.rpow x (-omega) ≤
          Real.rpow (Real.rpow X (1 / 12 : ℝ)) (-omega) :=
        Real.rpow_le_rpow_of_exponent_nonpos
          (Real.rpow_pos_of_pos hXpos _) hroot (by linarith)
      _ = Real.rpow X ((1 / 12 : ℝ) * (-omega)) :=
        (Real.rpow_mul hXpos.le (1 / 12 : ℝ) (-omega)).symm
      _ = Real.rpow X (-(omega / 12)) := by ring_nf
  have hsplit : Real.rpow x (1 - omega) = x * Real.rpow x (-omega) := by
    calc
      Real.rpow x (1 - omega) = Real.rpow x (1 + (-omega)) := by ring_nf
      _ = Real.rpow x 1 * Real.rpow x (-omega) :=
        Real.rpow_add hxpos 1 (-omega)
      _ = x * Real.rpow x (-omega) := by simp
  rw [hsplit]
  exact mul_le_mul hxUpper hneg (Real.rpow_nonneg hxpos.le _)
    (by positivity)

/-- The literal closed inside-Perron majorant has the same uniform scalar
bound as its underlying endpoint norm. -/
theorem insideMajorant_le
    {N : ℕ} {X T : ℝ} (hN : 1 ≤ N) (hNX : (N : ℝ) ≤ 5 * X)
    (hX : Real.exp 1 ≤ X) (hT : 0 < T) :
    insideMajorant N T ≤ 3000 * X * (Real.log X) ^ 2 / T := by
  obtain ⟨-, hlu, hlogN, -, -⟩ :=
    MAPAPPerronEndpointUniformBound.endpoint_scale_log_bounds hN hNX hX
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hL : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hX0).2 hX
  have hu1 : 1 < halfIntegerPoint N := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    unfold halfIntegerPoint
    linarith
  have hlu0 : 0 ≤ Real.log (halfIntegerPoint N) := (Real.log_pos hu1).le
  have hharm : ((harmonic N : ℚ) : ℝ) ≤ 7 * Real.log X := by
    calc
      ((harmonic N : ℚ) : ℝ) ≤ 1 + Real.log (N : ℝ) :=
        harmonic_le_one_add_log N
      _ ≤ 7 * Real.log X := by linarith
  have hharm0 : 0 ≤ ((harmonic N : ℚ) : ℝ) := by
    exact_mod_cast (harmonic_pos (by omega : N ≠ 0)).le
  have hfactor :
      3 * Real.exp 1 * halfIntegerPoint N *
          Real.log (halfIntegerPoint N) / (Real.pi * T) ≤
        3 * 3 * (6 * X) * (6 * Real.log X) / T := by
    have huX : halfIntegerPoint N ≤ 6 * X := by
      exact (MAPAPPerronEndpointUniformBound.endpoint_scale_log_bounds
        hN hNX hX).1
    have hnum :
        3 * Real.exp 1 * halfIntegerPoint N * Real.log (halfIntegerPoint N) ≤
          3 * 3 * (6 * X) * (6 * Real.log X) := by
      gcongr
      exact Real.exp_one_lt_three.le
    have hnum0 : 0 ≤ 3 * 3 * (6 * X) * (6 * Real.log X) := by positivity
    calc
      _ ≤ (3 * 3 * (6 * X) * (6 * Real.log X)) / (Real.pi * T) :=
        div_le_div_of_nonneg_right hnum (mul_pos Real.pi_pos hT).le
      _ ≤ (3 * 3 * (6 * X) * (6 * Real.log X)) / T :=
        div_le_div_of_nonneg_left hnum0 hT (by nlinarith [Real.pi_gt_three])
  unfold insideMajorant
  calc
    _ ≤ (3 * 3 * (6 * X) * (6 * Real.log X) / T) *
        (7 * Real.log X) :=
      mul_le_mul hfactor hharm hharm0 (by positivity)
    _ = 2268 * X * (Real.log X) ^ 2 / T := by ring
    _ ≤ 3000 * X * (Real.log X) ^ 2 / T := by gcongr <;> norm_num

/-- The literal closed outside-Perron majorant has the corresponding uniform
scalar bound. -/
theorem outsideMajorant_le
    {N : ℕ} {X T : ℝ} (hN : 1 ≤ N) (hNX : (N : ℝ) ≤ 5 * X)
    (hX : Real.exp 1 ≤ X) (hT : 0 < T) :
    outsideMajorant N T ≤ 9000 * X * (Real.log X) ^ 2 / T := by
  obtain ⟨huX, hlu, -, hlogNp1, hlogTwoN⟩ :=
    MAPAPPerronEndpointUniformBound.endpoint_scale_log_bounds hN hNX hX
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hL : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hX0).2 hX
  have hu1 : 1 < halfIntegerPoint N := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    unfold halfIntegerPoint
    linarith
  have hlu0 : 0 < Real.log (halfIntegerPoint N) := Real.log_pos hu1
  have hharm : ((harmonic (N + 1) : ℚ) : ℝ) ≤ 7 * Real.log X := by
    calc
      ((harmonic (N + 1) : ℚ) : ℝ) ≤ 1 + Real.log ((N + 1 : ℕ) : ℝ) :=
        harmonic_le_one_add_log (N + 1)
      _ = 1 + Real.log ((N : ℝ) + 1) := by norm_num
      _ ≤ 7 * Real.log X := by linarith
  have hharm0 : 0 ≤ ((harmonic (N + 1) : ℚ) : ℝ) := by
    exact_mod_cast (harmonic_pos (Nat.succ_ne_zero N)).le
  have hsecond :
      (4 / (Real.log (halfIntegerPoint N))⁻¹) *
          (1 + (((Real.log (halfIntegerPoint N))⁻¹ / 2)⁻¹)) ≤
        312 * (Real.log X) ^ 2 := by
    have heq :
        (4 / (Real.log (halfIntegerPoint N))⁻¹) *
            (1 + (((Real.log (halfIntegerPoint N))⁻¹ / 2)⁻¹)) =
          4 * Real.log (halfIntegerPoint N) *
            (1 + 2 * Real.log (halfIntegerPoint N)) := by
      field_simp [hlu0.ne']
    rw [heq]
    have hinner : 1 + 2 * Real.log (halfIntegerPoint N) ≤
        1 + 12 * Real.log X := by linarith
    calc
      _ ≤ 4 * (6 * Real.log X) * (1 + 12 * Real.log X) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hlu (by norm_num)) hinner
          (by positivity) (by positivity)
      _ ≤ 312 * (Real.log X) ^ 2 := by nlinarith
  have hbracket :
      2 * Real.log (2 * N + 1 : ℝ) * ((harmonic (N + 1) : ℚ) : ℝ) +
          (4 / (Real.log (halfIntegerPoint N))⁻¹) *
            (1 + (((Real.log (halfIntegerPoint N))⁻¹ / 2)⁻¹)) ≤
        480 * (Real.log X) ^ 2 := by
    have hfirst :
        2 * Real.log (2 * N + 1 : ℝ) * ((harmonic (N + 1) : ℚ) : ℝ) ≤
          2 * (12 * Real.log X) * (7 * Real.log X) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hlogTwoN (by norm_num)) hharm
        hharm0 (by positivity)
    calc
      _ ≤ 2 * (12 * Real.log X) * (7 * Real.log X) +
          312 * (Real.log X) ^ 2 := add_le_add hfirst hsecond
      _ = 480 * (Real.log X) ^ 2 := by ring
  have hfactor :
      Real.exp 1 * halfIntegerPoint N / (Real.pi * T) ≤ 3 * (6 * X) / T := by
    have hnum : Real.exp 1 * halfIntegerPoint N ≤ 3 * (6 * X) :=
      mul_le_mul Real.exp_one_lt_three.le huX (halfIntegerPoint_pos N).le
        (by norm_num)
    have hnum0 : 0 ≤ 3 * (6 * X) := by positivity
    calc
      _ ≤ (3 * (6 * X)) / (Real.pi * T) :=
        div_le_div_of_nonneg_right hnum (mul_pos Real.pi_pos hT).le
      _ ≤ (3 * (6 * X)) / T :=
        div_le_div_of_nonneg_left hnum0 hT (by nlinarith [Real.pi_gt_three])
  have hbracket0 : 0 ≤
      2 * Real.log (2 * N + 1 : ℝ) * ((harmonic (N + 1) : ℚ) : ℝ) +
          (4 / (Real.log (halfIntegerPoint N))⁻¹) *
            (1 + (((Real.log (halfIntegerPoint N))⁻¹ / 2)⁻¹)) := by
    have hlogTwoN0 : 0 ≤ Real.log (2 * N + 1 : ℝ) := by
      apply Real.log_nonneg
      push_cast
      have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    rw [show (4 / (Real.log (halfIntegerPoint N))⁻¹) *
          (1 + (((Real.log (halfIntegerPoint N))⁻¹ / 2)⁻¹)) =
        4 * Real.log (halfIntegerPoint N) *
          (1 + 2 * Real.log (halfIntegerPoint N)) by field_simp [hlu0.ne']]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hlogTwoN0) hharm0)
      (mul_nonneg (mul_nonneg (by norm_num) hlu0.le) (by linarith [hlu0]))
  unfold outsideMajorant
  calc
    _ ≤ (3 * (6 * X) / T) * (480 * (Real.log X) ^ 2) :=
      mul_le_mul hfactor hbracket hbracket0 (by positivity)
    _ = 8640 * X * (Real.log X) ^ 2 / T := by ring
    _ ≤ 9000 * X * (Real.log X) ^ 2 / T := by gcongr <;> norm_num

/-- Coarse common polynomial envelope for the principal contour
logarithmic-derivative majorant. -/
theorem principalContourR_le
    (D : ℕ) {X : ℝ} (hlog : 2 ≤ Real.log X) :
    let d := MAPKoukExercise12TwoContourAperture.exerciseContourClearance
      (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
    let LH := Real.log ((Real.log X) ^ D + 3)
    2 + 20 * (Real.log 223948800 + 6 * LH) +
        30300 * LH + 30300 * LH / d ≤
      10000000000000 * (Real.log X) ^ (4 * D) := by
  let L := Real.log X
  let H := L ^ D
  let d := MAPKoukExercise12TwoContourAperture.exerciseContourClearance
    (1 : DirichletCharacter ℂ 1) H
  let LH := Real.log (H + 3)
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hH1 : 1 ≤ H := by dsimp [H]; exact one_le_pow₀ hL1
  have hLH : LH ≤ 3 * H := by
    have harg : 0 < H + 3 := by positivity
    dsimp only [LH]
    exact (Real.log_le_sub_one_of_pos harg).trans (by linarith)
  have hinv : d⁻¹ ≤ 80000016 * L ^ (3 * D) := by
    dsimp only [d, H, L]
    simpa only [Nat.zero_add] using
      MAPKoukExercise12TwoPolylogScalars.inv_exerciseContourClearance_polylogHeight_le
        0 D hlog (1 : DirichletCharacter ℂ 1)
          (by
            show (1 : DirichletCharacter ℂ 1).conductor = 1
            rw [DirichletCharacter.conductor_one]) (by simp)
  have hLH0 : 0 ≤ LH := by
    dsimp only [LH]
    exact Real.log_nonneg (by linarith)
  have hinv0 : 0 ≤ d⁻¹ := inv_nonneg.mpr
      (MAPKoukExercise12TwoContourAperture.exerciseContourClearance_pos
        (1 : DirichletCharacter ℂ 1) H).le
  have hdiv : LH / d ≤ 240000048 * L ^ (4 * D) := by
    rw [div_eq_mul_inv]
    calc
      LH * d⁻¹ ≤ (3 * H) * (80000016 * L ^ (3 * D)) :=
        mul_le_mul hLH hinv hinv0 (by positivity)
      _ = 240000048 * L ^ (4 * D) := by
        dsimp only [H]
        rw [show 4 * D = D + 3 * D by omega, pow_add]
        ring
  have hpow : 1 ≤ L ^ (4 * D) := one_le_pow₀ hL1
  have hLHpow : LH ≤ 3 * L ^ (4 * D) := by
    refine hLH.trans ?_
    have hD : D ≤ 4 * D := by omega
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL1 hD) (by norm_num)
  have hconst : Real.log 223948800 ≤ 223948800 :=
    (Real.log_le_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 223948800)).trans (by norm_num)
  have hdivScaled : 30300 * LH / d ≤
      30300 * (240000048 * L ^ (4 * D)) := by
    calc
      30300 * LH / d = 30300 * (LH / d) := by ring
      _ ≤ 30300 * (240000048 * L ^ (4 * D)) :=
        mul_le_mul_of_nonneg_left hdiv (by norm_num)
  have hrough :
      2 + 20 * (Real.log 223948800 + 6 * LH) +
          30300 * LH + 30300 * LH / d ≤
        2 + 20 * (223948800 + 6 * (3 * L ^ (4 * D))) +
        30300 * (3 * (Real.log X) ^ (4 * D)) +
        30300 * (240000048 * L ^ (4 * D)) := by
    dsimp only [L]
    nlinarith [hdivScaled, hLHpow, hconst]
  dsimp only [d, LH, H, L] at hrough ⊢
  exact hrough.trans (by nlinarith [hpow])

end
end MAPKoukExercise12TwoEndpointScalars

#print axioms MAPKoukExercise12TwoEndpointScalars.halfIntegerPoint_floor_range
#print axioms MAPKoukExercise12TwoEndpointScalars.halfIntegerPoint_rpow_one_sub_le_weakFactor
#print axioms MAPKoukExercise12TwoEndpointScalars.insideMajorant_le
#print axioms MAPKoukExercise12TwoEndpointScalars.outsideMajorant_le
#print axioms MAPKoukExercise12TwoEndpointScalars.principalContourR_le
