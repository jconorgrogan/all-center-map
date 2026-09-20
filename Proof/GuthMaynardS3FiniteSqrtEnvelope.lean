import GuthMaynardFiniteSqrtBootstrap

open scoped Real

noncomputable section
namespace GuthMaynardS3FiniteSqrtEnvelope

open GuthMaynardJIteration

/-- The scalar output of the finite square-root bootstrap has the expected
power envelope.  All constants in the right hand side are selected before
`T`; the only dependence on the recurrence coefficients is through `C`. -/
theorem finite_sqrt_scalar_envelope
    {eta delta epsilon : ℝ} {N : ℕ}
    (heta : 0 < eta) (hdelta : 0 < delta)
    (hexp : 8 * eta + 2 * delta + 2 / ((2 : ℝ) ^ N) ≤ epsilon) :
    ∀ C T : ℝ, 0 < C → 1 ≤ T →
      (let A : ℝ := C * (16 : ℝ) ^ 6 * T ^ (3 * eta) + C
       let B : ℝ := C * T ^ (4 * eta + delta) * (16 : ℝ) ^ 2
       let D : ℝ := max 1 (max (2 * A) (4 * B ^ 2))
       D * iterSqrt N (max 1 ((34848 * T ^ 2) / D)) ≤
         34848 * (1 + 4 * C * (16 : ℝ) ^ 6 + 4 * C ^ 2 * (16 : ℝ) ^ 4) *
           T ^ epsilon) := by
  intro C T hC hT
  dsimp
  let q : ℝ := 8 * eta + 2 * delta
  let r : ℝ := ((2 : ℝ) ^ N)⁻¹
  let K0 : ℝ := 1 + 4 * C * (16 : ℝ) ^ 6 + 4 * C ^ 2 * (16 : ℝ) ^ 4
  let A : ℝ := C * (16 : ℝ) ^ 6 * T ^ (3 * eta) + C
  let B : ℝ := C * T ^ (4 * eta + delta) * (16 : ℝ) ^ 2
  let D : ℝ := max 1 (max (2 * A) (4 * B ^ 2))
  let H : ℝ := 34848 * T ^ 2
  let U : ℝ := max 1 (H / D)
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT0 : 0 ≤ T := hTpos.le
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
    exact (inv_le_one₀ (by positivity)).2 hp
  have hqexp : q + 2 * r ≤ epsilon := by
    dsimp [q, r] at hexp ⊢
    exact hexp
  have hTq1 : 1 ≤ T ^ q := Real.one_le_rpow hT hq
  have hTq0 : 0 ≤ T ^ q := (Real.rpow_nonneg hT0 q)
  have hT3 : T ^ (3 * eta) ≤ T ^ q := by
    apply Real.rpow_le_rpow_of_exponent_le hT
    dsimp [q]
    linarith
  have hCterm : C ≤ C * (16 : ℝ) ^ 6 * T ^ q := by
    have hpow16 : (1 : ℝ) ≤ (16 : ℝ) ^ 6 := by norm_num
    have hmul : C ≤ C * (16 : ℝ) ^ 6 := by nlinarith
    exact hmul.trans (by
      exact le_mul_of_one_le_right (by positivity) hTq1)
  have hA2 : 2 * A ≤ (4 * C * (16 : ℝ) ^ 6) * T ^ q := by
    have hmain : C * (16 : ℝ) ^ 6 * T ^ (3 * eta) ≤
        C * (16 : ℝ) ^ 6 * T ^ q := by gcongr
    dsimp [A]
    nlinarith
  have hB4 : 4 * B ^ 2 = (4 * C ^ 2 * (16 : ℝ) ^ 4) * T ^ q := by
    dsimp [B, q]
    have hsquare : (T ^ (4 * eta + delta)) ^ (2 : ℕ) =
        T ^ ((4 * eta + delta) * (2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT0]
      norm_num
    calc
      4 * (C * T ^ (4 * eta + delta) * (16 : ℝ) ^ 2) ^ 2 =
          4 * C ^ (2 : ℕ) * (T ^ (4 * eta + delta)) ^ (2 : ℕ) *
            ((16 : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = 4 * C ^ (2 : ℕ) * (16 : ℝ) ^ (4 : ℕ) *
            T ^ ((4 * eta + delta) * (2 : ℝ)) := by
        rw [hsquare]
        norm_num
        ring
      _ = 4 * C ^ (2 : ℕ) * (16 : ℝ) ^ (4 : ℕ) *
            T ^ (8 * eta + 2 * delta) := by
        congr 2
        ring
  have hD : D ≤ K0 * T ^ q := by
    have hD1 : (1 : ℝ) ≤ K0 * T ^ q := by
      have hK01 : (1 : ℝ) ≤ K0 := by
        dsimp [K0]
        nlinarith [sq_nonneg C]
      exact hK01.trans (le_mul_of_one_le_right (by positivity) hTq1)
    have hD2 : 2 * A ≤ K0 * T ^ q :=
      hA2.trans (by
        have hK : 4 * C * (16 : ℝ) ^ 6 ≤ K0 := by
          dsimp [K0]
          nlinarith [sq_nonneg C]
        gcongr)
    have hD4 : 4 * B ^ 2 ≤ K0 * T ^ q := by
      rw [hB4]
      have hK : 4 * C ^ 2 * (16 : ℝ) ^ 4 ≤ K0 := by
        dsimp [K0]
        nlinarith [sq_nonneg C]
      gcongr
    dsimp [D]
    exact max_le hD1 (max_le hD2 hD4)
  have hD1 : 1 ≤ D := by
    dsimp [D]
    exact le_max_left _ _
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hH0 : 0 ≤ H := by
    dsimp [H]
    positivity
  have hH1 : 1 ≤ H := by
    dsimp [H]
    have : (1 : ℝ) ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 1)]
    nlinarith
  have hHD : H / D ≤ H := by
    apply (div_le_iff₀ hDpos).2
    have hmul : 0 ≤ H * (D - 1) := mul_nonneg hH0 (sub_nonneg.mpr hD1)
    nlinarith
  have hU_H : U ≤ H := by
    dsimp [U]
    exact max_le hH1 hHD
  have hU0 : 0 ≤ U := le_trans zero_le_one (le_max_left _ _)
  have hUr : U ^ r ≤ H ^ r := Real.rpow_le_rpow hU0 hU_H hr0
  have hHr : H ^ r ≤ 34848 * T ^ (2 * r) := by
    have hconst : (34848 : ℝ) ^ r ≤ 34848 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 34848) hr1
      simpa using this
    have hmul : H = (34848 : ℝ) * T ^ (2 : ℕ) := by
      dsimp [H]
    calc
      H ^ r = ((34848 : ℝ) * T ^ (2 : ℕ)) ^ r := by rw [hmul]
      _ = (34848 : ℝ) ^ r * (T ^ (2 : ℕ)) ^ r := by
        exact Real.mul_rpow (by norm_num) (by positivity)
      _ = (34848 : ℝ) ^ r * T ^ (2 * r) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT0]
        norm_num
      _ ≤ 34848 * T ^ (2 * r) :=
        mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hT0 _)
  have hiter : iterSqrt N U = U ^ r := by
    rw [iterSqrt_eq_rpow hU0]
    rfl
  have hmainpow : T ^ q * T ^ (2 * r) = T ^ (q + 2 * r) := by
    exact (Real.rpow_add hTpos q (2 * r)).symm
  have hTexp : T ^ (q + 2 * r) ≤ T ^ epsilon :=
    Real.rpow_le_rpow_of_exponent_le hT hqexp
  have hK0 : 0 ≤ K0 := by
    dsimp [K0]
    nlinarith [sq_nonneg C]
  have hprod : D * iterSqrt N U ≤
      34848 * K0 * T ^ q * T ^ (2 * r) := by
    rw [hiter]
    calc
      D * U ^ r ≤ D * H ^ r :=
        mul_le_mul_of_nonneg_left hUr (le_trans zero_le_one hD1)
      _ ≤ D * (34848 * T ^ (2 * r)) :=
        mul_le_mul_of_nonneg_left hHr (le_trans zero_le_one hD1)
      _ ≤ (K0 * T ^ q) * (34848 * T ^ (2 * r)) := by
        gcongr
      _ = 34848 * K0 * T ^ q * T ^ (2 * r) := by ring
  calc
    D * iterSqrt N (max 1 ((34848 * T ^ 2) / D)) = D * iterSqrt N U := by rfl
    _ ≤ 34848 * K0 * T ^ q * T ^ (2 * r) := hprod
    _ = 34848 * K0 * T ^ (q + 2 * r) := by
      calc
        34848 * K0 * T ^ q * T ^ (2 * r) =
            34848 * K0 * (T ^ q * T ^ (2 * r)) := by ring
        _ = 34848 * K0 * T ^ (q + 2 * r) := by rw [hmainpow]
    _ ≤ 34848 * K0 * T ^ epsilon := by
      gcongr
    _ = 34848 * (1 + 4 * C * (16 : ℝ) ^ 6 + 4 * C ^ 2 * (16 : ℝ) ^ 4) * T ^ epsilon := by
      rfl

end GuthMaynardS3FiniteSqrtEnvelope

#print axioms GuthMaynardS3FiniteSqrtEnvelope.finite_sqrt_scalar_envelope
