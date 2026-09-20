import GuthMaynardS2DyadicReflection

/-! # Scale-local bound for the literal S2 reflection error
On a dyadic gap `U = N * 2^i` with Fourier cutoff `J = i + L`, the three
explicit remainder terms in `sourceReflectionError` are `O_ell(2^L / N)`.
The Mellin exterior and far-Fourier tails are `O_ell(1/N)`; the negative
frequency term is exactly a multiple of `2^L / N`.
-/

namespace GuthMaynardS2ReflectionError

open GuthMaynardS2DyadicReflection
open GuthMaynardLemma62AbsoluteMellinTail
open GuthMaynardLemma62NegativeNonstationary
open GuthMaynardSectionThreeCutoffDerivativeBudget

noncomputable section

/-- Absolute Mellin-tail prefactor at the fixed order `k = 6`. -/
def reflectionErrorMellinConstant : ℝ :=
  (128 / 5) * (2 * Real.pi) ^ 5 * sectionThreeMellinSeminorm 6

/-- Far-Fourier prefactor after the source bound `(1 + V) ≤ 3U`. -/
def reflectionErrorFarConstant (ell : ℕ) : ℝ :=
  2 * lemma43DerivativeConstant ell * (3 : ℝ) ^ ell / ((ell : ℝ) - 1)

/-- Combined `C_err(ell)` in the scale-local remainder `C_err(ell) * 2^L / N`. -/
def sourceReflectionErrorConstant (ell : ℕ) : ℝ :=
  reflectionErrorMellinConstant + negativeSectorConstant +
    reflectionErrorFarConstant ell

theorem reflectionErrorMellinConstant_nonneg :
    0 ≤ reflectionErrorMellinConstant := by
  unfold reflectionErrorMellinConstant
  have hsem := sectionThreeMellinSeminorm_nonneg 6
  positivity

theorem reflectionErrorFarConstant_nonneg {ell : ℕ} (hell : 2 ≤ ell) :
    0 ≤ reflectionErrorFarConstant ell := by
  unfold reflectionErrorFarConstant
  have hder := lemma43DerivativeConstant_nonneg ell
  have hellR : (1 : ℝ) < ell := by exact_mod_cast (show 1 < ell by omega)
  positivity

theorem sourceReflectionErrorConstant_nonneg {ell : ℕ} (hell : 2 ≤ ell) :
    0 ≤ sourceReflectionErrorConstant ell :=
  add_nonneg (add_nonneg reflectionErrorMellinConstant_nonneg
    negativeSectorConstant_nonneg) (reflectionErrorFarConstant_nonneg hell)

private theorem two_pow_natCast (n : ℕ) :
    ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by
  exact_mod_cast Nat.cast_pow (2 : ℕ) n

private theorem log_two_mul_two_pow_le (J : ℕ) :
    Real.log (2 * ((2 ^ J : ℕ) : ℝ)) ≤ 2 * ((2 ^ J : ℕ) : ℝ) := by
  have hx : 0 < 2 * ((2 ^ J : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hx
  linarith

private theorem rpow_one_sub_nat {x : ℝ} (hx : 0 < x) (ell : ℕ) :
    x ^ (1 - (ell : ℝ)) = x / x ^ ell := by
  rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one, Real.rpow_neg hx.le,
    Real.rpow_natCast]
  field_simp [hx.ne']

/-- The Mellin exterior is `O(1/N)` on the legal dyadic geometry. -/
theorem sourceReflectionError_mellin_le
    {N T : ℝ} {i L : ℕ}
    (hN : 1 ≤ N) (hT : T ≤ N ^ 2)
    (hJ : (2 : ℝ) ^ (i + L) ≤ T) :
    ((1 / (2 * Real.pi)) *
        Real.log (2 * ((2 ^ (i + L) : ℕ) : ℝ)) *
        ((2 ^ (i + L) : ℕ) : ℝ)) *
      (2 * (((2 * Real.pi) ^ 6 * sectionThreeMellinSeminorm 6) *
        (((N / 2) ^ (1 - (6 : ℝ))) / ((6 : ℝ) - 1)))) ≤
      reflectionErrorMellinConstant / N := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hR : 0 < N / 2 := by positivity
  have htwoJ : ((2 ^ (i + L) : ℕ) : ℝ) = (2 : ℝ) ^ (i + L) := two_pow_natCast _
  have hJ0 : 0 ≤ (2 : ℝ) ^ (i + L) := by positivity
  have hJ2 : ((2 ^ (i + L) : ℕ) : ℝ) ^ 2 ≤ N ^ 4 := by
    rw [htwoJ]
    have hJT : (2 : ℝ) ^ (i + L) ≤ N ^ 2 := hJ.trans hT
    have hsq := pow_le_pow_left₀ hJ0 hJT 2
    have hN4 : (N ^ 2) ^ 2 = N ^ 4 := by ring
    exact hsq.trans_eq hN4
  have hRpow : (N / 2) ^ (1 - (6 : ℝ)) = 32 / N ^ 5 := by
    have hneg : (1 : ℝ) - 6 = (-5 : ℝ) := by norm_num
    rw [hneg, Real.rpow_neg (by positivity : 0 ≤ N / 2),
      show (5 : ℝ) = (5 : ℕ) from rfl, Real.rpow_natCast]
    have hpow : (N / 2) ^ 5 = N ^ 5 / 32 := by
      field_simp
      ring
    rw [hpow]
    field_simp [hNpos.ne']
  have hlog := log_two_mul_two_pow_le (i + L)
  have hsem := sectionThreeMellinSeminorm_nonneg 6
  have hpre : 0 ≤ (1 / (2 * Real.pi)) * 2 *
      ((2 * Real.pi) ^ 6 * sectionThreeMellinSeminorm 6) / 5 := by positivity
  have hprod : Real.log (2 * ((2 ^ (i + L) : ℕ) : ℝ)) *
      ((2 ^ (i + L) : ℕ) : ℝ) * ((N / 2) ^ (1 - (6 : ℝ))) ≤
        64 / N := by
    have hR5 : (N / 2) ^ (1 - (6 : ℝ)) = 32 / N ^ 5 := hRpow
    have hlog2 : Real.log (2 * ((2 ^ (i + L) : ℕ) : ℝ)) *
        ((2 ^ (i + L) : ℕ) : ℝ) ≤
          2 * ((2 ^ (i + L) : ℕ) : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hlog (by positivity :
        0 ≤ ((2 ^ (i + L) : ℕ) : ℝ))
      nlinarith
    have hnum : 2 * ((2 ^ (i + L) : ℕ) : ℝ) ^ 2 * (32 / N ^ 5) ≤
        2 * (N ^ 4) * (32 / N ^ 5) := by
      gcongr
    have hsimp : 2 * (N ^ 4) * (32 / N ^ 5) = 64 / N := by
      field_simp [hNpos.ne']
      ring
    calc
      _ = Real.log (2 * ((2 ^ (i + L) : ℕ) : ℝ)) *
            ((2 ^ (i + L) : ℕ) : ℝ) * (32 / N ^ 5) := by rw [hR5]
      _ ≤ 2 * ((2 ^ (i + L) : ℕ) : ℝ) ^ 2 * (32 / N ^ 5) := by
        exact mul_le_mul_of_nonneg_right hlog2 (by positivity)
      _ ≤ _ := hnum.trans_eq hsimp
  have hrewrite :
      ((1 / (2 * Real.pi)) *
          Real.log (2 * ((2 ^ (i + L) : ℕ) : ℝ)) *
          ((2 ^ (i + L) : ℕ) : ℝ)) *
        (2 * (((2 * Real.pi) ^ 6 * sectionThreeMellinSeminorm 6) *
          (((N / 2) ^ (1 - (6 : ℝ))) / ((6 : ℝ) - 1)))) =
        ((1 / (2 * Real.pi)) * 2 *
            ((2 * Real.pi) ^ 6 * sectionThreeMellinSeminorm 6) / 5) *
          (Real.log (2 * ((2 ^ (i + L) : ℕ) : ℝ)) *
            ((2 ^ (i + L) : ℕ) : ℝ) *
              ((N / 2) ^ (1 - (6 : ℝ)))) := by
    ring
  have hconst :
      ((1 / (2 * Real.pi)) * 2 *
          ((2 * Real.pi) ^ 6 * sectionThreeMellinSeminorm 6) / 5) * (64 / N) =
        reflectionErrorMellinConstant / N := by
    unfold reflectionErrorMellinConstant
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    field_simp [hpi]
    ring
  calc
    _ = _ := hrewrite
    _ ≤ ((1 / (2 * Real.pi)) * 2 *
          ((2 * Real.pi) ^ 6 * sectionThreeMellinSeminorm 6) / 5) *
        (64 / N) :=
      mul_le_mul_of_nonneg_left hprod hpre
    _ = _ := hconst

/-- The opposite-sign remainder is exactly `O(B/N)` with `B = 2^L`. -/
theorem sourceReflectionError_negative_eq
    {N : ℝ} {i L : ℕ} (hN : 0 < N) :
    ((2 ^ (i + L) : ℕ) : ℝ) *
        (negativeSectorConstant / (N * (2 : ℝ) ^ i)) =
      negativeSectorConstant * (2 : ℝ) ^ L / N := by
  have htwo : ((2 ^ (i + L) : ℕ) : ℝ) = (2 : ℝ) ^ i * (2 : ℝ) ^ L := by
    rw [two_pow_natCast, pow_add]
  rw [htwo]
  field_simp [hN.ne', (pow_pos (by norm_num : (0 : ℝ) < 2) i).ne']

/-- The far-Fourier tail is `O_ell(1/N)` once `U ≤ T ≤ B^(ell-1)`. -/
theorem sourceReflectionError_far_le
    {N T : ℝ} {i L ell : ℕ}
    (hN : 1 ≤ N) (hell : 2 ≤ ell)
    (hU : N * (2 : ℝ) ^ i ≤ T)
    (hT : T ≤ ((2 : ℝ) ^ L) ^ (ell - 1)) :
    2 * ((lemma43DerivativeConstant ell *
        (1 + 2 * N * (2 : ℝ) ^ i) ^ ell *
        N ^ (-(ell : ℝ))) *
      (((2 ^ (i + L) : ℕ) : ℝ) ^ (1 - (ell : ℝ)) /
        ((ell : ℝ) - 1))) ≤
      reflectionErrorFarConstant ell / N := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hU1 : (1 : ℝ) ≤ N * (2 : ℝ) ^ i :=
    one_le_mul_of_one_le_of_one_le hN (one_le_pow₀ (by norm_num))
  have hVbd : 1 + 2 * N * (2 : ℝ) ^ i ≤ 3 * (N * (2 : ℝ) ^ i) := by nlinarith
  have hellR : (1 : ℝ) < ell := by exact_mod_cast (show 1 < ell by omega)
  have hder := lemma43DerivativeConstant_nonneg ell
  have htwoJpos : 0 < ((2 ^ (i + L) : ℕ) : ℝ) := by positivity
  have hNpow : N ^ (-(ell : ℝ)) = (N ^ ell)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hNpos), Real.rpow_natCast]
  have hJpow : ((2 ^ (i + L) : ℕ) : ℝ) ^ (1 - (ell : ℝ)) =
      ((2 ^ (i + L) : ℕ) : ℝ) * (((2 ^ (i + L) : ℕ) : ℝ) ^ ell)⁻¹ := by
    rw [rpow_one_sub_nat htwoJpos ell, div_eq_mul_inv]
  let U := N * (2 : ℝ) ^ i
  let B := (2 : ℝ) ^ L
  have hUdef : U = N * (2 : ℝ) ^ i := rfl
  have hBdef : B = (2 : ℝ) ^ L := rfl
  have htwoJ : ((2 ^ (i + L) : ℕ) : ℝ) = (2 : ℝ) ^ i * B := by
    rw [two_pow_natCast, pow_add, hBdef]
  have hcore : (1 + 2 * N * (2 : ℝ) ^ i) ^ ell *
      N ^ (-(ell : ℝ)) *
      ((2 ^ (i + L) : ℕ) : ℝ) ^ (1 - (ell : ℝ)) ≤
        (3 : ℝ) ^ ell / N := by
    have hJeq : ((2 ^ (i + L) : ℕ) : ℝ) * (((2 ^ (i + L) : ℕ) : ℝ) ^ ell)⁻¹ =
        ((2 : ℝ) ^ i * B) * (((2 : ℝ) ^ i * B) ^ ell)⁻¹ := by
      rw [htwoJ]
    have hprod :
        (1 + 2 * N * (2 : ℝ) ^ i) ^ ell *
          (N ^ ell)⁻¹ *
          (((2 ^ (i + L) : ℕ) : ℝ) * (((2 ^ (i + L) : ℕ) : ℝ) ^ ell)⁻¹) ≤
            (3 * U) ^ ell * (N ^ ell)⁻¹ *
              (((2 : ℝ) ^ i * B) * (((2 : ℝ) ^ i * B) ^ ell)⁻¹) := by
      rw [hJeq]
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · exact pow_le_pow_left₀ (by positivity) hVbd ell
        · positivity
      · positivity
    have h3U : (3 * U) ^ ell = (3 : ℝ) ^ ell * U ^ ell := mul_pow _ _ _
    have hUell : U ^ ell = N ^ ell * ((2 : ℝ) ^ i) ^ ell := by
      dsimp [U]; rw [mul_pow]
    have hBpow : ((2 : ℝ) ^ i * B) ^ ell = ((2 : ℝ) ^ i) ^ ell * B ^ ell := mul_pow _ _ _
    have hBell : B ^ ell = B ^ (ell - 1) * B := by
      rw [← pow_succ, Nat.sub_add_cancel (le_trans (by norm_num : 1 ≤ 2) hell)]
    have hmid : (3 : ℝ) ^ ell * U ^ ell * (N ^ ell)⁻¹ *
        (((2 : ℝ) ^ i * B) * (((2 : ℝ) ^ i * B) ^ ell)⁻¹) =
          (3 : ℝ) ^ ell * U / (N * B ^ (ell - 1)) := by
      have hi0 : (2 : ℝ) ^ i ≠ 0 := by positivity
      have hB0 : B ≠ 0 := by positivity
      have hNell : N ^ ell ≠ 0 := pow_ne_zero _ hNpos.ne'
      rw [hUell, hBpow, hBell]
      field_simp [hNpos.ne', hi0, hB0, hNell]
      ring
    have hfrac : (3 : ℝ) ^ ell * U / (N * B ^ (ell - 1)) ≤ (3 : ℝ) ^ ell / N := by
      have hden : 0 < N * B ^ (ell - 1) := by positivity
      have h1 : (3 : ℝ) ^ ell * U / (N * B ^ (ell - 1)) ≤
          (3 : ℝ) ^ ell * T / (N * B ^ (ell - 1)) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hUdef ▸ hU) (by positivity)) hden.le
      have h2 : (3 : ℝ) ^ ell * T / (N * B ^ (ell - 1)) ≤
          (3 : ℝ) ^ ell * (B ^ (ell - 1)) / (N * B ^ (ell - 1)) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hT (by positivity)) hden.le
      have h3 : (3 : ℝ) ^ ell * (B ^ (ell - 1)) / (N * B ^ (ell - 1)) =
          (3 : ℝ) ^ ell / N := by
        field_simp [hNpos.ne', (pow_pos (show 0 < B by positivity) (ell - 1)).ne']
      exact h1.trans (h2.trans_eq h3)
    calc
      _ = (1 + 2 * N * (2 : ℝ) ^ i) ^ ell * (N ^ ell)⁻¹ *
            (((2 ^ (i + L) : ℕ) : ℝ) *
              (((2 ^ (i + L) : ℕ) : ℝ) ^ ell)⁻¹) := by
        rw [hNpow, hJpow]
      _ ≤ (3 * U) ^ ell * (N ^ ell)⁻¹ *
            (((2 : ℝ) ^ i * B) * (((2 : ℝ) ^ i * B) ^ ell)⁻¹) := hprod
      _ = (3 : ℝ) ^ ell * U ^ ell * (N ^ ell)⁻¹ *
            (((2 : ℝ) ^ i * B) * (((2 : ℝ) ^ i * B) ^ ell)⁻¹) := by
        rw [h3U]
      _ = (3 : ℝ) ^ ell * U / (N * B ^ (ell - 1)) := hmid
      _ ≤ (3 : ℝ) ^ ell / N := hfrac
  have hpre : 0 ≤ 2 * lemma43DerivativeConstant ell / ((ell : ℝ) - 1) := by
    positivity
  have hrewrite :
      2 * ((lemma43DerivativeConstant ell *
          (1 + 2 * N * (2 : ℝ) ^ i) ^ ell *
          N ^ (-(ell : ℝ))) *
        (((2 ^ (i + L) : ℕ) : ℝ) ^ (1 - (ell : ℝ)) /
          ((ell : ℝ) - 1))) =
        (2 * lemma43DerivativeConstant ell / ((ell : ℝ) - 1)) *
          ((1 + 2 * N * (2 : ℝ) ^ i) ^ ell *
            N ^ (-(ell : ℝ)) *
            ((2 ^ (i + L) : ℕ) : ℝ) ^ (1 - (ell : ℝ))) := by
    ring
  have hconst :
      (2 * lemma43DerivativeConstant ell / ((ell : ℝ) - 1)) *
          ((3 : ℝ) ^ ell / N) =
        reflectionErrorFarConstant ell / N := by
    unfold reflectionErrorFarConstant
    ring
  calc
    _ = _ := hrewrite
    _ ≤ (2 * lemma43DerivativeConstant ell / ((ell : ℝ) - 1)) *
        ((3 : ℝ) ^ ell / N) :=
      mul_le_mul_of_nonneg_left hcore hpre
    _ = _ := hconst

/-- Literal dyadic remainder
`sourceReflectionError N (N*2^i) (2*N*2^i) (N/2) (i+L) 6 ell`
is at most `C_err(ell) * 2^L / N`. -/
theorem sourceReflectionError_le
    {N : ℕ} {T : ℝ} {i L ell : ℕ}
    (hN : 1 ≤ N) (_hT1 : 1 ≤ T) (hTN : T ≤ (N : ℝ) ^ 2)
    (hUi : (N : ℝ) * (2 : ℝ) ^ i ≤ T)
    (hJ : (2 : ℝ) ^ (i + L) ≤ T)
    (hBell : T ≤ ((2 : ℝ) ^ L) ^ (ell - 1))
    (hell : 2 ≤ ell) :
    sourceReflectionError N ((N : ℝ) * (2 : ℝ) ^ i)
        (2 * (N : ℝ) * (2 : ℝ) ^ i) ((N : ℝ) / 2) (i + L) 6 ell ≤
      sourceReflectionErrorConstant ell * (2 : ℝ) ^ L / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold sourceReflectionError sourceReflectionErrorConstant
  have hmellin := sourceReflectionError_mellin_le hNreal hTN hJ
  have hneg := sourceReflectionError_negative_eq (N := (N : ℝ)) (i := i) (L := L) hNpos
  have hfar := sourceReflectionError_far_le (N := (N : ℝ)) hNreal hell hUi hBell
  have hL : (1 : ℝ) ≤ (2 : ℝ) ^ L := one_le_pow₀ (by norm_num)
  have hmellin' : ((1 / (2 * Real.pi)) *
        Real.log (2 * ((2 ^ (i + L) : ℕ) : ℝ)) *
        ((2 ^ (i + L) : ℕ) : ℝ)) *
      (2 * (((2 * Real.pi) ^ 6 * sectionThreeMellinSeminorm 6) *
        (((N : ℝ) / 2) ^ (1 - (6 : ℝ)) / ((6 : ℝ) - 1)))) ≤
      reflectionErrorMellinConstant * (2 : ℝ) ^ L / (N : ℝ) := by
    apply hmellin.trans
    exact div_le_div_of_nonneg_right
      (le_mul_of_one_le_right reflectionErrorMellinConstant_nonneg hL) hNpos.le
  have hneg' :
      ((2 ^ (i + L) : ℕ) : ℝ) *
          (negativeSectorConstant / ((N : ℝ) * (2 : ℝ) ^ i)) ≤
        negativeSectorConstant * (2 : ℝ) ^ L / (N : ℝ) :=
    hneg.le
  have hfar' : 2 * ((lemma43DerivativeConstant ell *
        (1 + 2 * (N : ℝ) * (2 : ℝ) ^ i) ^ ell *
        (N : ℝ) ^ (-(ell : ℝ))) *
      (((2 ^ (i + L) : ℕ) : ℝ) ^ (1 - (ell : ℝ)) /
        ((ell : ℝ) - 1))) ≤
      reflectionErrorFarConstant ell * (2 : ℝ) ^ L / (N : ℝ) := by
    apply hfar.trans
    exact div_le_div_of_nonneg_right
      (le_mul_of_one_le_right (reflectionErrorFarConstant_nonneg hell) hL)
      hNpos.le
  -- `k = 6` reduces the Mellin seminorm power to the same expression as `hmellin'`.
  simp only [Nat.cast_ofNat]
  refine (add_le_add (add_le_add hmellin' hneg') hfar').trans_eq ?_
  ring

end
end GuthMaynardS2ReflectionError

#print axioms GuthMaynardS2ReflectionError.sourceReflectionError_le
#print axioms GuthMaynardS2ReflectionError.sourceReflectionError_mellin_le
#print axioms GuthMaynardS2ReflectionError.sourceReflectionError_negative_eq
#print axioms GuthMaynardS2ReflectionError.sourceReflectionError_far_le
