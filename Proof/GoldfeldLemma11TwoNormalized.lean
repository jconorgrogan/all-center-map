import GoldfeldLemma11TwoDerivative

/-!
# Normalized `t = 0` derivative bound from Koukoulopoulos, Lemma 11.2

This module performs only the elementary cutoff and logarithmic absorption
after `GoldfeldLemma11TwoDerivative`.
-/

namespace MAPGoldfeldSiegel

open Complex

noncomputable section

/-- Multiplying the square-root conductor by its negative `sigma` power gives
the source exponent `1 - sigma`. -/
theorem sqrt_mul_rpow_neg_eq_rpow_one_sub
    {x sigma : ℝ} (hx : 0 < x) :
    x * Real.rpow x (-sigma) = Real.rpow x (1 - sigma) := by
  calc
    x * Real.rpow x (-sigma) =
        Real.rpow x 1 * Real.rpow x (-sigma) := by
      rw [show Real.rpow x 1 = x by simp [Real.rpow_eq_pow]]
    _ = Real.rpow x (1 + -sigma) := by
      simpa only [Real.rpow_eq_pow] using (Real.rpow_add hx 1 (-sigma)).symm
    _ = Real.rpow x (1 - sigma) := by ring_nf

/-- Absorption of the trivial initial segment at
`K = 9 * ceil (sqrt N)`. -/
theorem goldfeldCutoff_initialTerm_le
    {N : ℕ} (hN : 2 ≤ N)
    {sigma : ℝ} (hsigmaHalf : 1 / 2 ≤ sigma) (hsigmaOne : sigma ≤ 1) :
    let K := 9 * Nat.ceil (Real.sqrt N)
    Real.rpow (K : ℝ) (1 - sigma) * Real.log K * (1 + Real.log K) ≤
      5508 * Real.rpow (Real.sqrt N) (1 - sigma) *
        (1 + Real.log N) ^ 2 := by
  dsimp only
  let K := 9 * Nat.ceil (Real.sqrt N)
  have hpow := goldfeldCutoff_rpow_le hN hsigmaHalf hsigmaOne
  change Real.rpow (K : ℝ) (1 - sigma) ≤
    18 * Real.rpow (Real.sqrt N) (1 - sigma) at hpow
  have hlog := (goldfeldCutoff_log_bounds hN).1
  change Real.log (K : ℝ) ≤ 17 * (1 + Real.log (N : ℝ)) at hlog
  have hNone : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNone
  have hLone : 1 ≤ 1 + Real.log (N : ℝ) := by linarith
  have hL0 : 0 ≤ 1 + Real.log (N : ℝ) := hLone.trans' (by norm_num)
  have hlogK0 : 0 ≤ Real.log (K : ℝ) := by
    have hKone : (1 : ℝ) ≤ K := by
      have hsqrtPos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by
        exact_mod_cast (Nat.zero_lt_of_lt hN))
      have hceil : 1 ≤ Nat.ceil (Real.sqrt N) :=
        (Nat.one_le_iff_ne_zero).2 (ne_of_gt (Nat.ceil_pos.2 hsqrtPos))
      exact_mod_cast (show 1 ≤ K by dsimp [K]; omega)
    exact Real.log_nonneg hKone
  have hlogPlus : 1 + Real.log (K : ℝ) ≤
      18 * (1 + Real.log (N : ℝ)) := by nlinarith
  have hpowRight0 : 0 ≤ 18 * Real.rpow (Real.sqrt N) (1 - sigma) := by
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hprod : Real.rpow (K : ℝ) (1 - sigma) * Real.log K ≤
      (18 * Real.rpow (Real.sqrt N) (1 - sigma)) *
        (17 * (1 + Real.log N)) :=
    mul_le_mul hpow hlog hlogK0 hpowRight0
  have hprodRight0 : 0 ≤
      (18 * Real.rpow (Real.sqrt N) (1 - sigma)) *
        (17 * (1 + Real.log N)) :=
    mul_nonneg hpowRight0 (mul_nonneg (by norm_num) hL0)
  calc
    Real.rpow (K : ℝ) (1 - sigma) * Real.log K * (1 + Real.log K) ≤
        (18 * Real.rpow (Real.sqrt N) (1 - sigma)) *
          (17 * (1 + Real.log N)) * (18 * (1 + Real.log N)) := by
      exact mul_le_mul hprod hlogPlus (by positivity) hprodRight0
    _ = 5508 * Real.rpow (Real.sqrt N) (1 - sigma) *
        (1 + Real.log N) ^ 2 := by ring

/-- Absorption of the Pólya--Vinogradov/Abel tail at the same cutoff. -/
theorem goldfeldCutoff_tailTerm_le
    {N : ℕ} (hN : 2 ≤ N)
    {sigma : ℝ} (hsigmaHalf : 1 / 2 ≤ sigma) :
    let K := 9 * Nat.ceil (Real.sqrt N)
    2 * (Real.sqrt N * (1 + Real.log N)) *
        firstDerivativeWeight sigma (K + 1) ≤
      36 * Real.rpow (Real.sqrt N) (1 - sigma) *
        (1 + Real.log N) ^ 2 := by
  dsimp only
  let K := 9 * Nat.ceil (Real.sqrt N)
  have hweight := firstDerivativeWeight_goldfeldCutoff_le hN hsigmaHalf
  change firstDerivativeWeight sigma (K + 1) ≤
    18 * (1 + Real.log (N : ℝ)) * Real.rpow (Real.sqrt N) (-sigma) at hweight
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hRpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hNone : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hL0 : 0 ≤ 1 + Real.log (N : ℝ) := by
    have := Real.log_nonneg hNone
    linarith
  calc
    2 * (Real.sqrt N * (1 + Real.log N)) *
        firstDerivativeWeight sigma (K + 1) ≤
        2 * (Real.sqrt N * (1 + Real.log N)) *
          (18 * (1 + Real.log N) * Real.rpow (Real.sqrt N) (-sigma)) := by
      gcongr
    _ = 36 * (Real.sqrt N * Real.rpow (Real.sqrt N) (-sigma)) *
        (1 + Real.log N) ^ 2 := by ring
    _ = 36 * Real.rpow (Real.sqrt N) (1 - sigma) *
        (1 + Real.log N) ^ 2 := by
      rw [sqrt_mul_rpow_neg_eq_rpow_one_sub hRpos]

/-- Koukoulopoulos, Lemma 11.2 at `t = 0`, `j = 1`, in the exact
primitive-quadratic range needed by Goldfeld's comparison.  The constant is
deliberately generous; the essential conductor exponent is
`(sqrt N)^(1-sigma)`. -/
theorem primitive_quadratic_deriv_LFunction_t0_le
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1) (hreal : chi ^ 2 = 1)
    {sigma : ℝ} (hsigmaHalf : 1 / 2 ≤ sigma) (hsigmaOne : sigma ≤ 1) :
    ‖deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
      6000 * Real.rpow (Real.sqrt N) (1 - sigma) *
        (1 + Real.log N) ^ 2 := by
  let K := 9 * Nat.ceil (Real.sqrt N)
  have hraw := primitive_quadratic_deriv_LFunction_t0_cutoff
    hN chi hprim hchi hreal hsigmaHalf hsigmaOne
  change ‖deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
    Real.rpow (K : ℝ) (1 - sigma) * Real.log K * (1 + Real.log K) +
      2 * (Real.sqrt N * (1 + Real.log N)) *
        firstDerivativeWeight sigma (K + 1) at hraw
  have hinitial := goldfeldCutoff_initialTerm_le hN hsigmaHalf hsigmaOne
  change Real.rpow (K : ℝ) (1 - sigma) * Real.log K * (1 + Real.log K) ≤
    5508 * Real.rpow (Real.sqrt N) (1 - sigma) *
      (1 + Real.log N) ^ 2 at hinitial
  have htail := goldfeldCutoff_tailTerm_le hN hsigmaHalf
  change 2 * (Real.sqrt N * (1 + Real.log N)) *
      firstDerivativeWeight sigma (K + 1) ≤
    36 * Real.rpow (Real.sqrt N) (1 - sigma) *
      (1 + Real.log N) ^ 2 at htail
  have hnonneg : 0 ≤ Real.rpow (Real.sqrt N) (1 - sigma) *
      (1 + Real.log N) ^ 2 := mul_nonneg
    (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (sq_nonneg _)
  calc
    ‖deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤ _ := hraw
    _ ≤ 5508 * Real.rpow (Real.sqrt N) (1 - sigma) *
          (1 + Real.log N) ^ 2 +
        36 * Real.rpow (Real.sqrt N) (1 - sigma) *
          (1 + Real.log N) ^ 2 := add_le_add hinitial htail
    _ ≤ 6000 * Real.rpow (Real.sqrt N) (1 - sigma) *
        (1 + Real.log N) ^ 2 := by nlinarith

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.sqrt_mul_rpow_neg_eq_rpow_one_sub
#print axioms MAPGoldfeldSiegel.goldfeldCutoff_initialTerm_le
#print axioms MAPGoldfeldSiegel.goldfeldCutoff_tailTerm_le
#print axioms MAPGoldfeldSiegel.primitive_quadratic_deriv_LFunction_t0_le
