import Mathlib

/-!
# Scalar convergence behind the long-contour dyadic assembly

This file is independent of the analytic definitions.  It proves that the
square roots of the exact quarter-line block costs form a summable sequence.
The proof retains the `N^{-3/2}` energy and uses only the elementary harmonic
bound; no analytic moment estimate is hidden here.
-/

namespace RamachandraLongDyadicScalarSummability

open scoped BigOperators
open Real

noncomputable section

/-- The scalar root cost of a quarter-line dyadic cell. -/
def longDyadicRootCost (D : ℝ) (j : ℕ) : ℝ :=
  let N : ℕ := 2 ^ j
  Real.sqrt ((D + 8 * Real.pi * (N : ℝ)) *
    Real.rpow (N : ℝ) (-(3 / 2 : ℝ)) *
    (harmonic (2 * N) : ℝ) ^ 4)

private theorem harmonic_two_pow_le (j : ℕ) :
    (harmonic (2 * (2 ^ j)) : ℝ) ≤ (j : ℝ) + 2 := by
  have hh := harmonic_le_one_add_log (2 * (2 ^ j))
  have hcast : ((2 * (2 ^ j) : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) := by
    norm_num [pow_succ, mul_comm]
  rw [hcast, Real.log_pow] at hh
  have hlog2 : Real.log 2 ≤ 1 := by
    convert (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)) using 1 <;>
      norm_num
  have hj0 : 0 ≤ (j + 1 : ℝ) := by positivity
  calc
    (harmonic (2 * (2 ^ j)) : ℝ) ≤
        1 + (j + 1 : ℝ) * Real.log 2 := by simpa using hh
    _ ≤ 1 + (j + 1 : ℝ) * 1 := by gcongr
    _ = (j : ℝ) + 2 := by push_cast; ring

private theorem dyadic_rpow_neg_quarter (j : ℕ) :
    Real.rpow ((2 ^ j : ℕ) : ℝ) (-(1 / 4 : ℝ)) =
      (Real.rpow 2 (-(1 / 4 : ℝ))) ^ j := by
  rw [show (((2 ^ j : ℕ) : ℝ)) = (2 : ℝ) ^ j by norm_num]
  exact (Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)
    (-(1 / 4 : ℝ)) j).symm

private theorem sqrt_rpow_neg_half (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (Real.rpow x (-(1 / 2 : ℝ))) =
      Real.rpow x (-(1 / 4 : ℝ)) := by
  calc
    Real.sqrt (Real.rpow x (-(1 / 2 : ℝ))) =
        Real.rpow (Real.rpow x (-(1 / 2 : ℝ))) (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow _
    _ = Real.rpow x ((-(1 / 2 : ℝ)) * (1 / 2 : ℝ)) :=
      (Real.rpow_mul hx (-(1 / 2 : ℝ)) (1 / 2 : ℝ)).symm
    _ = Real.rpow x (-(1 / 4 : ℝ)) := by congr 1 <;> ring

private theorem longDyadicRootCost_le_geometric
    {D : ℝ} (hD : 0 ≤ D) (j : ℕ) :
    longDyadicRootCost D j ≤
      Real.sqrt (D + 8 * Real.pi) *
        ((j : ℝ) + 2) ^ 2 *
        (Real.rpow 2 (-(1 / 4 : ℝ))) ^ j := by
  let N : ℝ := ((2 ^ j : ℕ) : ℝ)
  let J : ℝ := (j : ℝ) + 2
  let K : ℝ := D + 8 * Real.pi
  have hN1 : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)) : 1 ≤ 2 ^ j)
  have hN0 : 0 ≤ N := hN1.trans' (by norm_num)
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN1
  have hJ0 : 0 ≤ J := by dsimp [J]; positivity
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg hD (mul_nonneg (by norm_num) Real.pi_pos.le)
  have hF : D + 8 * Real.pi * N ≤ K * N := by
    dsimp [K]
    nlinarith [mul_le_mul_of_nonneg_left hN1 hD]
  have hH := harmonic_two_pow_le j
  have hH0 : 0 ≤ (harmonic (2 * (2 ^ j)) : ℝ) := by
    exact_mod_cast (harmonic_pos (by positivity : 2 * (2 ^ j) ≠ 0)).le
  have hH4 : (harmonic (2 * (2 ^ j)) : ℝ) ^ 4 ≤ J ^ 4 := by
    dsimp [J]
    exact pow_le_pow_left₀ hH0 hH 4
  have hrpow0 : 0 ≤ Real.rpow N (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg hN0 _
  have hraw :
      (D + 8 * Real.pi * N) * Real.rpow N (-(3 / 2 : ℝ)) *
          (harmonic (2 * (2 ^ j)) : ℝ) ^ 4 ≤
        K * Real.rpow N (-(1 / 2 : ℝ)) * J ^ 4 := by
    calc
      _ ≤ (K * N) * Real.rpow N (-(3 / 2 : ℝ)) *
          (harmonic (2 * (2 ^ j)) : ℝ) ^ 4 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hF hrpow0) (by positivity)
      _ ≤ (K * N) * Real.rpow N (-(3 / 2 : ℝ)) * J ^ 4 := by
        exact mul_le_mul_of_nonneg_left hH4
          (mul_nonneg (mul_nonneg hK0 hN0) hrpow0)
      _ = K * Real.rpow N (-(1 / 2 : ℝ)) * J ^ 4 := by
        have hpow : N * Real.rpow N (-(3 / 2 : ℝ)) =
            Real.rpow N (-(1 / 2 : ℝ)) := by
          calc
            N * Real.rpow N (-(3 / 2 : ℝ)) =
                Real.rpow N (1 : ℝ) * Real.rpow N (-(3 / 2 : ℝ)) := by
              exact congrArg (fun x => x * Real.rpow N (-(3 / 2 : ℝ)))
                (Real.rpow_one N).symm
            _ = Real.rpow N (1 + (-(3 / 2 : ℝ))) :=
              (Real.rpow_add hNpos 1 (-(3 / 2 : ℝ))).symm
            _ = Real.rpow N (-(1 / 2 : ℝ)) := by norm_num
        calc
          K * N * Real.rpow N (-(3 / 2 : ℝ)) * J ^ 4 =
              K * (N * Real.rpow N (-(3 / 2 : ℝ))) * J ^ 4 := by ring
          _ = K * Real.rpow N (-(1 / 2 : ℝ)) * J ^ 4 := by rw [hpow]
  have hsqrt := Real.sqrt_le_sqrt hraw
  have hsqrtEq : Real.sqrt
      (K * Real.rpow N (-(1 / 2 : ℝ)) * J ^ 4) =
      Real.sqrt K * Real.rpow N (-(1 / 4 : ℝ)) * J ^ 2 := by
    calc
      Real.sqrt (K * Real.rpow N (-(1 / 2 : ℝ)) * J ^ 4) =
          Real.sqrt (K * (Real.rpow N (-(1 / 2 : ℝ)) * J ^ 4)) := by ring
      _ = Real.sqrt K *
          Real.sqrt (Real.rpow N (-(1 / 2 : ℝ)) * J ^ 4) :=
        Real.sqrt_mul hK0 _
      _ = Real.sqrt K *
          (Real.sqrt (Real.rpow N (-(1 / 2 : ℝ))) * Real.sqrt (J ^ 4)) := by
        congr 1
        exact Real.sqrt_mul (Real.rpow_nonneg hN0 (-(1 / 2 : ℝ))) _
      _ = Real.sqrt K * Real.rpow N (-(1 / 4 : ℝ)) * J ^ 2 := by
        rw [sqrt_rpow_neg_half N hN0,
          show J ^ 4 = (J ^ 2) ^ 2 by ring,
          Real.sqrt_sq (sq_nonneg J)]
        ring
  unfold longDyadicRootCost
  dsimp only
  change Real.sqrt
      ((D + 8 * Real.pi * N) * Real.rpow N (-(3 / 2 : ℝ)) *
        (harmonic (2 * (2 ^ j)) : ℝ) ^ 4) ≤ _
  rw [hsqrtEq] at hsqrt
  rw [dyadic_rpow_neg_quarter] at hsqrt
  dsimp [N, J, K] at hsqrt ⊢
  simpa [mul_assoc, mul_comm, mul_left_comm] using hsqrt

/-- Scale-sensitive version of the dyadic root estimate.  When the conductor
term `D` is at most `C` times the current cell scale, no spurious `sqrt D`
factor is introduced. -/
theorem longDyadicRootCost_le_geometric_of_le_mul_pow
    {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C) (j : ℕ)
    (hDC : D ≤ C * ((2 ^ j : ℕ) : ℝ)) :
    longDyadicRootCost D j ≤
      Real.sqrt (C + 8 * Real.pi) *
        ((j : ℝ) + 2) ^ 2 *
        (Real.rpow 2 (-(1 / 4 : ℝ))) ^ j := by
  let N : ℝ := ((2 ^ j : ℕ) : ℝ)
  let J : ℝ := (j : ℝ) + 2
  let K : ℝ := C + 8 * Real.pi
  have hN1 : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)) : 1 ≤ 2 ^ j)
  have hN0 : 0 ≤ N := hN1.trans' (by norm_num)
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN1
  have hJ0 : 0 ≤ J := by dsimp [J]; positivity
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg hC (mul_nonneg (by norm_num) Real.pi_pos.le)
  have hF : D + 8 * Real.pi * N ≤ K * N := by
    dsimp [K, N] at hDC ⊢
    nlinarith [mul_nonneg Real.pi_pos.le (by positivity : 0 ≤ ((2 ^ j : ℕ) : ℝ))]
  have hH := harmonic_two_pow_le j
  have hH0 : 0 ≤ (harmonic (2 * (2 ^ j)) : ℝ) := by
    exact_mod_cast (harmonic_pos (by positivity : 2 * (2 ^ j) ≠ 0)).le
  have hH4 : (harmonic (2 * (2 ^ j)) : ℝ) ^ 4 ≤ J ^ 4 := by
    dsimp [J]
    exact pow_le_pow_left₀ hH0 hH 4
  have hrpow0 : 0 ≤ Real.rpow N (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg hN0 _
  have hraw :
      (D + 8 * Real.pi * N) * Real.rpow N (-(3 / 2 : ℝ)) *
          (harmonic (2 * (2 ^ j)) : ℝ) ^ 4 ≤
        K * Real.rpow N (-(1 / 2 : ℝ)) * J ^ 4 := by
    calc
      _ ≤ (K * N) * Real.rpow N (-(3 / 2 : ℝ)) *
          (harmonic (2 * (2 ^ j)) : ℝ) ^ 4 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hF hrpow0) (by positivity)
      _ ≤ (K * N) * Real.rpow N (-(3 / 2 : ℝ)) * J ^ 4 := by
        exact mul_le_mul_of_nonneg_left hH4
          (mul_nonneg (mul_nonneg hK0 hN0) hrpow0)
      _ = K * Real.rpow N (-(1 / 2 : ℝ)) * J ^ 4 := by
        have hpow : N * Real.rpow N (-(3 / 2 : ℝ)) =
            Real.rpow N (-(1 / 2 : ℝ)) := by
          calc
            N * Real.rpow N (-(3 / 2 : ℝ)) =
                Real.rpow N (1 : ℝ) * Real.rpow N (-(3 / 2 : ℝ)) := by
              exact congrArg (fun x => x * Real.rpow N (-(3 / 2 : ℝ)))
                (Real.rpow_one N).symm
            _ = Real.rpow N (1 + (-(3 / 2 : ℝ))) :=
              (Real.rpow_add hNpos 1 (-(3 / 2 : ℝ))).symm
            _ = Real.rpow N (-(1 / 2 : ℝ)) := by norm_num
        rw [show K * N * Real.rpow N (-(3 / 2 : ℝ)) =
          K * (N * Real.rpow N (-(3 / 2 : ℝ))) by ring, hpow]
  have hsqrt := Real.sqrt_le_sqrt hraw
  have hsqrtEq : Real.sqrt
      (K * Real.rpow N (-(1 / 2 : ℝ)) * J ^ 4) =
      Real.sqrt K * Real.rpow N (-(1 / 4 : ℝ)) * J ^ 2 := by
    calc
      Real.sqrt (K * Real.rpow N (-(1 / 2 : ℝ)) * J ^ 4) =
          Real.sqrt (K * (Real.rpow N (-(1 / 2 : ℝ)) * J ^ 4)) := by ring
      _ = Real.sqrt K * Real.sqrt
          (Real.rpow N (-(1 / 2 : ℝ)) * J ^ 4) := Real.sqrt_mul hK0 _
      _ = Real.sqrt K *
          (Real.sqrt (Real.rpow N (-(1 / 2 : ℝ))) * Real.sqrt (J ^ 4)) := by
        congr 1
        exact Real.sqrt_mul (Real.rpow_nonneg hN0 _) _
      _ = Real.sqrt K * Real.rpow N (-(1 / 4 : ℝ)) * J ^ 2 := by
        rw [sqrt_rpow_neg_half N hN0,
          show J ^ 4 = (J ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg J)]
        ring
  unfold longDyadicRootCost
  dsimp only
  change Real.sqrt
      ((D + 8 * Real.pi * N) * Real.rpow N (-(3 / 2 : ℝ)) *
        (harmonic (2 * (2 ^ j)) : ℝ) ^ 4) ≤ _
  rw [hsqrtEq] at hsqrt
  rw [dyadic_rpow_neg_quarter] at hsqrt
  dsimp [N, J, K] at hsqrt ⊢
  simpa [mul_assoc, mul_comm, mul_left_comm] using hsqrt

/-- The square-root block costs are summable.  This is the exact scalar fact
needed for the infinite-shell Minkowski passage. -/
theorem summable_longDyadicRootCost {D : ℝ} (hD : 0 ≤ D) :
    Summable (longDyadicRootCost D) := by
  let r : ℝ := Real.rpow 2 (-(1 / 4 : ℝ))
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hgeom : Summable (fun j : ℕ => ((j : ℝ) + 2) ^ 2 * r ^ j) := by
    have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0
      (show ‖r‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
    have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (show ‖r‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
    have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
      (show ‖r‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
    have hsum := (h2.add (h1.mul_left 4)).add (h0.mul_left 4)
    convert hsum using 1
    funext j
    push_cast
    ring
  apply Summable.of_nonneg_of_le
    (fun j => Real.sqrt_nonneg _)
    (fun j => by
      have h := longDyadicRootCost_le_geometric hD j
      calc
        longDyadicRootCost D j ≤
            Real.sqrt (D + 8 * Real.pi) * ((j : ℝ) + 2) ^ 2 * r ^ j := by
          simpa only [r] using h
        _ = Real.sqrt (D + 8 * Real.pi) *
            (((j : ℝ) + 2) ^ 2 * r ^ j) := by ring)
    (hgeom.mul_left (Real.sqrt (D + 8 * Real.pi)))

/-- The universal polynomial-geometric tail mass. -/
def longDyadicTailMass : ℝ :=
  let r : ℝ := Real.rpow 2 (-(1 / 4 : ℝ))
  ∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * r ^ k

theorem longDyadicTailMass_nonneg : 0 ≤ longDyadicTailMass := by
  unfold longDyadicTailMass
  exact tsum_nonneg (fun k => mul_nonneg (sq_nonneg _)
    (pow_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) k))

theorem summable_longDyadicTailMajorant :
    let r : ℝ := Real.rpow 2 (-(1 / 4 : ℝ))
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * r ^ k) := by
  dsimp only
  let r : ℝ := Real.rpow 2 (-(1 / 4 : ℝ))
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0
    (show ‖r‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
    (show ‖r‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
    (show ‖r‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
  have hsum := (h2.add (h1.mul_left 2)).add h0
  convert hsum using 1
  funext k
  push_cast
  ring

/-- Quantitative shifted-tail form.  Starting the shell sum at `K` costs
exactly `2^{-K/4}` times a quadratic polynomial in `K`. -/
theorem tsum_longDyadicRootCost_natAdd_le
    {D : ℝ} (hD : 0 ≤ D) (K : ℕ) :
    (∑' k : ℕ, longDyadicRootCost D (k + K)) ≤
      Real.sqrt (D + 8 * Real.pi) * ((K : ℝ) + 2) ^ 2 *
        (Real.rpow 2 (-(1 / 4 : ℝ))) ^ K * longDyadicTailMass := by
  let r : ℝ := Real.rpow 2 (-(1 / 4 : ℝ))
  let C : ℝ := Real.sqrt (D + 8 * Real.pi) * ((K : ℝ) + 2) ^ 2 * r ^ K
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hroot : Summable (fun k : ℕ => longDyadicRootCost D (k + K)) :=
    (summable_nat_add_iff K).2 (summable_longDyadicRootCost hD)
  have htail := summable_longDyadicTailMajorant
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hmajor : Summable (fun k : ℕ => C * (((k : ℝ) + 1) ^ 2 * r ^ k)) :=
    htail.mul_left C
  have hpoint (k : ℕ) :
      longDyadicRootCost D (k + K) ≤
        C * (((k : ℝ) + 1) ^ 2 * r ^ k) := by
    have hbase := longDyadicRootCost_le_geometric hD (k + K)
    have hpoly : (((k + K : ℕ) : ℝ) + 2) ≤
        ((K : ℝ) + 2) * ((k : ℝ) + 1) := by
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      nlinarith [mul_nonneg hk0 hK0]
    have hpoly2 : (((k + K : ℕ) : ℝ) + 2) ^ 2 ≤
        (((K : ℝ) + 2) * ((k : ℝ) + 1)) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hpoly 2
    calc
      longDyadicRootCost D (k + K) ≤
          Real.sqrt (D + 8 * Real.pi) *
            (((k + K : ℕ) : ℝ) + 2) ^ 2 * r ^ (k + K) := by
        simpa only [r] using hbase
      _ ≤ Real.sqrt (D + 8 * Real.pi) *
            (((K : ℝ) + 2) * ((k : ℝ) + 1)) ^ 2 * r ^ (k + K) := by
        gcongr
      _ = C * (((k : ℝ) + 1) ^ 2 * r ^ k) := by
        dsimp [C]
        rw [pow_add]
        ring
  calc
    (∑' k : ℕ, longDyadicRootCost D (k + K)) ≤
        ∑' k : ℕ, C * (((k : ℝ) + 1) ^ 2 * r ^ k) :=
      hroot.tsum_le_tsum hpoint hmajor
    _ = C * (∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * r ^ k) := by
      rw [tsum_mul_left]
    _ = Real.sqrt (D + 8 * Real.pi) * ((K : ℝ) + 2) ^ 2 *
        (Real.rpow 2 (-(1 / 4 : ℝ))) ^ K * longDyadicTailMass := by
      rfl

end
end RamachandraLongDyadicScalarSummability

#print axioms RamachandraLongDyadicScalarSummability.summable_longDyadicRootCost
#print axioms RamachandraLongDyadicScalarSummability.tsum_longDyadicRootCost_natAdd_le
