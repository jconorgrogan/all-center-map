import GuthMaynardS3Assembly

set_option maxHeartbeats 800000

namespace GuthMaynardEnergy119FactorBound
noncomputable section
open GuthMaynardS3Source

private lemma sqrt_add_two_le_local {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := sqrt_add_two_le hx hy

/-- Direct scalar factor bound used in the Lemma 11.9 adapter.  All powers are
written as `Real.rpow` so that the endpoint absorptions are consumed literally. -/
theorem lemma11_9_scalar_factor_bound
    {T N R E : ℝ}
    (hT : 1 ≤ T) (hN : Real.rpow T (3 / 4 : ℝ) ≤ N)
    (hR : 1 ≤ R) (hElo : Real.rpow R (2 : ℝ) ≤ E)
    (hEhi : E ≤ Real.rpow R (3 : ℝ)) :
    Real.sqrt (Real.rpow R 1 * T + Real.rpow R 2 * N +
      Real.rpow R (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ) * N) *
      Real.sqrt (N * Real.rpow R 4 + E * T +
        Real.rpow E (3 / 4 : ℝ) * R * Real.rpow T (1 / 2 : ℝ) * N) ≤
      10 * (N * Real.rpow R 3 + N * Real.rpow T (1 / 4 : ℝ) *
        Real.rpow R (21 / 8 : ℝ) + N ^ 2 * Real.rpow R (1 / 2 : ℝ) *
          Real.rpow E (1 / 2 : ℝ)) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hR0 : 0 ≤ R := hRpos.le
  have hsR : Real.sqrt R = Real.rpow R (1 / 2 : ℝ) := by
    calc
      Real.sqrt R = Real.sqrt (Real.rpow R (1 : ℝ)) :=
        congrArg Real.sqrt (Real.rpow_one R).symm
      _ = Real.rpow R (1 / 2 : ℝ) := sqrt_rpow hR0
  have hNpos : 0 < N := lt_of_lt_of_le (Real.rpow_pos_of_pos hTpos _) hN
  have hEpos : 0 < E := lt_of_lt_of_le (Real.rpow_pos_of_pos hRpos (2 : ℝ)) hElo
  have hN1 : 1 ≤ N := by
    have hTpow1' : Real.rpow T (0 : ℝ) ≤ Real.rpow T (3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
    have hTpow1 : (1 : ℝ) ≤ Real.rpow T (3 / 4 : ℝ) := by
      calc
        (1 : ℝ) = Real.rpow T (0 : ℝ) := (Real.rpow_zero T).symm
        _ ≤ Real.rpow T (3 / 4 : ℝ) := hTpow1'
    exact hTpow1.trans hN
  let U : ℝ := Real.rpow R (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ) * N
  let V : ℝ := N * Real.rpow R 4
  let Q : ℝ := Real.rpow E (3 / 4 : ℝ) * R * Real.rpow T (1 / 2 : ℝ) * N
  let X : ℝ := N * Real.rpow R 3
  let Y : ℝ := N * Real.rpow T (1 / 4 : ℝ) * Real.rpow R (21 / 8 : ℝ)
  let Z : ℝ := N ^ 2 * Real.rpow R (1 / 2 : ℝ) * Real.rpow E (1 / 2 : ℝ)
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hY0 : 0 ≤ Y := by dsimp [Y]; positivity
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  rcases le_total R (Real.rpow T (2 / 3 : ℝ)) with hlow | hhigh
  · have hfac := lemma11_9_lowW_factor_absorptions
      (T := T) (W := R) (E := E) (N := N) hT hR hEpos hNpos.le hlow hEhi hN
    have hres := lemma11_9_lowW_residual_absorption
      (T := T) (W := R) (E := E) (N := N) hTpos hRpos hEpos hNpos
        hlow hElo hN
    have hRpow : R ≤ Real.rpow R (5 / 4 : ℝ) := by
      calc
        R = Real.rpow R (1 : ℝ) := (Real.rpow_one R).symm
        _ ≤ Real.rpow R (5 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
    have hTpowN : Real.rpow T (1 / 2 : ℝ) ≤ N :=
      (Real.rpow_le_rpow_of_exponent_le hT (by norm_num)).trans hN
    have hRT : Real.rpow R 1 * T ≤ U := by
      have hmul : Real.rpow R 1 * Real.rpow T (1 / 2 : ℝ) ≤
          Real.rpow R (5 / 4 : ℝ) * N := by
        have hr1 : Real.rpow R (1 : ℝ) = R := Real.rpow_one R
        calc
          Real.rpow R 1 * Real.rpow T (1 / 2 : ℝ) =
              R * Real.rpow T (1 / 2 : ℝ) := by rw [hr1]
          _ ≤ Real.rpow R (5 / 4 : ℝ) * N :=
            mul_le_mul hRpow hTpowN
              (Real.rpow_nonneg hTpos.le (1 / 2 : ℝ))
              (Real.rpow_nonneg hRpos.le (5 / 4 : ℝ))
      have hTsplit : T = Real.rpow T (1 / 2 : ℝ) * Real.rpow T (1 / 2 : ℝ) := by
        calc
          T = Real.rpow T (1 : ℝ) := (Real.rpow_one T).symm
          _ = Real.rpow T ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by norm_num
          _ = Real.rpow T (1 / 2 : ℝ) * Real.rpow T (1 / 2 : ℝ) :=
            Real.rpow_add hTpos _ _
      dsimp [U]
      calc
        Real.rpow R 1 * T = Real.rpow R 1 *
            (Real.rpow T (1 / 2 : ℝ) * Real.rpow T (1 / 2 : ℝ)) :=
          congrArg (fun x : ℝ => Real.rpow R 1 * x) hTsplit
        _ ≤ (Real.rpow R (5 / 4 : ℝ) * N) * Real.rpow T (1 / 2 : ℝ) := by
          have hnonT : 0 ≤ Real.rpow T (1 / 2 : ℝ) :=
            Real.rpow_nonneg hTpos.le (1 / 2 : ℝ)
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hmul hnonT
        _ = Real.rpow R (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ) * N := by ring
    have hR2N : Real.rpow R 2 * N ≤ U := by
      dsimp [U]
      calc
        Real.rpow R 2 * N ≤
            (Real.rpow R (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ)) * N :=
          mul_le_mul_of_nonneg_right hfac.1 hNpos.le
        _ = Real.rpow R (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ) * N := by ring
    have hA : Real.rpow R 1 * T + Real.rpow R 2 * N + U ≤ 3 * U := by
      calc
        Real.rpow R 1 * T + Real.rpow R 2 * N + U ≤ U + U + U := by
          exact add_le_add (add_le_add hRT hR2N) (le_refl U)
        _ = 3 * U := by ring
    have hET : E * T ≤ Q := by simpa [Q] using hfac.2
    have hB : V + E * T + Q ≤ V + 2 * Q := by
      dsimp [V]
      calc
        N * Real.rpow R 4 + E * T + Q ≤ N * Real.rpow R 4 + Q + Q := by gcongr
        _ = V + 2 * Q := by ring
    have hprod :
        Real.sqrt (Real.rpow R 1 * T + Real.rpow R 2 * N + U) *
          Real.sqrt (V + E * T + Q) ≤ Real.sqrt (3 * U) * Real.sqrt (V + 2 * Q) := by
      apply mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
      all_goals positivity
    have hsplit : Real.sqrt (V + 2 * Q) ≤ Real.sqrt V + Real.sqrt (2 * Q) := by
      exact sqrt_add_two_le_local hV0 (by positivity)
    have hrootU : Real.sqrt (3 * U) ≤ Real.sqrt 3 * Real.sqrt U := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hUV : Real.sqrt U * Real.sqrt V = Y := by
      dsimp [U, V, Y]
      change Real.sqrt ((Real.rpow R (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ)) * N) *
        Real.sqrt (N * Real.rpow R 4) =
        N * Real.rpow T (1 / 4 : ℝ) * Real.rpow R (21 / 8 : ℝ)
      rw [Real.sqrt_mul (x := Real.rpow R (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ))
        (mul_nonneg (Real.rpow_nonneg hRpos.le _) (Real.rpow_nonneg hTpos.le _))]
      rw [Real.sqrt_mul (x := Real.rpow R (5 / 4 : ℝ))
        (Real.rpow_nonneg hRpos.le _) (Real.rpow T (1 / 2 : ℝ))]
      rw [Real.sqrt_mul (x := N) (by positivity) (Real.rpow R 4)]
      rw [sqrt_rpow hRpos.le, sqrt_rpow hTpos.le]
      rw [sqrt_rpow hRpos.le]
      have hNsq : Real.sqrt N * Real.sqrt N = N := by
        nlinarith [Real.sq_sqrt hNpos.le]
      have hRexp : (5 / 4 : ℝ) / 2 = 5 / 8 := by norm_num
      have hTexp : (1 / 2 : ℝ) / 2 = 1 / 4 := by norm_num
      have hR4exp : (4 : ℝ) / 2 = 2 := by norm_num
      rw [hRexp, hTexp, hR4exp]
      calc
        Real.rpow R (5 / 8 : ℝ) * Real.rpow T (1 / 4 : ℝ) * Real.sqrt N *
            (Real.sqrt N * Real.rpow R 2) =
            (Real.sqrt N * Real.sqrt N) *
              (Real.rpow R (5 / 8 : ℝ) * Real.rpow R 2) *
              Real.rpow T (1 / 4 : ℝ) := by ring
        _ = N * (Real.rpow R (5 / 8 : ℝ) * Real.rpow R 2) *
              Real.rpow T (1 / 4 : ℝ) := by rw [hNsq]
        _ = N * Real.rpow T (1 / 4 : ℝ) * Real.rpow R (21 / 8 : ℝ) := by
          have hRsum : Real.rpow R (5 / 8 : ℝ) * Real.rpow R 2 =
              Real.rpow R (21 / 8 : ℝ) := by
            calc
              _ = Real.rpow R ((5 / 8 : ℝ) + 2) :=
                (Real.rpow_add hRpos _ _).symm
              _ = Real.rpow R (21 / 8 : ℝ) := by norm_num
          rw [hRsum]
          ring
    have hUQ : Real.sqrt U * Real.sqrt Q ≤ Z := by
      have hUQeq : Real.sqrt U * Real.sqrt Q =
          N * Real.rpow R (9 / 8 : ℝ) * Real.rpow T (1 / 2 : ℝ) *
            Real.rpow E (3 / 8 : ℝ) := by
        dsimp [U, Q]
        change Real.sqrt ((Real.rpow R (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ)) * N) *
          Real.sqrt ((Real.rpow E (3 / 4 : ℝ) * R * Real.rpow T (1 / 2 : ℝ)) * N) = _
        rw [Real.sqrt_mul (x := Real.rpow R (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ))
          (mul_nonneg (Real.rpow_nonneg hRpos.le _) (Real.rpow_nonneg hTpos.le _))]
        rw [Real.sqrt_mul (x := Real.rpow R (5 / 4 : ℝ))
          (Real.rpow_nonneg hRpos.le _) (Real.rpow T (1 / 2 : ℝ))]
        change Real.sqrt (Real.rpow R (5 / 4 : ℝ)) * Real.sqrt (Real.rpow T (1 / 2 : ℝ)) * Real.sqrt N *
          Real.sqrt (((Real.rpow E (3 / 4 : ℝ) * R) * Real.rpow T (1 / 2 : ℝ)) * N) = _
        have hqsplit :
            Real.sqrt (((Real.rpow E (3 / 4 : ℝ) * R) * Real.rpow T (1 / 2 : ℝ)) * N) =
              Real.sqrt ((Real.rpow E (3 / 4 : ℝ) * R) * Real.rpow T (1 / 2 : ℝ)) * Real.sqrt N :=
          Real.sqrt_mul (x := (Real.rpow E (3 / 4 : ℝ) * R) * Real.rpow T (1 / 2 : ℝ))
            (mul_nonneg (mul_nonneg (Real.rpow_nonneg hEpos.le _) hR0)
              (Real.rpow_nonneg hTpos.le _)) N
        rw [hqsplit]
        have hqsplit2 :
            Real.sqrt ((Real.rpow E (3 / 4 : ℝ) * R) * Real.rpow T (1 / 2 : ℝ)) =
              Real.sqrt (Real.rpow E (3 / 4 : ℝ) * R) *
                Real.sqrt (Real.rpow T (1 / 2 : ℝ)) :=
          Real.sqrt_mul (x := (Real.rpow E (3 / 4 : ℝ) * R))
            (mul_nonneg (Real.rpow_nonneg hEpos.le _) hR0)
            (Real.rpow T (1 / 2 : ℝ))
        rw [hqsplit2]
        have hesplit : Real.sqrt (Real.rpow E (3 / 4 : ℝ) * R) =
            Real.sqrt (Real.rpow E (3 / 4 : ℝ)) * Real.sqrt R :=
          Real.sqrt_mul (x := Real.rpow E (3 / 4 : ℝ)) (Real.rpow_nonneg hEpos.le _) R
        rw [hesplit]
        rw [sqrt_rpow hRpos.le, sqrt_rpow hTpos.le, sqrt_rpow hEpos.le]
        have hNsq : Real.sqrt N * Real.sqrt N = N := by
          simpa [pow_two] using Real.sq_sqrt hNpos.le
        have hRexp : (5 / 4 : ℝ) / 2 = 5 / 8 := by norm_num
        have hTexp : (1 / 2 : ℝ) / 2 = 1 / 4 := by norm_num
        have hEexp : (3 / 4 : ℝ) / 2 = 3 / 8 := by norm_num
        rw [hRexp, hTexp, hEexp]
        have hRsum : Real.rpow R (5 / 8 : ℝ) * Real.rpow R (1 / 2 : ℝ) =
            Real.rpow R (9 / 8 : ℝ) := by
          calc
            _ = Real.rpow R ((5 / 8 : ℝ) + 1 / 2) :=
              (Real.rpow_add hRpos _ _).symm
            _ = Real.rpow R (9 / 8 : ℝ) := by norm_num
        have hTsum : Real.rpow T (1 / 4 : ℝ) * Real.rpow T (1 / 4 : ℝ) =
            Real.rpow T (1 / 2 : ℝ) := by
          calc
            _ = Real.rpow T ((1 / 4 : ℝ) + 1 / 4) :=
              (Real.rpow_add hTpos _ _).symm
            _ = Real.rpow T (1 / 2 : ℝ) := by norm_num
        calc
          Real.rpow R (5 / 8 : ℝ) * Real.rpow T (1 / 4 : ℝ) * Real.sqrt N *
              (Real.rpow E (3 / 8 : ℝ) * Real.sqrt R * Real.rpow T (1 / 4 : ℝ) * Real.sqrt N) =
              (Real.sqrt N * Real.sqrt N) *
                (Real.rpow R (5 / 8 : ℝ) * Real.sqrt R) *
                (Real.rpow T (1 / 4 : ℝ) * Real.rpow T (1 / 4 : ℝ)) *
                Real.rpow E (3 / 8 : ℝ) := by ring
          _ = N * (Real.rpow R (5 / 8 : ℝ) * Real.rpow R (1 / 2 : ℝ)) *
                (Real.rpow T (1 / 4 : ℝ) * Real.rpow T (1 / 4 : ℝ)) *
                Real.rpow E (3 / 8 : ℝ) := by rw [hNsq, hsR]
          _ = N * Real.rpow R (9 / 8 : ℝ) * Real.rpow T (1 / 2 : ℝ) *
                Real.rpow E (3 / 8 : ℝ) := by rw [hRsum, hTsum]
      have hK : 0 ≤ N * Real.rpow R (1 / 2 : ℝ) * Real.rpow E (3 / 8 : ℝ) :=
        mul_nonneg (mul_nonneg hNpos.le (Real.rpow_nonneg hRpos.le _))
          (Real.rpow_nonneg hEpos.le _)
      calc
        Real.sqrt U * Real.sqrt Q =
            (Real.rpow T (1 / 2 : ℝ) * Real.rpow R (5 / 8 : ℝ)) *
              (N * Real.rpow R (1 / 2 : ℝ) * Real.rpow E (3 / 8 : ℝ)) := by
                have hRsum : Real.rpow R (5 / 8 : ℝ) * Real.rpow R (1 / 2 : ℝ) =
                    Real.rpow R (9 / 8 : ℝ) := by
                  calc
                    _ = Real.rpow R ((5 / 8 : ℝ) + 1 / 2) :=
                      (Real.rpow_add hRpos _ _).symm
                    _ = Real.rpow R (9 / 8 : ℝ) := by norm_num
                rw [hUQeq, ← hRsum]
                ring
        _ ≤ (Real.rpow E (1 / 8 : ℝ) * N) *
              (N * Real.rpow R (1 / 2 : ℝ) * Real.rpow E (3 / 8 : ℝ)) :=
          mul_le_mul_of_nonneg_right hres hK
        _ = Z := by
          have hEadd : Real.rpow E (1 / 8 : ℝ) * Real.rpow E (3 / 8 : ℝ) =
              Real.rpow E (1 / 2 : ℝ) := by
            calc
              _ = Real.rpow E ((1 / 8 : ℝ) + 3 / 8) :=
                (Real.rpow_add hEpos _ _).symm
              _ = Real.rpow E (1 / 2 : ℝ) := by norm_num
          calc
            (Real.rpow E (1 / 8 : ℝ) * N) *
                (N * Real.rpow R (1 / 2 : ℝ) * Real.rpow E (3 / 8 : ℝ)) =
                N ^ 2 * Real.rpow R (1 / 2 : ℝ) *
                  (Real.rpow E (1 / 8 : ℝ) * Real.rpow E (3 / 8 : ℝ)) := by ring
            _ = Z := by rw [hEadd]
    have hs2 : Real.sqrt (2 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    have hs3 : Real.sqrt (3 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
    have hsmall : Real.sqrt (3 * U) * Real.sqrt (V + 2 * Q) ≤
        10 * (X + Y + Z) := by
      have hmain : Real.sqrt 3 * Real.sqrt U *
            (Real.sqrt V + Real.sqrt 2 * Real.sqrt Q) ≤
          Real.sqrt 3 * Y + Real.sqrt 3 * Real.sqrt 2 * Z := by
        calc
          _ = Real.sqrt 3 * (Real.sqrt U * Real.sqrt V) +
              Real.sqrt 3 * Real.sqrt 2 * (Real.sqrt U * Real.sqrt Q) := by ring
          _ ≤ Real.sqrt 3 * Y + Real.sqrt 3 * Real.sqrt 2 * Z := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hUV.le (by positivity))
              (mul_le_mul_of_nonneg_left hUQ (by positivity))
      calc
        Real.sqrt (3 * U) * Real.sqrt (V + 2 * Q) ≤
            Real.sqrt (3 * U) * (Real.sqrt V + Real.sqrt (2 * Q)) :=
          mul_le_mul_of_nonneg_left hsplit (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt 3 * Real.sqrt U *
            (Real.sqrt V + Real.sqrt 2 * Real.sqrt Q) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
          exact mul_le_mul_of_nonneg_right hrootU (by positivity)
        _ ≤ Real.sqrt 3 * Y + Real.sqrt 3 * Real.sqrt 2 * Z := hmain
        _ ≤ 10 * (X + Y + Z) := by
          have h32 : Real.sqrt 3 * Real.sqrt 2 ≤ 4 := by
            have hmul := mul_le_mul hs3 hs2 (Real.sqrt_nonneg (2 : ℝ)) (by positivity)
            convert hmul using 1 <;> norm_num
          have hcoef : Real.sqrt 3 * Y + Real.sqrt 3 * Real.sqrt 2 * Z ≤
              2 * Y + 4 * Z := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hs3 hY0)
              (mul_le_mul_of_nonneg_right h32 hZ0)
          calc
            Real.sqrt 3 * Y + Real.sqrt 3 * Real.sqrt 2 * Z ≤ 2 * Y + 4 * Z := hcoef
            _ ≤ 10 * (X + Y + Z) := by nlinarith [hX0, hY0, hZ0]
    calc
      _ ≤ Real.sqrt (3 * U) * Real.sqrt (V + 2 * Q) := hprod
      _ ≤ 10 * (X + Y + Z) := hsmall
      _ = 10 * (N * Real.rpow R 3 + N * Real.rpow T (1 / 4 : ℝ) *
          Real.rpow R (21 / 8 : ℝ) + N ^ 2 * Real.rpow R (1 / 2 : ℝ) *
            Real.rpow E (1 / 2 : ℝ)) := by rfl
  · have hfac := lemma11_9_highW_factor_absorptions
      (T := T) (W := R) (E := E) (N := N) hTpos hRpos hEpos.le hNpos.le hhigh hEhi
    have htime := lemma11_9_highW_energy_time_absorption
      (T := T) (W := R) (E := E) (N := N) hT hRpos hEpos.le hNpos.le hhigh hN hEhi
    have hTthird : Real.rpow T (1 / 3 : ℝ) ≤ N :=
      (Real.rpow_le_rpow_of_exponent_le hT (by norm_num)).trans hN
    have hTN : T ≤ N * R := by
      have hmul := mul_le_mul hTthird hhigh
        (Real.rpow_nonneg hTpos.le _) hNpos.le
      calc
        T = Real.rpow T (1 : ℝ) := (Real.rpow_one T).symm
        _ = Real.rpow T ((1 / 3 : ℝ) + 2 / 3) := by norm_num
        _ = Real.rpow T (1 / 3 : ℝ) * Real.rpow T (2 / 3 : ℝ) :=
          Real.rpow_add hTpos _ _
        _ ≤ N * R := hmul
    have hR2eq : Real.rpow R (2 : ℝ) = R * R := by
      calc
        Real.rpow R (2 : ℝ) = Real.rpow R ((1 : ℝ) + 1) := by norm_num
        _ = Real.rpow R (1 : ℝ) * Real.rpow R (1 : ℝ) :=
          Real.rpow_add hRpos _ _
        _ = R * R := by
          exact congrArg₂ (fun x y : ℝ => x * y) (Real.rpow_one R) (Real.rpow_one R)
    have hRT : Real.rpow R 1 * T ≤ Real.rpow R 2 * N := by
      have hmul := mul_le_mul_of_nonneg_left hTN hR0
      calc
        Real.rpow R 1 * T = R * T :=
          congrArg (fun x : ℝ => x * T) (Real.rpow_one R)
        _ ≤ R * (N * R) := hmul
        _ = Real.rpow R 2 * N := by rw [hR2eq]; ring
    have hUhigh : U ≤ Real.rpow R 2 * N := by
      dsimp [U]
      exact mul_le_mul_of_nonneg_right hfac.1 hNpos.le
    have hA : Real.rpow R 1 * T + Real.rpow R 2 * N + U ≤
        3 * (Real.rpow R 2 * N) := by
      calc
        Real.rpow R 1 * T + Real.rpow R 2 * N + U ≤
            Real.rpow R 2 * N + Real.rpow R 2 * N + Real.rpow R 2 * N := by
          exact add_le_add (add_le_add hRT (le_refl _)) hUhigh
        _ = 3 * (Real.rpow R 2 * N) := by ring
    have hET : E * T ≤ N * Real.rpow R 4 := htime
    have hQ : Q ≤ N * Real.rpow R 4 := by simpa [Q] using hfac.2
    have hB : V + E * T + Q ≤ 3 * V := by
      calc
        V + E * T + Q ≤ V + V + V := by
          exact add_le_add (add_le_add (le_refl V) hET) hQ
        _ = 3 * V := by dsimp [V]; ring
    have hprod :
        Real.sqrt (Real.rpow R 1 * T + Real.rpow R 2 * N + U) *
          Real.sqrt (V + E * T + Q) ≤
        Real.sqrt (3 * (Real.rpow R 2 * N)) * Real.sqrt (3 * V) := by
      apply mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
      all_goals positivity
    have hWV : Real.sqrt (Real.rpow R 2 * N) * Real.sqrt V = X := by
      dsimp [V, X]
      change Real.sqrt (Real.rpow R 2 * N) * Real.sqrt (N * Real.rpow R 4) =
        N * Real.rpow R 3
      have hs1 : Real.sqrt (Real.rpow R 2 * N) =
          Real.sqrt (Real.rpow R 2) * Real.sqrt N :=
        Real.sqrt_mul (Real.rpow_nonneg hRpos.le _) N
      have hs2 : Real.sqrt (N * Real.rpow R 4) =
          Real.sqrt N * Real.sqrt (Real.rpow R 4) :=
        Real.sqrt_mul (by positivity) (Real.rpow R 4)
      rw [hs1, hs2, sqrt_rpow hRpos.le]
      have hR2exp : (2 : ℝ) / 2 = 1 := by norm_num
      rw [hR2exp]
      have hNsq : Real.sqrt N * Real.sqrt N = N := by
        simpa [pow_two] using Real.sq_sqrt hNpos.le
      have hRsum : Real.rpow R 1 * Real.rpow R 2 = Real.rpow R 3 := by
        calc
          _ = Real.rpow R ((1 : ℝ) + 2) := (Real.rpow_add hRpos _ _).symm
          _ = Real.rpow R 3 := by norm_num
      rw [sqrt_rpow hRpos.le]
      calc
        Real.rpow R 1 * Real.sqrt N * (Real.sqrt N * Real.rpow R (4 / 2 : ℝ)) =
            Real.rpow R 1 * (Real.sqrt N * Real.sqrt N) * Real.rpow R (4 / 2 : ℝ) := by ring
        _ = N * (Real.rpow R 1 * Real.rpow R 2) := by
          rw [hNsq]
          have hR4exp : (4 : ℝ) / 2 = 2 := by norm_num
          rw [hR4exp]
          ring
        _ = N * Real.rpow R 3 := by rw [hRsum]
        _ = X := by rfl
    have hhighsmall : Real.sqrt (3 * (Real.rpow R 2 * N)) * Real.sqrt (3 * V) ≤
        10 * (X + Y + Z) := by
      have hmain : Real.sqrt 3 * Real.sqrt 3 *
          (Real.sqrt (Real.rpow R 2 * N) * Real.sqrt V) ≤ 4 * X := by
        rw [hWV]
        have hs33 : Real.sqrt 3 * Real.sqrt 3 ≤ 4 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
            Real.sqrt_nonneg (3 : ℝ)]
        exact mul_le_mul_of_nonneg_right hs33 hX0
      calc
        Real.sqrt (3 * (Real.rpow R 2 * N)) * Real.sqrt (3 * V) =
            Real.sqrt 3 * Real.sqrt 3 *
              (Real.sqrt (Real.rpow R 2 * N) * Real.sqrt V) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3),
            Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
          ring
        _ ≤ 4 * X := hmain
        _ ≤ 10 * (X + Y + Z) := by nlinarith [hX0, hY0, hZ0]
    calc
      _ ≤ Real.sqrt (3 * (Real.rpow R 2 * N)) * Real.sqrt (3 * V) := hprod
      _ ≤ 10 * (X + Y + Z) := hhighsmall
      _ = 10 * (N * Real.rpow R 3 + N * Real.rpow T (1 / 4 : ℝ) *
          Real.rpow R (21 / 8 : ℝ) + N ^ 2 * Real.rpow R (1 / 2 : ℝ) *
            Real.rpow E (1 / 2 : ℝ)) := by rfl


end
end GuthMaynardEnergy119FactorBound

#print axioms GuthMaynardEnergy119FactorBound.lemma11_9_scalar_factor_bound
