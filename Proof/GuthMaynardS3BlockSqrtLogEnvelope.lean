import GuthMaynardS3DyadicLogLoss
import GuthMaynardS3CubicHorizonTail

open scoped Real
noncomputable section
namespace GuthMaynardS3BlockSqrtLogEnvelope

open GuthMaynardS3DyadicLogLoss GuthMaynardS3CubicHorizonTail

private theorem rpow_nat_mul {T delta : ℝ} (hT : 0 ≤ T) (m : ℕ) :
    (Real.rpow T delta) ^ m = Real.rpow T (delta * (m : ℝ)) := by
  exact (Real.rpow_mul_natCast hT delta m).symm

private theorem sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hs : 0 ≤ Real.sqrt a + Real.sqrt b := by positivity
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) hs).mp
  rw [Real.sq_sqrt (add_nonneg ha hb), add_sq]
  rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
  nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

private theorem sqrt_eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsq : a = b ^ 2) : Real.sqrt a = b := by
  have hleft : Real.sqrt a ^ 2 = b ^ 2 := by
    rw [Real.sq_sqrt ha]
    exact hsq
  have h1 : Real.sqrt a ≤ b := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hb).mp
    exact le_of_eq hleft
  have h2 : b ≤ Real.sqrt a := by
    apply (sq_le_sq₀ hb (Real.sqrt_nonneg _)).mp
    exact le_of_eq hleft.symm
  exact le_antisymm h1 h2

private theorem sqrt_rpow_nine {T eta : ℝ} (hT : 0 ≤ T) :
    Real.sqrt ((Real.rpow T eta) ^ (9 : ℕ)) =
      Real.rpow T (9 * eta / 2) := by
  rw [Real.sqrt_eq_rpow]
  calc
    ((Real.rpow T eta) ^ (9 : ℕ)) ^ (1 / 2 : ℝ) =
        (Real.rpow T (eta * (9 : ℝ))) ^ (1 / 2 : ℝ) := by
          rw [rpow_nat_mul hT 9]
          norm_num
    _ = Real.rpow T (eta * (9 : ℝ) * (1 / 2 : ℝ)) :=
      (Real.rpow_mul hT _ _).symm
    _ = Real.rpow T (9 * eta / 2) := by congr 1 <;> ring

private theorem sqrt_T4_R3 {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Real.sqrt (T ^ (4 : ℕ) * R ^ (3 : ℕ)) =
      T ^ (2 : ℕ) * Real.rpow R (3 / 2 : ℝ) := by
  have hA : 0 ≤ T ^ (4 : ℕ) * R ^ (3 : ℕ) := by positivity
  have hB : 0 ≤ T ^ (2 : ℕ) * Real.rpow R (3 / 2 : ℝ) :=
    mul_nonneg (pow_nonneg hT _) (Real.rpow_nonneg hR _)
  have hsq : T ^ (4 : ℕ) * R ^ (3 : ℕ) =
      (T ^ (2 : ℕ) * Real.rpow R (3 / 2 : ℝ)) ^ 2 := by
    have hRp : (Real.rpow R (3 / 2 : ℝ)) ^ (2 : ℕ) = R ^ (3 : ℕ) := by
      calc
        _ = Real.rpow R ((3 / 2 : ℝ) * (2 : ℝ)) := rpow_nat_mul hR 2
        _ = R ^ (3 : ℕ) := by
          have he : (3 / 2 : ℝ) * (2 : ℝ) = 3 := by norm_num
          rw [he]
          exact Real.rpow_natCast R 3
    calc
      _ = (T ^ (2 : ℕ)) ^ 2 * R ^ (3 : ℕ) := by ring
      _ = (T ^ (2 : ℕ)) ^ 2 * (Real.rpow R (3 / 2 : ℝ)) ^ 2 := by rw [hRp]
      _ = _ := by ring
  exact sqrt_eq_of_sq_eq hA hB hsq

private theorem sqrt_T2_n2_RE {T n R E : ℝ} (hT : 0 ≤ T) (hn : 0 ≤ n)
    (hR : 0 ≤ R) (hE : 0 ≤ E) :
    Real.sqrt (T ^ (2 : ℕ) * n ^ (2 : ℕ) * R * E) =
      T * n * Real.sqrt R * Real.sqrt E := by
  have hA : 0 ≤ T ^ (2 : ℕ) * n ^ (2 : ℕ) * R * E := by positivity
  have hB : 0 ≤ T * n * Real.sqrt R * Real.sqrt E := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hT (by positivity))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hsq : T ^ (2 : ℕ) * n ^ (2 : ℕ) * R * E =
      (T * n * Real.sqrt R * Real.sqrt E) ^ 2 := by
    calc
      _ = (T ^ 2) * (n ^ 2) * (Real.sqrt R) ^ 2 *
          (Real.sqrt E) ^ 2 := by rw [Real.sq_sqrt hR, Real.sq_sqrt hE]
      _ = _ := by ring
  exact sqrt_eq_of_sq_eq hA hB hsq

/-- Scalar square-root envelope for a selected dyadic block. -/
theorem block_sqrt_log_envelope
    {T eta R E n Cm Ct X : ℝ} {k : ℕ}
    (hT : 1 ≤ T) (heta : 0 < eta) (hK : (2 : ℝ) ^ k ≤ T ^ 2)
    (hR : 0 ≤ R) (hE : 0 ≤ E) (hn : 0 ≤ n)
    (hCm : 0 ≤ Cm) (hCt : 0 ≤ Ct)
    (hX : X ^ 2 ≤
      Cm * (Real.rpow T eta) ^ 9 * (k + 7 : ℝ) ^ 2 *
          (T ^ 4 * R ^ 3 + T ^ 2 * n ^ 2 * R * E) +
        Ct * Real.rpow T (-282 : ℝ)) :
    (1 + Real.log T) ^ 2 * |X| ≤
      Real.sqrt Cm * ((7 + 2 / Real.log 2) * (1 + 3 / eta) ^ 3) *
          Real.rpow T (6 * eta) *
            (T ^ 2 * Real.rpow R (3 / 2 : ℝ) +
              T * n * Real.sqrt R * Real.sqrt E) +
        Real.sqrt Ct * Real.rpow T (-100 : ℝ) := by
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT0 : 0 ≤ T := hTp.le
  have hL0 : 0 ≤ (k + 7 : ℝ) := by positivity
  have hQ0 : 0 ≤ T ^ 4 * R ^ 3 + T ^ 2 * n ^ 2 * R * E := by positivity
  have htail0 : 0 ≤ Ct * Real.rpow T (-282 : ℝ) :=
    mul_nonneg hCt (Real.rpow_nonneg hT0 _)
  have hmain0 : 0 ≤
      Cm * (Real.rpow T eta) ^ 9 * (k + 7 : ℝ) ^ 2 *
        (T ^ 4 * R ^ 3 + T ^ 2 * n ^ 2 * R * E) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hCm
      (pow_nonneg (Real.rpow_nonneg hT0 eta) 9)) (sq_nonneg (k + 7 : ℝ))) (by positivity)
  have hsum0 : 0 ≤
      Cm * (Real.rpow T eta) ^ 9 * (k + 7 : ℝ) ^ 2 *
          (T ^ 4 * R ^ 3 + T ^ 2 * n ^ 2 * R * E) +
        Ct * Real.rpow T (-282 : ℝ) := add_nonneg hmain0 htail0
  have habs : |X| ≤ Real.sqrt (Cm * (Real.rpow T eta) ^ 9 *
      (k + 7 : ℝ) ^ 2 *
          (T ^ 4 * R ^ 3 + T ^ 2 * n ^ 2 * R * E)) +
      Real.sqrt (Ct * Real.rpow T (-282 : ℝ)) := by
    rw [← Real.sqrt_sq_eq_abs]
    calc
      Real.sqrt (X ^ 2) ≤ Real.sqrt (Cm * (Real.rpow T eta) ^ 9 *
          (k + 7 : ℝ) ^ 2 *
            (T ^ 4 * R ^ 3 + T ^ 2 * n ^ 2 * R * E) +
          Ct * Real.rpow T (-282 : ℝ)) := Real.sqrt_le_sqrt hX
      _ ≤ _ := sqrt_add_le hmain0 htail0
  have hq := selection_and_bin_log_loss hT heta hK
  let B : ℝ := T ^ 2 * Real.rpow R (3 / 2 : ℝ) +
      T * n * Real.sqrt R * Real.sqrt E
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg
      (mul_nonneg (sq_nonneg T) (Real.rpow_nonneg hR _))
      (mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  have hqbound : T ^ 4 * R ^ 3 + T ^ 2 * n ^ 2 * R * E ≤ B ^ 2 := by
    have hcross : 0 ≤ 2 * (T ^ 2 * Real.rpow R (3 / 2 : ℝ)) *
        (T * n * Real.sqrt R * Real.sqrt E) := by
      have hTn : 0 ≤ T * n := mul_nonneg hT0 hn
      have hTnR : 0 ≤ T * n * Real.sqrt R :=
        mul_nonneg hTn (Real.sqrt_nonneg _)
      exact mul_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg (sq_nonneg T) (Real.rpow_nonneg hR _)))
        (mul_nonneg hTnR (Real.sqrt_nonneg _))
    have hsquares :
        (T ^ 2 * Real.rpow R (3 / 2 : ℝ)) ^ 2 = T ^ 4 * R ^ 3 := by
      have hs := sqrt_T4_R3 hT0 hR
      calc
        _ = (Real.sqrt (T ^ 4 * R ^ 3)) ^ 2 := by rw [hs]
        _ = _ := Real.sq_sqrt (by positivity)
    have hsquares2 :
        (T * n * Real.sqrt R * Real.sqrt E) ^ 2 =
          T ^ 2 * n ^ 2 * R * E := by
      have hs := sqrt_T2_n2_RE hT0 hn hR hE
      calc
        _ = (Real.sqrt (T ^ 2 * n ^ 2 * R * E)) ^ 2 := by rw [hs]
        _ = _ := Real.sq_sqrt (by positivity)
    dsimp [B]
    have htmp :
        T ^ 4 * R ^ 3 + T ^ 2 * n ^ 2 * R * E ≤
          (T ^ 2 * Real.rpow R (3 / 2 : ℝ)) ^ 2 +
            2 * (T ^ 2 * Real.rpow R (3 / 2 : ℝ)) *
              (T * n * Real.sqrt R * Real.sqrt E) +
            (T * n * Real.sqrt R * Real.sqrt E) ^ 2 := by
      rw [hsquares, hsquares2]
      nlinarith [hcross]
    calc
      _ ≤ (T ^ 2 * Real.rpow R (3 / 2 : ℝ)) ^ 2 +
          2 * (T ^ 2 * Real.rpow R (3 / 2 : ℝ)) *
            (T * n * Real.sqrt R * Real.sqrt E) +
          (T * n * Real.sqrt R * Real.sqrt E) ^ 2 := htmp
      _ = (T ^ 2 * Real.rpow R (3 / 2 : ℝ) +
          T * n * Real.sqrt R * Real.sqrt E) ^ 2 := by ring
  have hrootQ : Real.sqrt (T ^ 4 * R ^ 3 + T ^ 2 * n ^ 2 * R * E) ≤ B := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hB0).mp
    rw [Real.sq_sqrt hQ0]
    exact hqbound
  have ht9 : 0 ≤ (Real.rpow T eta) ^ 9 := pow_nonneg (Real.rpow_nonneg hT0 eta) 9
  have hmainroot : Real.sqrt (Cm * (Real.rpow T eta) ^ 9 *
      (k + 7 : ℝ) ^ 2 *
          (T ^ 4 * R ^ 3 + T ^ 2 * n ^ 2 * R * E)) ≤
      Real.sqrt Cm * Real.rpow T (9 * eta / 2) * (k + 7 : ℝ) * B := by
    have hright : 0 ≤ Real.sqrt Cm * Real.rpow T (9 * eta / 2) *
        (k + 7 : ℝ) * B := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (Real.rpow_nonneg hT0 _)) (by positivity)) hB0
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hright).mp
    rw [Real.sq_sqrt hmain0]
    have hsqrtCm : (Real.sqrt Cm) ^ 2 = Cm := Real.sq_sqrt hCm
    have hsqrtT : (Real.rpow T (9 * eta / 2)) ^ 2 =
        (Real.rpow T eta) ^ 9 := by
      calc
        _ = Real.rpow T ((9 * eta / 2) * (2 : ℝ)) := rpow_nat_mul hT0 2
        _ = Real.rpow T (eta * (9 : ℝ)) := by congr 1 <;> ring
        _ = _ := (rpow_nat_mul hT0 9).symm
    have hrightsq :
        (Real.sqrt Cm * Real.rpow T (9 * eta / 2) *
          (k + 7 : ℝ) * B) ^ 2 =
          Cm * (Real.rpow T eta) ^ 9 * (k + 7 : ℝ) ^ 2 * B ^ 2 := by
      calc
        _ = (Real.sqrt Cm) ^ 2 *
            (Real.rpow T (9 * eta / 2)) ^ 2 *
            (k + 7 : ℝ) ^ 2 * B ^ 2 := by ring
        _ = _ := by rw [hsqrtCm, hsqrtT]
    rw [hrightsq]
    have hcoef : 0 ≤ Cm * (Real.rpow T eta) ^ 9 * (k + 7 : ℝ) ^ 2 := by
      positivity
    exact mul_le_mul_of_nonneg_left hqbound hcoef
  have hmainlog :
      (1 + Real.log T) ^ 2 *
          Real.sqrt (Cm * (Real.rpow T eta) ^ 9 *
            (k + 7 : ℝ) ^ 2 *
              (T ^ 4 * R ^ 3 + T ^ 2 * n ^ 2 * R * E)) ≤
      Real.sqrt Cm * ((7 + 2 / Real.log 2) * (1 + 3 / eta) ^ 3) *
          Real.rpow T (6 * eta) * B := by
    have hlog0 : 0 ≤ (1 + Real.log T) ^ 2 := sq_nonneg _
    have hcoef0 : 0 ≤ Real.sqrt Cm := Real.sqrt_nonneg _
    calc
      _ ≤ (1 + Real.log T) ^ 2 *
          (Real.sqrt Cm * Real.rpow T (9 * eta / 2) *
            (k + 7 : ℝ) * B) :=
        mul_le_mul_of_nonneg_left hmainroot hlog0
      _ ≤ Real.sqrt Cm * Real.rpow T (9 * eta / 2) * B *
          (((7 + 2 / Real.log 2) * (1 + 3 / eta) ^ 3) *
            Real.rpow T eta) := by
        have hfac : 0 ≤ Real.sqrt Cm * Real.rpow T (9 * eta / 2) * B := by
          exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
            (Real.rpow_nonneg hT0 _)) hB0
        calc
          _ = (Real.sqrt Cm * Real.rpow T (9 * eta / 2) * B) *
              ((1 + Real.log T) ^ 2 * (k + 7 : ℝ)) := by ring
          _ ≤ (Real.sqrt Cm * Real.rpow T (9 * eta / 2) * B) *
              (((7 + 2 / Real.log 2) * (1 + 3 / eta) ^ 3) *
                Real.rpow T eta) :=
            mul_le_mul_of_nonneg_left hq hfac
          _ = _ := by ring
      _ = Real.sqrt Cm * ((7 + 2 / Real.log 2) * (1 + 3 / eta) ^ 3) *
          Real.rpow T (11 * eta / 2) * B := by
        have hrpow : Real.rpow T (9 * eta / 2) * Real.rpow T eta =
            Real.rpow T (11 * eta / 2) := by
          calc
            _ = Real.rpow T (9 * eta / 2 + eta) :=
              (Real.rpow_add hTp _ _).symm
            _ = _ := by congr 1 <;> ring
        calc
          _ = Real.sqrt Cm * ((7 + 2 / Real.log 2) *
              (1 + 3 / eta) ^ 3) *
              (Real.rpow T (9 * eta / 2) * Real.rpow T eta) * B := by ring
          _ = _ := by rw [hrpow]
      _ ≤ _ := by
        have hp : Real.rpow T (11 * eta / 2) ≤ Real.rpow T (6 * eta) :=
          Real.rpow_le_rpow_of_exponent_le hT
          (by nlinarith [heta])
        have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
        have hnon : 0 ≤ Real.sqrt Cm *
            ((7 + 2 / Real.log 2) * (1 + 3 / eta) ^ 3) * B := by positivity
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_left hp hnon)
  have htail := log_weighted_sqrt_tail hT hCt
  calc
    (1 + Real.log T) ^ 2 * |X| ≤
        (1 + Real.log T) ^ 2 *
          (Real.sqrt (Cm * (Real.rpow T eta) ^ 9 *
            (k + 7 : ℝ) ^ 2 *
              (T ^ 4 * R ^ 3 + T ^ 2 * n ^ 2 * R * E)) +
            Real.sqrt (Ct * Real.rpow T (-282 : ℝ))) :=
      mul_le_mul_of_nonneg_left habs (sq_nonneg _)
    _ = (1 + Real.log T) ^ 2 *
          Real.sqrt (Cm * (Real.rpow T eta) ^ 9 *
            (k + 7 : ℝ) ^ 2 *
              (T ^ 4 * R ^ 3 + T ^ 2 * n ^ 2 * R * E)) +
        (1 + Real.log T) ^ 2 * Real.sqrt (Ct * Real.rpow T (-282 : ℝ)) := by ring
    _ ≤ _ := by simpa [B] using add_le_add hmainlog htail

#print axioms GuthMaynardS3BlockSqrtLogEnvelope.block_sqrt_log_envelope
end GuthMaynardS3BlockSqrtLogEnvelope
