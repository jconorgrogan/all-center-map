import GuthMaynardS3OneStepSubpower

open scoped Real

noncomputable section
set_option maxHeartbeats 2000000
namespace GuthMaynardS3BlockMainLedger

/-!
The literal scalar part of the block ledger.  The two summands are kept
separate: the first uses `(N*K)^4`, while the second uses `(N*K)^2*N^2`.
The tail/remainder term belongs to a different consumer.
-/

theorem main_terms_scalar_ledger
    {D C A B R E N K T rho V L : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hR : 0 ≤ R) (hE : 0 ≤ E) (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hKpos : 0 < K) (hT : 1 ≤ T) (hrho : 1 ≤ rho)
    (hNK : N * K ≤ 4 * rho * T)
    (hV : 0 ≤ V) (hVcap : V ≤ 64 * rho ^ 3) :
    8 * (16 * D * rho * N ^ 2 / K) ^ 2 * A * R * L ^ 2 * C * V *
          ((4 * K) ^ 6 * (A * R) ^ 2 + (4 * K) ^ 4 * (B * rho * E)) ≤
      (64 * ((2 : ℝ) ^ 19 * D ^ 2 * C * A) * (4096 * A ^ 2 + 16 * B)) *
          rho ^ 9 * L ^ 2 * (T ^ 4 * R ^ 3 + T ^ 2 * N ^ 2 * R * E) := by
  have hT0 : 0 ≤ T := by linarith
  have hrho0 : 0 ≤ rho := by linarith
  have hNK0 : 0 ≤ N * K := mul_nonneg hN hK
  have hpowNK4 : (N * K) ^ 4 ≤ (4 * rho * T) ^ 4 := by
    exact pow_le_pow_left₀ hNK0 hNK 4
  have hpowNK2 : (N * K) ^ 2 ≤ (4 * rho * T) ^ 2 := by
    exact pow_le_pow_left₀ hNK0 hNK 2
  have hN2 : 0 ≤ N ^ 2 := sq_nonneg N
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  have hR3 : 0 ≤ R ^ 3 := by positivity
  have hRE : 0 ≤ R * E := mul_nonneg hR hE
  have hT4R3 : 0 ≤ T ^ 4 * R ^ 3 := by positivity
  have hT2N2RE : 0 ≤ T ^ 2 * N ^ 2 * R * E := by positivity
  have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
  have hA3 : 0 ≤ A ^ 3 := by positivity
  have hD2 : 0 ≤ D ^ 2 := sq_nonneg D
  have hDC1 : 0 ≤ D ^ 2 * C * A ^ 3 := by positivity
  have hDC2 : 0 ≤ D ^ 2 * C * A * B := by positivity
  have hterm1_id :
      8 * (16 * D * rho * N ^ 2 / K) ^ 2 * A * R * L ^ 2 * C * V *
          ((4 * K) ^ 6 * (A * R) ^ 2) =
        (2 : ℝ) ^ 23 * D ^ 2 * C * A ^ 3 * V * rho ^ 2 *
          (N ^ 4 * K ^ 4) * R ^ 3 * L ^ 2 := by
    field_simp [ne_of_gt hKpos]
    ring
  have hterm2_id :
      8 * (16 * D * rho * N ^ 2 / K) ^ 2 * A * R * L ^ 2 * C * V *
          ((4 * K) ^ 4 * (B * rho * E)) =
        (2 : ℝ) ^ 19 * D ^ 2 * C * A * B * V * rho ^ 3 *
          (N ^ 4 * K ^ 2) * R * E * L ^ 2 := by
    field_simp [ne_of_gt hKpos]
    ring
  have hfirst :
      (2 : ℝ) ^ 23 * D ^ 2 * C * A ^ 3 * V * rho ^ 2 *
          (N ^ 4 * K ^ 4) * R ^ 3 * L ^ 2 ≤
        (2 : ℝ) ^ 37 * D ^ 2 * C * A ^ 3 * rho ^ 9 * T ^ 4 *
          R ^ 3 * L ^ 2 := by
    calc
      (2 : ℝ) ^ 23 * D ^ 2 * C * A ^ 3 * V * rho ^ 2 *
          (N ^ 4 * K ^ 4) * R ^ 3 * L ^ 2 ≤
          (2 : ℝ) ^ 23 * D ^ 2 * C * A ^ 3 * (64 * rho ^ 3) *
            rho ^ 2 * (N ^ 4 * K ^ 4) * R ^ 3 * L ^ 2 := by
        gcongr
      _ ≤ (2 : ℝ) ^ 23 * D ^ 2 * C * A ^ 3 * (64 * rho ^ 3) *
            rho ^ 2 * (4 * rho * T) ^ 4 * R ^ 3 * L ^ 2 := by
        have hpow : N ^ 4 * K ^ 4 ≤ (4 * rho * T) ^ 4 := by
          calc
            N ^ 4 * K ^ 4 = (N * K) ^ 4 := by ring
            _ ≤ (4 * rho * T) ^ 4 := hpowNK4
        gcongr
      _ = (2 : ℝ) ^ 37 * D ^ 2 * C * A ^ 3 * rho ^ 9 * T ^ 4 *
            R ^ 3 * L ^ 2 := by ring
  have hrho8 : rho ^ 8 ≤ rho ^ 9 := by
    calc
      rho ^ 8 = rho ^ 8 * 1 := by ring
      _ ≤ rho ^ 8 * rho := by gcongr
      _ = rho ^ 9 := by ring
  have hsecond :
      (2 : ℝ) ^ 19 * D ^ 2 * C * A * B * V * rho ^ 3 *
          (N ^ 4 * K ^ 2) * R * E * L ^ 2 ≤
        (2 : ℝ) ^ 29 * D ^ 2 * C * A * B * rho ^ 9 * T ^ 2 *
          N ^ 2 * R * E * L ^ 2 := by
    calc
      (2 : ℝ) ^ 19 * D ^ 2 * C * A * B * V * rho ^ 3 *
          (N ^ 4 * K ^ 2) * R * E * L ^ 2 ≤
          (2 : ℝ) ^ 19 * D ^ 2 * C * A * B * (64 * rho ^ 3) *
            rho ^ 3 * (N ^ 4 * K ^ 2) * R * E * L ^ 2 := by
        gcongr
      _ ≤ (2 : ℝ) ^ 19 * D ^ 2 * C * A * B * (64 * rho ^ 3) *
            rho ^ 3 * ((4 * rho * T) ^ 2 * N ^ 2) * R * E * L ^ 2 := by
        have hprod : N ^ 4 * K ^ 2 = (N * K) ^ 2 * N ^ 2 := by ring
        rw [hprod]
        gcongr
      _ = (2 : ℝ) ^ 29 * D ^ 2 * C * A * B * rho ^ 8 * T ^ 2 *
            N ^ 2 * R * E * L ^ 2 := by ring
      _ ≤ (2 : ℝ) ^ 29 * D ^ 2 * C * A * B * rho ^ 9 * T ^ 2 *
            N ^ 2 * R * E * L ^ 2 := by
        gcongr
  have hfirst_rhs :
      (2 : ℝ) ^ 37 * D ^ 2 * C * A ^ 3 * rho ^ 9 * T ^ 4 * R ^ 3 * L ^ 2 ≤
          (64 * ((2 : ℝ) ^ 19 * D ^ 2 * C * A) * (4096 * A ^ 2)) *
          rho ^ 9 * L ^ 2 * (T ^ 4 * R ^ 3) := by
    convert le_rfl using 1 <;> ring
  have hsecond_rhs :
      (2 : ℝ) ^ 29 * D ^ 2 * C * A * B * rho ^ 9 * T ^ 2 *
          N ^ 2 * R * E * L ^ 2 ≤
          (64 * ((2 : ℝ) ^ 19 * D ^ 2 * C * A) * (16 * B)) *
          rho ^ 9 * L ^ 2 * (T ^ 2 * N ^ 2 * R * E) := by
    convert le_rfl using 1 <;> ring
  have hfirst' :
      8 * (16 * D * rho * N ^ 2 / K) ^ 2 * A * R * L ^ 2 * C * V *
          ((4 * K) ^ 6 * (A * R) ^ 2) ≤
        (2 : ℝ) ^ 37 * D ^ 2 * C * A ^ 3 * rho ^ 9 * T ^ 4 *
          R ^ 3 * L ^ 2 := by
    rw [hterm1_id]
    exact hfirst
  have hsecond' :
      8 * (16 * D * rho * N ^ 2 / K) ^ 2 * A * R * L ^ 2 * C * V *
          ((4 * K) ^ 4 * (B * rho * E)) ≤
        (2 : ℝ) ^ 29 * D ^ 2 * C * A * B * rho ^ 9 * T ^ 2 *
          N ^ 2 * R * E * L ^ 2 := by
    rw [hterm2_id]
    exact hsecond
  calc
    8 * (16 * D * rho * N ^ 2 / K) ^ 2 * A * R * L ^ 2 * C * V *
          ((4 * K) ^ 6 * (A * R) ^ 2 + (4 * K) ^ 4 * (B * rho * E)) =
        8 * (16 * D * rho * N ^ 2 / K) ^ 2 * A * R * L ^ 2 * C * V *
          ((4 * K) ^ 6 * (A * R) ^ 2) +
        8 * (16 * D * rho * N ^ 2 / K) ^ 2 * A * R * L ^ 2 * C * V *
          ((4 * K) ^ 4 * (B * rho * E)) := by ring
    _ ≤
      (2 : ℝ) ^ 37 * D ^ 2 * C * A ^ 3 * rho ^ 9 * T ^ 4 * R ^ 3 * L ^ 2 +
        (2 : ℝ) ^ 29 * D ^ 2 * C * A * B * rho ^ 9 * T ^ 2 *
          N ^ 2 * R * E * L ^ 2 := add_le_add hfirst' hsecond'
    _ ≤
      (64 * ((2 : ℝ) ^ 19 * D ^ 2 * C * A) *
            (4096 * A ^ 2 + 16 * B)) * rho ^ 9 * L ^ 2 *
          (T ^ 4 * R ^ 3 + T ^ 2 * N ^ 2 * R * E) := by
      calc
        _ ≤ (64 * ((2 : ℝ) ^ 19 * D ^ 2 * C * A) * (4096 * A ^ 2)) *
              rho ^ 9 * L ^ 2 * (T ^ 4 * R ^ 3) +
            (64 * ((2 : ℝ) ^ 19 * D ^ 2 * C * A) * (16 * B)) *
              rho ^ 9 * L ^ 2 * (T ^ 2 * N ^ 2 * R * E) :=
          add_le_add hfirst_rhs hsecond_rhs
        _ ≤ _ := by
          have hq : 0 ≤ 64 * ((2 : ℝ) ^ 19 * D ^ 2 * C * A) := by
            positivity
          have hcross :
              0 ≤ (64 * ((2 : ℝ) ^ 19 * D ^ 2 * C * A)) * rho ^ 9 * L ^ 2 *
                (4096 * A ^ 2 * (T ^ 2 * N ^ 2 * R * E) +
                  16 * B * (T ^ 4 * R ^ 3)) := by
            positivity
          have hstep :
              (64 * ((2 : ℝ) ^ 19 * D ^ 2 * C * A) * (4096 * A ^ 2)) *
                  rho ^ 9 * L ^ 2 * (T ^ 4 * R ^ 3) +
                (64 * ((2 : ℝ) ^ 19 * D ^ 2 * C * A) * (16 * B)) *
                  rho ^ 9 * L ^ 2 * (T ^ 2 * N ^ 2 * R * E) ≤
              ((64 * ((2 : ℝ) ^ 19 * D ^ 2 * C * A) * (4096 * A ^ 2)) *
                  rho ^ 9 * L ^ 2 * (T ^ 4 * R ^ 3) +
                (64 * ((2 : ℝ) ^ 19 * D ^ 2 * C * A) * (16 * B)) *
                  rho ^ 9 * L ^ 2 * (T ^ 2 * N ^ 2 * R * E)) +
                (64 * ((2 : ℝ) ^ 19 * D ^ 2 * C * A)) * rho ^ 9 * L ^ 2 *
                  (4096 * A ^ 2 * (T ^ 2 * N ^ 2 * R * E) +
                    16 * B * (T ^ 4 * R ^ 3)) := by
            exact le_add_of_nonneg_right hcross
          calc
            _ ≤ _ +
                (64 * ((2 : ℝ) ^ 19 * D ^ 2 * C * A)) * rho ^ 9 * L ^ 2 *
                  (4096 * A ^ 2 * (T ^ 2 * N ^ 2 * R * E) +
                    16 * B * (T ^ 4 * R ^ 3)) := hstep
            _ = _ := by ring

end GuthMaynardS3BlockMainLedger

#print axioms GuthMaynardS3BlockMainLedger.main_terms_scalar_ledger
