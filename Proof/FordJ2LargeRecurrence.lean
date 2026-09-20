import FordJ2LPower
import FordJ2InitialL
import FordJ2GeometricAlgebra

open scoped BigOperators
open MAPFordType MAPFordP16Source35Triangular
open MAPFordLemma32LiteralContract MAPFordCompleteSystemMoment
open MAPFordWeakPolicy
open FordJ2GeometricAlgebra FordJ2LPower FordJ2InitialL

noncomputable section
set_option autoImplicit false
namespace FordJ2LargeRecurrence

/-- One actual large-scale recurrence step.  The degree-zero geometric prime
selection and the degree-one L-power estimate are composed with no residual
K/L or polynomial-type hypotheses. -/
theorem large_recurrence_bound
    {s k r P M1 M2 Q1 B : ℕ} {a Delta C : ℝ}
    (hk : 2 ≤ k) (hs : 1 ≤ s) (hr : 2 ≤ r) (hrk : r ≤ k)
    (hP : 1 ≤ P) (hlarge : 16 * k ^ 4 < P)
    (haPhi : a = fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ)))
    (ha : a ≤ 1) (hb : 1 / (r : ℝ) ≤ 1 - a)
    (hM1floor : M1 = Nat.floor ((P : ℝ) ^ a)) (hM1 : k ≤ M1)
    (hPsource1 : P ≤ (M1 + 1) ^ (k + 1))
    (hM2floor : M2 = Nat.floor ((P : ℝ) ^ (1 / (r : ℝ))))
    (hM2 : k ≤ M2)
    (hPsource2 : P ≤ (M2 + 1) ^ (k + 1))
    (hQ1floor : Q1 = Nat.floor ((P : ℝ) ^ (1 - a)))
    (hB : 2 ^ (k ^ 3) ≤ B)
    (hnative0 : (4 * s) ^ 2 * B * M1 ≤ P)
    (hnative1 : (4 * s) ^ 2 * B * M2 ≤ Q1)
    (hC : 0 ≤ C)
    (hlambda : 0 ≤ lambda (s : ℝ) (k : ℝ) Delta)
    (hJ : ∀ N : ℕ, 1 ≤ N →
      (completeMoment s k N : ℝ) ≤ C * (N : ℝ) ^ lambda (s : ℝ) (k : ℝ) Delta) :
    (completeMoment (s + k) k P : ℝ) ≤
      4 * (k : ℝ) ^ 3 * (B : ℝ) ^ (countExponent s k r 0) *
        (2 : ℝ) ^ k *
        max ((k : ℝ) ^ k)
          (2 * Real.sqrt (4 * (k : ℝ) ^ 3 *
            (B : ℝ) ^ (countExponent s k r 1))) * C *
        (P : ℝ) ^ lambda (s + k) (k : ℝ)
          (fordDeltaNext (k : ℝ) Delta ((k : ℝ) - (r : ℝ))) := by
  subst a
  have hInit := exists_initial_L_bound
    (s := s) (k := k) (r := r) (P := P) (M := M1) (B := B)
    (a := fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ)))
    hk hs (by omega) hrk hlarge ha hM1floor hM1 hPsource1 hB hnative0
  obtain ⟨p, hp, hkp, hM1p, hpB, hnativep, m, phi, hphi, hInit⟩ := hInit
  have hInitQ : completeMoment (s + k) k P ≤
      4 * k ^ 3 * p ^ (countExponent s k r 0) *
        Fintype.card (LPoint s k P Q1 p 1 r phi) := by
    simpa [hQ1floor] using hInit
  have hpFloor : Nat.floor ((P : ℝ) ^ fordPhi1 (k : ℝ) Delta
      ((k : ℝ) - (r : ℝ))) < p := by
    simpa [hM1floor] using hM1p
  have hL := l_power_bound
    (s := s) (k := k) (r := r) (P := P) (Q := Q1) (M := M2)
    (B := B) (p := p) (m := m) (Delta := Delta) (C := C)
    hk hs hr hrk hP hlarge hM2floor hM2 hPsource2 hB hQ1floor hnative1 hb
    hpFloor phi hphi hC hlambda hJ
  have hInitR : (completeMoment (s + k) k P : ℝ) ≤
      4 * (k : ℝ) ^ 3 * (p : ℝ) ^ (countExponent s k r 0) *
        (Fintype.card (LPoint s k P Q1 p 1 r phi) : ℝ) := by
    exact_mod_cast hInitQ
  have hLscaled : (Fintype.card (LPoint s k P Q1 p 1 r phi) : ℝ) ≤
      (2 * (P : ℝ)) ^ k * C *
        (P : ℝ) ^ ((1 - fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ))) *
          lambda (s : ℝ) (k : ℝ) Delta) *
        max ((k : ℝ) ^ k)
          (2 * Real.sqrt (4 * (k : ℝ) ^ 3 *
            (B : ℝ) ^ (countExponent s k r 1))) := hL
  have hM1real : (M1 : ℝ) ≤
      (P : ℝ) ^ fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ)) := by
    rw [hM1floor]
    exact_mod_cast (Nat.floor_le (Real.rpow_nonneg (by positivity) _))
  have hpReal : (p : ℝ) ≤ (B : ℝ) *
      (P : ℝ) ^ fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ)) := by
    have hpBM : (p : ℝ) ≤ (B : ℝ) * (M1 : ℝ) := by
      exact_mod_cast hpB
    exact hpBM.trans (mul_le_mul_of_nonneg_left hM1real (by positivity))
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hPnonneg : 0 ≤ (P : ℝ) := hPpos.le
  have hpPow : (p : ℝ) ^ (countExponent s k r 0) ≤
      (B : ℝ) ^ (countExponent s k r 0) *
        (P : ℝ) ^ (fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ)) *
          (countExponent s k r 0 : ℝ)) := by
    calc
      (p : ℝ) ^ (countExponent s k r 0) ≤
          ((B : ℝ) * (P : ℝ) ^ fordPhi1 (k : ℝ) Delta
            ((k : ℝ) - (r : ℝ))) ^ (countExponent s k r 0) :=
        pow_le_pow_left₀ (by positivity) hpReal _
      _ = _ := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast, Real.rpow_mul hPnonneg]
  have hE0 := countExponent_zero s k r
  change (countExponent s k r 0 : ℝ) = eZero (s : ℝ) (k : ℝ) (r : ℝ) at hE0
  have hexp := terminal_exponent (s : ℝ) (k : ℝ) (r : ℝ) Delta
  rw [← hE0] at hexp
  have hPpow : (P : ℝ) ^
      (fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ)) *
        (countExponent s k r 0 : ℝ)) *
      (P : ℝ) ^ (k : ℝ) *
      (P : ℝ) ^ ((1 - fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ))) *
        lambda (s : ℝ) (k : ℝ) Delta) =
      (P : ℝ) ^ lambda (s + k) (k : ℝ)
        (fordDeltaNext (k : ℝ) Delta ((k : ℝ) - (r : ℝ))) := by
    rw [← Real.rpow_add hPpos, ← Real.rpow_add hPpos]
    exact congrArg (fun x : ℝ => (P : ℝ) ^ x) hexp
  calc
    (completeMoment (s + k) k P : ℝ) ≤
        4 * (k : ℝ) ^ 3 * (p : ℝ) ^ (countExponent s k r 0) *
          ((2 * (P : ℝ)) ^ k * C *
            (P : ℝ) ^ ((1 - fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ))) *
              lambda (s : ℝ) (k : ℝ) Delta) *
            max ((k : ℝ) ^ k)
              (2 * Real.sqrt (4 * (k : ℝ) ^ 3 *
                (B : ℝ) ^ (countExponent s k r 1)))) := by
      exact hInitR.trans (mul_le_mul_of_nonneg_left hLscaled (by positivity))
    _ ≤ 4 * (k : ℝ) ^ 3 *
          ((B : ℝ) ^ (countExponent s k r 0) *
            (P : ℝ) ^ (fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ)) *
              (countExponent s k r 0 : ℝ))) *
          ((2 * (P : ℝ)) ^ k * C *
            (P : ℝ) ^ ((1 - fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ))) *
              lambda (s : ℝ) (k : ℝ) Delta) *
            max ((k : ℝ) ^ k)
              (2 * Real.sqrt (4 * (k : ℝ) ^ 3 *
                (B : ℝ) ^ (countExponent s k r 1)))) := by
      have hscaled := mul_le_mul_of_nonneg_left hpPow (by positivity :
        0 ≤ 4 * (k : ℝ) ^ 3)
      have hscaled' := mul_le_mul_of_nonneg_right hscaled (by positivity :
        0 ≤ (2 * (P : ℝ)) ^ k * C *
          (P : ℝ) ^ ((1 - fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ))) *
            lambda (s : ℝ) (k : ℝ) Delta) *
          max ((k : ℝ) ^ k)
            (2 * Real.sqrt (4 * (k : ℝ) ^ 3 *
              (B : ℝ) ^ (countExponent s k r 1))))
      simpa [mul_assoc] using hscaled'
    _ = 4 * (k : ℝ) ^ 3 * (B : ℝ) ^ (countExponent s k r 0) *
          (2 : ℝ) ^ k *
          max ((k : ℝ) ^ k)
            (2 * Real.sqrt (4 * (k : ℝ) ^ 3 *
              (B : ℝ) ^ (countExponent s k r 1))) * C *
            (P : ℝ) ^ lambda (s + k) (k : ℝ)
            (fordDeltaNext (k : ℝ) Delta ((k : ℝ) - (r : ℝ))) := by
      rw [mul_pow]
      have hPk : (P : ℝ) ^ k = (P : ℝ) ^ (k : ℝ) := by
        rw [← Real.rpow_natCast]
      rw [hPk]
      calc
        _ = 4 * (k : ℝ) ^ 3 * (B : ℝ) ^ (countExponent s k r 0) *
            (2 : ℝ) ^ k *
            max ((k : ℝ) ^ k)
              (2 * Real.sqrt (4 * (k : ℝ) ^ 3 *
                (B : ℝ) ^ (countExponent s k r 1))) * C *
            ((P : ℝ) ^ (fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ)) *
              (countExponent s k r 0 : ℝ)) *
              (P : ℝ) ^ (k : ℝ) *
              (P : ℝ) ^ ((1 - fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ))) *
                lambda (s : ℝ) (k : ℝ) Delta)) := by
          ring_nf
        _ = _ := by
          rw [hPpow]

end FordJ2LargeRecurrence
#print axioms FordJ2LargeRecurrence.large_recurrence_bound
