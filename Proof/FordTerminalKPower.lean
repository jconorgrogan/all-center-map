import FordTerminalKCount
import FordTerminalPrimeScale
import FordJ2GeometricAlgebra
import FordNaturalScaleBounds

open scoped BigOperators
open MAPFordType MAPFordP16Source35Triangular
open MAPFordLemma32LiteralContract MAPFordCompleteSystemMoment
open MAPFordLemma32GeometricRange
open FordTerminalKCount FordTerminalPrimeScale
open FordJ2GeometricAlgebra FordNaturalScaleBounds

noncomputable section
set_option autoImplicit false
namespace FordTerminalKPower

/-- Degree-one terminal power bound. The only analytic input is a uniform
power bound for the actual complete moment; all prime, quotient, and floor
steps remain literal finite arithmetic. -/
theorem terminal_K_power_bound
    {s k r P Q M B q : ℕ} {T : ℤ}
    (hk : 2 ≤ k) (hs : 1 ≤ s) (hr : 2 ≤ r) (hrk : r ≤ k)
    (hP : 1 ≤ P) (hlarge : 16 * k ^ 4 < P)
    (hMfloor : M = Nat.floor ((P : ℝ) ^ ((1 : ℝ) / (r : ℝ))))
    (hM : k ≤ M)
    (hPsource : P ≤ (M + 1) ^ (k + 1))
    (hB : 2 ^ (k ^ 3) ≤ B)
    {C lambda b : ℝ}
    (hnative : (4 * s) ^ 2 * B * M ≤ Q)
    (hQ : Q ≤ Nat.floor ((P : ℝ) ^ (b : ℝ)))
    (hb : (1 : ℝ) / (r : ℝ) ≤ b)
    (hT : 0 < T) (hTsize : T.natAbs ≤ P)
    (hq : 0 < q) (m : ℕ) (phi : Fin k → Polynomial ℤ)
    (htype : FordType k 1 T m (psiNatSucc phi))
    (hC : 0 ≤ C) (hlambda : 0 ≤ lambda)
    (hJ : ∀ N : ℕ, 1 ≤ N →
      (completeMoment s k N : ℝ) ≤ C * (N : ℝ) ^ lambda) :
    (Fintype.card (KPoint s k P Q phi q) : ℝ) ≤
      4 * (k : ℝ) ^ 3 * (B : ℝ) ^ (countExponent s k r 1) * C *
        (P : ℝ) ^ ((k : ℝ) +
          ((1 : ℝ) / (r : ℝ)) * (countExponent s k r 1 : ℝ) +
          (b - (1 : ℝ) / (r : ℝ)) * lambda) := by
  have hk1 : 1 ≤ k := by omega
  have hr1 : 1 ≤ r := by omega
  have hnative0 : (4 * s) ^ 2 * (2 ^ (k ^ 3) * M) ≤ Q := by
    calc
      (4 * s) ^ 2 * (2 ^ (k ^ 3) * M) ≤ (4 * s) ^ 2 * (B * M) := by
        exact Nat.mul_le_mul_left ((4 * s) ^ 2)
          (Nat.mul_le_mul_right M hB)
      _ = (4 * s) ^ 2 * B * M := by ring
      _ ≤ Q := hnative
  have hfloor_lt : Nat.floor ((P : ℝ) ^ ((1 : ℝ) / (r : ℝ))) < M + 1 := by
    rw [← hMfloor]
    omega
  have hterminal : P < (M + 1) ^ r :=
    terminal_prime_scale hP hr1 hfloor_lt
  obtain ⟨p, hp, hkp, hMp, hupper, hnativep, m', phi', hphi', hK⟩ :=
    exists_terminal_K_bound hk (by omega) (by omega) hs hr1 hrk hlarge hM
      hPsource hnative0 hq hterminal hT (by simpa using hTsize) m phi htype
  have hMplus : M + 1 ≤ p := by omega
  have hpFloor : Nat.floor ((P : ℝ) ^ ((1 : ℝ) / (r : ℝ))) < p := by
    calc
      Nat.floor ((P : ℝ) ^ ((1 : ℝ) / (r : ℝ))) = M := hMfloor.symm
      _ < p := hMp
  have hquot : Q / p ≤ Nat.floor ((P : ℝ) ^
      (b - (1 : ℝ) / (r : ℝ))) :=
    floor_quotient_shortening hP hb hpFloor hQ
  have hQp : 1 ≤ Q / p := by
    have hpQ : p ≤ Q := by
      calc p ≤ B * M := by
            exact hupper.trans (Nat.mul_le_mul_right M hB)
        _ ≤ (4 * s) ^ 2 * B * M := by
            simpa [Nat.mul_assoc] using
              (Nat.le_mul_of_pos_left (B * M) (by positivity))
        _ ≤ Q := hnative
    exact (Nat.le_div_iff_mul_le hp.pos).2 (by
      simpa [Nat.mul_comm] using hpQ)
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hPnonneg : 0 ≤ (P : ℝ) := hPpos.le
  have hMreal : (M : ℝ) ≤ (P : ℝ) ^ ((1 : ℝ) / (r : ℝ)) := by
    rw [hMfloor]
    exact_mod_cast (Nat.floor_le (Real.rpow_nonneg hPnonneg _))
  have ha2 : (0 : ℝ) ≤ (1 : ℝ) / (r : ℝ) := by positivity
  have hBnat : 0 < B := lt_of_lt_of_le (by positivity) hB
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast hBnat
  have hpB : p ≤ B * M := hupper.trans (Nat.mul_le_mul_right M hB)
  have hpReal : (p : ℝ) ≤ (B : ℝ) *
      (P : ℝ) ^ ((1 : ℝ) / (r : ℝ)) := by
    have hpBM : (p : ℝ) ≤ (B : ℝ) * M := by exact_mod_cast hpB
    exact hpBM.trans (mul_le_mul_of_nonneg_left hMreal (le_of_lt hBpos))
  let E1 : ℕ := countExponent s k r 1
  have hpPow : (p : ℝ) ^ E1 ≤
      (B : ℝ) ^ E1 * (P : ℝ) ^
        ((1 : ℝ) / (r : ℝ) * (E1 : ℝ)) := by
    calc
      (p : ℝ) ^ E1 ≤
          ((B : ℝ) * (P : ℝ) ^ ((1 : ℝ) / (r : ℝ))) ^ E1 :=
        pow_le_pow_left₀ (by positivity) hpReal E1
      _ = (B : ℝ) ^ E1 *
          (P : ℝ) ^ ((1 : ℝ) / (r : ℝ) * (E1 : ℝ)) := by
        rw [mul_pow, Real.rpow_mul_natCast hPnonneg]
  have hNreal : ((Q / p : ℕ) : ℝ) ≤
      (P : ℝ) ^ (b - (1 : ℝ) / (r : ℝ)) := by
    calc
      ((Q / p : ℕ) : ℝ) ≤ (Nat.floor ((P : ℝ) ^
          (b - (1 : ℝ) / (r : ℝ))) : ℝ) := by exact_mod_cast hquot
      _ ≤ (P : ℝ) ^ (b - (1 : ℝ) / (r : ℝ)) :=
        Nat.floor_le (Real.rpow_nonneg hPnonneg _)
  have hJq := hJ (Q / p) hQp
  have hJpower : (completeMoment s k (Q / p) : ℝ) ≤
      C * (P : ℝ) ^ ((b - (1 : ℝ) / (r : ℝ)) * lambda) := by
    calc
      (completeMoment s k (Q / p) : ℝ) ≤ C * ((Q / p : ℕ) : ℝ) ^ lambda := hJq
      _ ≤ C * ((P : ℝ) ^ (b - (1 : ℝ) / (r : ℝ))) ^ lambda := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hNreal hlambda) hC
      _ = C * (P : ℝ) ^ ((b - (1 : ℝ) / (r : ℝ)) * lambda) := by
        rw [Real.rpow_mul hPnonneg]
  have hKnat : Fintype.card (KPoint s k P Q phi q) ≤
      4 * k ^ 3 * p ^ E1 * P ^ k * completeMoment s k (Q / p) := by
    simpa [E1, FordJ2GeometricAlgebra.countExponent, Nat.factorial,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hK
  have hKreal : (Fintype.card (KPoint s k P Q phi q) : ℝ) ≤
      (4 * (k : ℝ) ^ 3) * (p : ℝ) ^ E1 * (P : ℝ) ^ (k : ℝ) *
        (completeMoment s k (Q / p) : ℝ) := by
    exact_mod_cast hKnat
  calc
    (Fintype.card (KPoint s k P Q phi q) : ℝ) ≤
        (4 * (k : ℝ) ^ 3) * (p : ℝ) ^ E1 * (P : ℝ) ^ (k : ℝ) *
          (C * (P : ℝ) ^ ((b - (1 : ℝ) / (r : ℝ)) * lambda)) := by
      exact hKreal.trans (mul_le_mul_of_nonneg_left hJpower (by positivity))
    _ ≤ (4 * (k : ℝ) ^ 3) * ((B : ℝ) ^ E1 *
          (P : ℝ) ^ ((1 : ℝ) / (r : ℝ) * (E1 : ℝ))) *
          (P : ℝ) ^ (k : ℝ) *
          (C * (P : ℝ) ^ ((b - (1 : ℝ) / (r : ℝ)) * lambda)) := by
      have hleft0 : 0 ≤ (4 : ℝ) * (k : ℝ) ^ 3 := by positivity
      have hPk0 : 0 ≤ (P : ℝ) ^ (k : ℝ) := by positivity
      have hrest0 : 0 ≤ C * (P : ℝ) ^
          ((b - (1 : ℝ) / (r : ℝ)) * lambda) :=
        mul_nonneg hC (by positivity)
      have hmul := mul_le_mul_of_nonneg_left hpPow
        (mul_nonneg hleft0 (mul_nonneg hPk0 hrest0))
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    _ = 4 * (k : ℝ) ^ 3 * (B : ℝ) ^ (countExponent s k r 1) * C *
        (P : ℝ) ^ ((k : ℝ) +
          ((1 : ℝ) / (r : ℝ)) * (countExponent s k r 1 : ℝ) +
          (b - (1 : ℝ) / (r : ℝ)) * lambda) := by
      dsimp [E1]
      have hcombine :
          (P : ℝ) ^ ((1 : ℝ) / (r : ℝ) * (countExponent s k r 1 : ℝ)) *
              (P : ℝ) ^ (k : ℝ) *
              (C * (P : ℝ) ^ ((b - (1 : ℝ) / (r : ℝ)) * lambda)) =
            C * (P : ℝ) ^ ((k : ℝ) +
              (1 : ℝ) / (r : ℝ) * (countExponent s k r 1 : ℝ) +
              (b - (1 : ℝ) / (r : ℝ)) * lambda) := by
        calc
          _ = C * ((P : ℝ) ^ ((1 : ℝ) / (r : ℝ) *
              (countExponent s k r 1 : ℝ)) *
              (P : ℝ) ^ (k : ℝ) *
              (P : ℝ) ^ ((b - (1 : ℝ) / (r : ℝ)) * lambda)) := by ring
          _ = C * ((P : ℝ) ^ ((1 : ℝ) / (r : ℝ) *
              (countExponent s k r 1 : ℝ) + (k : ℝ)) *
              (P : ℝ) ^ ((b - (1 : ℝ) / (r : ℝ)) * lambda)) := by
                rw [← Real.rpow_add hPpos]
          _ = C * (P : ℝ) ^ ((k : ℝ) +
              (1 : ℝ) / (r : ℝ) * (countExponent s k r 1 : ℝ) +
              (b - (1 : ℝ) / (r : ℝ)) * lambda) := by
                rw [← Real.rpow_add hPpos]
                ring
      calc
        _ = 4 * (k : ℝ) ^ 3 * (B : ℝ) ^ countExponent s k r 1 *
            ((P : ℝ) ^ ((1 : ℝ) / (r : ℝ) * (countExponent s k r 1 : ℝ)) *
              (P : ℝ) ^ (k : ℝ) *
              (C * (P : ℝ) ^ ((b - (1 : ℝ) / (r : ℝ)) * lambda))) := by ring
        _ = _ := by rw [hcombine]; ring

end FordTerminalKPower

#print axioms FordTerminalKPower.terminal_K_power_bound
