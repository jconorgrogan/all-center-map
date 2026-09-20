import Mathlib

namespace MAPFordCollisionHalfCount

/-- An exact natural-number form of the collision exclusion step. -/
theorem energy_le_twice_good
    (k P C E E2 B pin bad good : ℕ)
    (hk : 2 ≤ k) (hP : (2*C)^2 < P)
    (hholder : pin^(2*k) ≤ E2 * E^(2*k-2) * B)
    (hmax : E2 ≤ E) (hdiag : P^k * B ≤ E)
    (hbad : bad ≤ C*pin) (hpartition : E = bad+good) :
    E ≤ 2*good := by
  by_contra hnot
  have hE : E ≤ 2*C*pin := by nlinarith [hbad]
  have hpin : 0 < pin := by
    by_contra hn
    have hz : pin = 0 := by omega
    simp [hz] at hbad
    omega
  have hh : pin^(2*k)*P^k ≤ E^(2*k) := by
    calc
      pin^(2*k)*P^k ≤ (E2*E^(2*k-2)*B)*P^k := Nat.mul_le_mul_right _ hholder
      _ ≤ (E*E^(2*k-2)*B)*P^k := by gcongr
      _ = (E*E^(2*k-2))*(P^k*B) := by ring
      _ ≤ (E*E^(2*k-2))*E := Nat.mul_le_mul_left _ hdiag
      _ = E^(2*k) := by
        rw [← pow_succ', ← pow_succ]
        congr 1
        omega
  have hpow : E^(2*k) ≤ (2*C*pin)^(2*k) := Nat.pow_le_pow_left hE _
  have hcancel : P^k ≤ (2*C)^(2*k) := by
    have hc : pin^(2*k)*P^k ≤ pin^(2*k)*(2*C)^(2*k) := by
      calc
        pin^(2*k)*P^k ≤ (2*C*pin)^(2*k) := hh.trans hpow
        _ = pin^(2*k)*(2*C)^(2*k) := by rw [mul_pow]; ring
    exact Nat.le_of_mul_le_mul_left hc (by positivity)
  have hlt : ((2*C)^2)^k < P^k := Nat.pow_lt_pow_left hP (by omega)
  rw [pow_mul] at hcancel
  exact (Nat.not_lt_of_ge hcancel) hlt

end MAPFordCollisionHalfCount
#print axioms MAPFordCollisionHalfCount.energy_le_twice_good
