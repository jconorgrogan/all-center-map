import FordCompleteMomentKPower
import FordLemma32GeometricRange
import FordLPointMonotone
import FordTerminalPrimeScale
import FordJ2GeometricAlgebra

open scoped BigOperators
open MAPFordType MAPFordP16Source35Triangular
open MAPFordLemma32LiteralContract MAPFordCompleteSystemMoment
open MAPFordLemma32GeometricRange
open FordCompleteMomentKPower FordLPointMonotone FordTerminalPrimeScale
open FordJ2GeometricAlgebra

noncomputable section
set_option autoImplicit false
namespace FordJ2InitialL

/-- Initial bounded-scale bootstrap: the degree-zero complete moment is
controlled by one geometric prime and an L-carrier at the shortened source
box. -/
theorem exists_initial_L_bound
    {s k r P M B : ℕ} {a : ℝ}
    (hk : 2 ≤ k) (hs : 1 ≤ s) (hr1 : 1 ≤ r) (hrk : r ≤ k)
    (hlarge : 16 * k ^ 4 < P)
    (ha : a ≤ 1)
    (hMfloor : M = Nat.floor ((P : ℝ) ^ a))
    (hM : k ≤ M)
    (hPsource : P ≤ (M + 1) ^ (k + 1))
    (hB : 2 ^ (k ^ 3) ≤ B)
    (hnative : (4 * s) ^ 2 * B * M ≤ P) :
    ∃ p : ℕ, ∃ hp : p.Prime,
      k < p ∧ M < p ∧ p ≤ B * M ∧ (4 * s) ^ 2 * p ≤ P ∧
      ∃ (m : ℕ) (phi : Fin k → Polynomial ℤ),
        FordType k 0 1 m (psiNatSucc phi) ∧
        completeMoment (s + k) k P ≤
          4 * k ^ 3 * p ^ (countExponent s k r 0) *
            Fintype.card (LPoint s k P (Nat.floor ((P : ℝ) ^ (1 - a))) p 1 r phi) := by
  have hP1 : 1 ≤ P := by omega
  have h0k : 0 ≤ k := by omega
  have h0s : 0 ≤ s := by omega
  have hnative0 : (4 * s) ^ 2 * (2 ^ (k ^ 3) * M) ≤ P := by
    calc
      (4 * s) ^ 2 * (2 ^ (k ^ 3) * M) ≤ (4 * s) ^ 2 * (B * M) := by
        exact Nat.mul_le_mul_left ((4 * s) ^ 2)
          (Nat.mul_le_mul_right M hB)
      _ = (4 * s) ^ 2 * B * M := by ring
      _ ≤ P := hnative
  obtain ⟨p, hp, hkp, hMp, hpupper, hnativep, m, phi, hphi, hK⟩ :=
    K_exists_L_geometric_range
      (s := s) (k := k) (d := 0) (P := P) (Q := P) (q := 1) (r := r) (M := M)
      (T := 1) hk (by omega) (by omega) hs hr1 hrk hlarge hM hPsource hnative0
      (by norm_num) (by norm_num) (by simpa using hP1) 0 (powerFamily (k := k))
      (powerFamily_fordType (k := k))
  have hpB : p ≤ B * M := by
    exact hpupper.trans (Nat.mul_le_mul_right M hB)
  have hpFloor : Nat.floor ((P : ℝ) ^ a) < p := by
    calc
      Nat.floor ((P : ℝ) ^ a) = M := hMfloor.symm
      _ < p := hMp
  have hshort : P / p ≤ Nat.floor ((P : ℝ) ^ (1 - a)) := by
    apply floor_quotient_shortening hP1 ha hpFloor
    have hPfloor : P ≤ Nat.floor ((P : ℝ) ^ (1 : ℝ)) := by
      simpa using (Nat.le_floor (by positivity : (0 : ℝ) ≤ (P : ℝ)))
    exact hPfloor
  have hLmono := lPoint_card_mono
    (s := s) (k := k) (P := P) (Q₁ := P / p)
    (Q₂ := Nat.floor ((P : ℝ) ^ (1 - a)))
    (p := p) (q := 1) (r := r) hshort phi
  have hKcomplete := completeMoment_eq_kPoint_power (s := s) (k := k) (P := P)
  have hK' : Fintype.card (KPoint s k P P (powerFamily (k := k)) 1) ≤
      4 * k ^ 3 * p ^ (countExponent s k r 0) *
        Fintype.card (LPoint s k P (P / p) p 1 r phi) := by
    simpa [countExponent, Nat.factorial] using hK
  refine ⟨p, hp, hkp, hMp, hpB, hnativep, m, phi, hphi, ?_⟩
  calc
    completeMoment (s + k) k P = Fintype.card (KPoint s k P P (powerFamily (k := k)) 1) :=
      hKcomplete
    _ ≤ 4 * k ^ 3 * p ^ (countExponent s k r 0) *
        Fintype.card (LPoint s k P (P / p) p 1 r phi) := hK'
    _ ≤ 4 * k ^ 3 * p ^ (countExponent s k r 0) *
        Fintype.card (LPoint s k P (Nat.floor ((P : ℝ) ^ (1 - a))) p 1 r phi) := by
      exact Nat.mul_le_mul_left _ hLmono

end FordJ2InitialL

#print axioms FordJ2InitialL.exists_initial_L_bound
