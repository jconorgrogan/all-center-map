import FordWeakTrajectoryMoment
import FordWeakPolicyLowerTrajectory
import FordWeakTotalCoefficient
import FordCompleteMomentLiftBound

open MAPFordWeakPolicy MAPFordCompleteSystemMoment FordJ2GeometricAlgebra
open FordWeakTrajectoryMoment FordWeakTotalCoefficient
open FordCompleteMomentLiftBound

noncomputable section
set_option autoImplicit false
namespace FordWeakCompleteMoment

def weakExponent (s k : ℕ) : ℝ :=
  2 * (s : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 + (k : ℝ) ^ 2 / 1000

def weakCoefficient (k : ℕ) : ℝ := (2 : ℝ) ^ ((2 ^ 24) * k ^ 6)

private lemma ceil_nat_mul_bound {k n : ℕ}
    (hn : n ≤ Nat.ceil (1001 * (k : ℝ)) + 1) :
    n ≤ 1001 * k + 1 := by
  have hceil : Nat.ceil (1001 * (k : ℝ)) = 1001 * k := by
    have heq : 1001 * (k : ℝ) = ((1001 * k : ℕ) : ℝ) := by norm_num
    rw [heq]
    exact Nat.ceil_natCast (1001 * k)
  simpa [hceil] using hn

/-- The stopped lower-policy trajectory gives one actual complete-moment row
with the total coefficient envelope and the literal deficit exponent. -/
theorem exists_weak_complete_moment
    {k : ℕ} (hk : 2000 ≤ k) :
    ∃ s : ℕ, 1 ≤ s ∧ s ≤ 1003 * k ^ 2 ∧
      ∀ P : ℕ, 1 ≤ P →
        (completeMoment s k P : ℝ) ≤
          weakCoefficient k * (P : ℝ) ^ weakExponent s k := by
  have hkR : (2000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨n, hn, hstop⟩ := policyTrajectoryLower_stops hkR hkpos
  have hnNat : n ≤ 1001 * k + 1 := ceil_nat_mul_bound hn
  have hcoef0 := total_coefficient_bound hk hnNat
  have hcoef : trajectoryCoefficient k n ≤ weakCoefficient k := by
    dsimp [trajectoryCoefficient, weakCoefficient]
    exact hcoef0
  have htraj := trajectory_moment_bound hk hn
  have hsR := policyTrajectoryLower_s_parameter_bound hkR hkpos hn
  have hs : k + n * k ≤ 1003 * k ^ 2 := by exact_mod_cast hsR
  have hs1 : 1 ≤ k + n * k := by omega
  refine ⟨k + n * k, hs1, hs, ?_⟩
  intro P hP
  have hJ := htraj P hP
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hDelta : policyTrajectoryLower (k : ℝ) n ≤ (k : ℝ) ^ 2 / 1000 := le_of_lt hstop
  have hExp : lambda ((k + n * k : ℕ) : ℝ) (k : ℝ)
      (policyTrajectoryLower (k : ℝ) n) ≤
      weakExponent (k + n * k) k := by
    dsimp [lambda, weakExponent]
    norm_num at *
    linarith
  have hPexp := Real.rpow_le_rpow_of_exponent_le hP1 hExp
  have hPleft : 0 ≤ (P : ℝ) ^
      (lambda ((k + n * k : ℕ) : ℝ) (k : ℝ)
        (policyTrajectoryLower (k : ℝ) n)) := by positivity
  have hWeak : 0 ≤ weakCoefficient k := by
    dsimp [weakCoefficient]
    positivity
  have hmul := mul_le_mul hcoef hPexp hPleft hWeak
  exact hJ.trans hmul

/-- A deterministic fixed-row version obtained by lifting the stopped row to
`R = 1003*k^2`; the same coefficient and deficit exponent are retained. -/
theorem fixed_weak_complete_moment
    {k : ℕ} (hk : 2000 ≤ k) :
    ∀ P : ℕ, 1 ≤ P →
      (completeMoment (1003 * k ^ 2) k P : ℝ) ≤
        weakCoefficient k * (P : ℝ) ^ weakExponent (1003 * k ^ 2) k := by
  obtain ⟨s, hs1, hsR, hrow⟩ := exists_weak_complete_moment hk
  intro P hP
  let t : ℕ := 1003 * k ^ 2 - s
  have hst : s + t = 1003 * k ^ 2 := by
    dsimp [t]
    omega
  have hlift := FordCompleteMomentLiftBound.completeMoment_lift (s := s)
    (t := t) (k := k) (P := P) hP
  have hrowP := hrow P hP
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hPnonneg : 0 ≤ (P : ℝ) := hPpos.le
  have hPpow : 0 ≤ (P : ℝ) ^ (2 * (t : ℝ)) := by positivity
  have hbound :
      (completeMoment (s + t) k P : ℝ) ≤
        (P : ℝ) ^ (2 * (t : ℝ)) *
          (weakCoefficient k * (P : ℝ) ^ weakExponent s k) := by
    calc
      (completeMoment (s + t) k P : ℝ) ≤
          ((P ^ (2 * t) : ℕ) : ℝ) * (completeMoment s k P : ℝ) := by
            exact_mod_cast hlift
      _ = (P : ℝ) ^ (2 * (t : ℝ)) * (completeMoment s k P : ℝ) := by
            push_cast
            congr 1
            have he : (2 * (t : ℝ)) = ((2 * t : ℕ) : ℝ) := by norm_num
            rw [he, Real.rpow_natCast]
      _ ≤ _ := mul_le_mul_of_nonneg_left hrowP hPpow
  rw [hst] at hbound
  have hexp : 2 * (t : ℝ) + weakExponent s k =
      weakExponent (1003 * k ^ 2) k := by
    dsimp [t, weakExponent]
    have hstR : (s : ℝ) + (t : ℝ) = (1003 * k ^ 2 : ℕ) := by
      exact_mod_cast hst
    linarith
  calc
    (completeMoment (1003 * k ^ 2) k P : ℝ) ≤
        (P : ℝ) ^ (2 * (t : ℝ)) *
          (weakCoefficient k * (P : ℝ) ^ weakExponent s k) := hbound
    _ = weakCoefficient k *
          ((P : ℝ) ^ (2 * (t : ℝ)) * (P : ℝ) ^ weakExponent s k) := by
      ring
    _ = weakCoefficient k * (P : ℝ) ^ weakExponent (1003 * k ^ 2) k := by
      rw [← Real.rpow_add hPpos]
      rw [hexp]

end FordWeakCompleteMoment
#print axioms FordWeakCompleteMoment.exists_weak_complete_moment
#print axioms FordWeakCompleteMoment.fixed_weak_complete_moment
