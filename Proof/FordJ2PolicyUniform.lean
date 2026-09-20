import FordJ2LargeUniform
import FordJ2SmallUniform
import FordWeakLowerPolicyNatBridge

open MAPFordWeakPolicy MAPFordCompleteSystemMoment
open scoped BigOperators ZMod ComplexConjugate
open MAPFordCompleteSystemMoment FordKPointEnergy FordBoundaryCountGeometry
open FordBoundaryEnergyMoments FordBoundaryWeightedHolder MAPFordP16FiniteFourierBridge
open MAPFordBoundaryCrossFourier


open FordJ2LargeUniform FordJ2SmallUniform FordWeakLowerNat
open FordJ2GeometricAlgebra

noncomputable section
set_option autoImplicit false
namespace FordJ2PolicyUniform

/-- Uniform policy step for every positive source scale.  The lower-policy
natural bridge supplies the legal remainder and both source exponents; the
large/small split leaves only the prior uniform moment estimate. -/
theorem policy_uniform_bound
    {s k P : ℕ} {Delta C : ℝ}
    (hk : 2000 ≤ k) (hs1 : 1 ≤ s) (hs : s ≤ 1003 * k ^ 2)
    (hD0 : (k : ℝ) ^ 2 / 1000 ≤ Delta)
    (hD1 : Delta ≤ ((k : ℝ) ^ 2 - (k : ℝ)) / 2)
    (hP : 1 ≤ P) (hC : 0 ≤ C)
    (hlambda : 0 ≤ lambda (s : ℝ) (k : ℝ) Delta)
    (hJ : ∀ N : ℕ, 1 ≤ N →
      (completeMoment s k N : ℝ) ≤ C * (N : ℝ) ^ lambda (s : ℝ) (k : ℝ) Delta) :
    (completeMoment (s + k) k P : ℝ) ≤
      (2 : ℝ) ^ (8192 * k ^ 5) * C *
        (P : ℝ) ^ lambda ((s + k : ℕ) : ℝ) (k : ℝ)
          (fordDeltaNext (k : ℝ) Delta
            (max 1 (Nat.ceil (Delta / (k : ℝ) - 1) : ℝ))) := by
  have hbridge := lower_policy_nat_bridge hk hD0 hD1
  rcases hbridge with ⟨hAcast, hRcast, hR2, hRle, ha1lo, ha2lo, hgap⟩
  have hdrop := lower_policy_deltaNext_drop_le hk hD0 hD1
  let A : ℝ := max 1 (Nat.ceil (Delta / (k : ℝ) - 1) : ℝ)
  have hAeq : (lowerPolicyA k Delta : ℝ) = A := hAcast
  have hReq : (lowerPolicyR k Delta : ℝ) = (k : ℝ) - A := by
    calc
      (lowerPolicyR k Delta : ℝ) = (k : ℝ) - (lowerPolicyA k Delta : ℝ) := hRcast
      _ = (k : ℝ) - A := by rw [hAeq]
  have hdeltaEq :
      fordDeltaNext (k : ℝ) Delta ((k : ℝ) - (lowerPolicyR k Delta : ℝ)) =
        fordDeltaNext (k : ℝ) Delta A := by
    rw [hReq]
    congr 2
    ring
  have hdropA : Delta - fordDeltaNext (k : ℝ) Delta A ≤ (k : ℝ) := by
    simpa [hAeq] using hdrop
  by_cases hlarge : 2 ^ (100 * k ^ 4) ≤ P
  · have hRnat : 2 ≤ lowerPolicyR k Delta := hR2
    have hRkle : lowerPolicyR k Delta ≤ k := hRle
    have ha1Phi :
        MAPFordWeakPolicy.fordPhi1 (k : ℝ) Delta
            ((k : ℝ) - (lowerPolicyR k Delta : ℝ)) =
          MAPFordWeakPolicy.fordPhi1 (k : ℝ) Delta A := by
      rw [hReq]
      congr 2
      ring
    have hlarge' := large_uniform_bound
      (s := s) (k := k) (r := lowerPolicyR k Delta) (P := P)
      (a1 := MAPFordWeakPolicy.fordPhi1 (k : ℝ) Delta
        ((k : ℝ) - (lowerPolicyR k Delta : ℝ)))
      (a2 := 1 / (lowerPolicyR k Delta : ℝ)) (Delta := Delta) (C := C)
      (by omega) hs1 hs hRnat hRkle hlarge rfl rfl
      (by
        rw [ha1Phi, ← hAeq]
        exact ha1lo) ha2lo (by
        rw [ha1Phi, ← hAeq]
        simpa [div_eq_mul_inv] using hgap)
      hC (by simpa using hlambda) (by simpa using hJ)
    simpa [A, hdeltaEq] using hlarge'
  · have hsmall : P ≤ 2 ^ (100 * k ^ 4) := by omega
    have hsmall' := small_uniform_bound
      (s := s) (k := k) (P := P) (Delta := Delta)
      (DeltaNext := fordDeltaNext (k : ℝ) Delta A) (C := C) hP hsmall hC hdropA (hJ P hP)
    simpa [A] using hsmall'

end FordJ2PolicyUniform
#print axioms FordJ2PolicyUniform.policy_uniform_bound
