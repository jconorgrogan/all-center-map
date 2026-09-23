import Mathlib
import FordWeakLowerPolicyScales

open MAPFordWeakPolicy

namespace FordWeakLowerNat
noncomputable section
set_option maxHeartbeats 900000

/-- The natural ceiling parameter used by the lower-floor policy. -/
def lowerPolicyA (kNat : ℕ) (Delta : ℝ) : ℕ :=
  max 1 (Nat.ceil (Delta / (kNat : ℝ) - 1))

/-- The natural remainder length associated with `lowerPolicyA`. -/
def lowerPolicyR (kNat : ℕ) (Delta : ℝ) : ℕ :=
  kNat - lowerPolicyA kNat Delta

theorem lower_policy_nat_bridge
    {kNat : ℕ} {Delta : ℝ}
    (hkNat : 2000 ≤ kNat)
    (hD0 : (kNat : ℝ) ^ 2 / 1000 ≤ Delta)
    (hD1 : Delta ≤ ((kNat : ℝ) ^ 2 - (kNat : ℝ)) / 2) :
    ((lowerPolicyA kNat Delta : ℕ) : ℝ) =
        max 1 (Nat.ceil (Delta / (kNat : ℝ) - 1) : ℝ) ∧
    ((lowerPolicyR kNat Delta : ℕ) : ℝ) =
        (kNat : ℝ) - (lowerPolicyA kNat Delta : ℝ) ∧
    2 ≤ lowerPolicyR kNat Delta ∧
    lowerPolicyR kNat Delta ≤ kNat ∧
    1 / ((kNat : ℝ) + 1) ≤
      MAPFordWeakPolicy.fordPhi1 (kNat : ℝ) Delta
        (lowerPolicyA kNat Delta : ℝ) ∧
    1 / ((kNat : ℝ) + 1) ≤
      1 / (lowerPolicyR kNat Delta : ℝ) ∧
    MAPFordWeakPolicy.fordPhi1 (kNat : ℝ) Delta
        (lowerPolicyA kNat Delta : ℝ) +
      2 / (lowerPolicyR kNat Delta : ℝ) ≤ (9 / 10 : ℝ) := by
  let k : ℝ := (kNat : ℝ)
  let A : ℝ := max 1 (Nat.ceil (Delta / k - 1) : ℝ)
  let r : ℝ := k - A
  have hk : 2000 ≤ k := by
    dsimp [k]
    exact_mod_cast hkNat
  have hk0 : 0 < k := by
    dsimp [k]
    positivity
  have hD0' : k ^ 2 / 1000 ≤ Delta := by
    simpa [k] using hD0
  have hD1' : Delta ≤ (k ^ 2 - k) / 2 := by
    simpa [k] using hD1
  have hs := FordWeakLowerPolicyScales.lower_policy_scales hk hk0 hD0' hD1'
  dsimp at hs
  rcases hs with ⟨hA1, hAhalf, hr4, hrltrk, ha1lo, ha2lo, hagap⟩
  have hAcast : (lowerPolicyA kNat Delta : ℝ) = A := by
    dsimp [lowerPolicyA, A, k]
    norm_num [Nat.cast_max]
  have hAle : lowerPolicyA kNat Delta ≤ kNat := by
    have hA_le_real : (lowerPolicyA kNat Delta : ℝ) ≤ k := by
      rw [hAcast]
      linarith [hAhalf]
    have hA_le_real' : (lowerPolicyA kNat Delta : ℝ) ≤ (kNat : ℝ) := by
      simpa [k] using hA_le_real
    exact_mod_cast hA_le_real'
  have hAcast_nat : (lowerPolicyA kNat Delta : ℝ) =
      max 1 (Nat.ceil (Delta / (kNat : ℝ) - 1) : ℝ) := by
    dsimp [lowerPolicyA]
    norm_num [Nat.cast_max]
  have hRcast : (lowerPolicyR kNat Delta : ℝ) = r := by
    change ((kNat - lowerPolicyA kNat Delta : ℕ) : ℝ) = r
    rw [Nat.cast_sub hAle, hAcast]
  have hRnat2 : 2 ≤ lowerPolicyR kNat Delta := by
    have : (4 : ℝ) ≤ (lowerPolicyR kNat Delta : ℝ) := by
      rw [hRcast]
      exact hr4
    have : (2 : ℝ) ≤ (lowerPolicyR kNat Delta : ℝ) := by
      linarith
    exact_mod_cast this
  have hRcast_nat : (lowerPolicyR kNat Delta : ℝ) =
      (kNat : ℝ) - (lowerPolicyA kNat Delta : ℝ) := by
    change ((kNat - lowerPolicyA kNat Delta : ℕ) : ℝ) = _
    rw [Nat.cast_sub hAle]
  have hRnat_le : lowerPolicyR kNat Delta ≤ kNat :=
    Nat.sub_le _ _
  have ha1nat :
      1 / ((kNat : ℝ) + 1) ≤
        MAPFordWeakPolicy.fordPhi1 (kNat : ℝ) Delta
          (lowerPolicyA kNat Delta : ℝ) := by
    rw [hAcast]
    simpa [k, A] using ha1lo
  have ha2nat :
      1 / ((kNat : ℝ) + 1) ≤ 1 / (lowerPolicyR kNat Delta : ℝ) := by
    rw [hRcast]
    simpa [k, r, A] using ha2lo
  have hagapnat :
      MAPFordWeakPolicy.fordPhi1 (kNat : ℝ) Delta
          (lowerPolicyA kNat Delta : ℝ) +
        2 / (lowerPolicyR kNat Delta : ℝ) ≤ (9 / 10 : ℝ) := by
    rw [hAcast, hRcast]
    simpa [k, A, r, div_eq_mul_inv] using hagap
  exact ⟨hAcast_nat, hRcast_nat, hRnat2, hRnat_le, ha1nat, ha2nat, hagapnat⟩

/-- On the same natural policy cell, one J2 update drops `Delta` by at most
    `k`; this is the sign needed when tracking the trajectory parameter. -/
theorem lower_policy_deltaNext_drop_le
    {kNat : ℕ} {Delta : ℝ}
    (hkNat : 2000 ≤ kNat)
    (hD0 : (kNat : ℝ) ^ 2 / 1000 ≤ Delta)
    (hD1 : Delta ≤ ((kNat : ℝ) ^ 2 - (kNat : ℝ)) / 2) :
    Delta - MAPFordWeakPolicy.fordDeltaNext (kNat : ℝ) Delta
        (lowerPolicyA kNat Delta : ℝ) ≤ (kNat : ℝ) := by
  have hbridge := lower_policy_nat_bridge hkNat hD0 hD1
  rcases hbridge with ⟨hAcast, hRcast, hR2, hRle, ha1lo, ha2lo, hagap⟩
  have ha10 : 0 ≤ MAPFordWeakPolicy.fordPhi1 (kNat : ℝ) Delta
      (lowerPolicyA kNat Delta : ℝ) := by
    have hk1 : 0 < (kNat : ℝ) + 1 := by positivity
    have : 0 ≤ 1 / ((kNat : ℝ) + 1) := by positivity
    linarith
  have hbracket :
      Delta - (((kNat : ℝ) ^ 2 + (kNat : ℝ) +
        ((kNat : ℝ) - (lowerPolicyA kNat Delta : ℝ)) ^ 2 -
        ((kNat : ℝ) - (lowerPolicyA kNat Delta : ℝ))) / 2) - (kNat : ℝ) ≤ 0 := by
    nlinarith [hD1, sq_nonneg ((kNat : ℝ) - (lowerPolicyA kNat Delta : ℝ))]
  have hidentity :
      Delta - MAPFordWeakPolicy.fordDeltaNext (kNat : ℝ) Delta
          (lowerPolicyA kNat Delta : ℝ) =
        (kNat : ℝ) +
          MAPFordWeakPolicy.fordPhi1 (kNat : ℝ) Delta
            (lowerPolicyA kNat Delta : ℝ) *
            (Delta - (((kNat : ℝ) ^ 2 + (kNat : ℝ) +
              ((kNat : ℝ) - (lowerPolicyA kNat Delta : ℝ)) ^ 2 -
              ((kNat : ℝ) - (lowerPolicyA kNat Delta : ℝ))) / 2) - (kNat : ℝ)) := by
    dsimp [MAPFordWeakPolicy.fordDeltaNext]
    ring
  have hprod :
      MAPFordWeakPolicy.fordPhi1 (kNat : ℝ) Delta
          (lowerPolicyA kNat Delta : ℝ) *
        (Delta - (((kNat : ℝ) ^ 2 + (kNat : ℝ) +
          ((kNat : ℝ) - (lowerPolicyA kNat Delta : ℝ)) ^ 2 -
          ((kNat : ℝ) - (lowerPolicyA kNat Delta : ℝ))) / 2) - (kNat : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha10 hbracket
  linarith [hidentity, hprod]

end
end FordWeakLowerNat

#print axioms FordWeakLowerNat.lower_policy_nat_bridge
#print axioms FordWeakLowerNat.lower_policy_deltaNext_drop_le
