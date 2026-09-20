import FordJ2LargeRecurrence
import FordJ2NativeThreshold
import FordJ2CoefficientBound

open MAPFordWeakPolicy
open MAPFordCompleteSystemMoment
open FordJ2GeometricAlgebra FordJ2LargeRecurrence
open FordJ2NativeThreshold FordJ2CoefficientBound

noncomputable section
set_option autoImplicit false
namespace FordJ2LargeUniform

/-- The large-scale policy specialization.  All floor, source-box, and native
bounds are discharged from the explicit large-P threshold; the only analytic
premise is the uniform complete-moment estimate. -/
theorem large_uniform_bound
    {s k r P : ℕ} {a1 a2 Delta C : ℝ}
    (hk : 2000 ≤ k) (hs1 : 1 ≤ s) (hs : s ≤ 1003 * k ^ 2)
    (hr : 2 ≤ r) (hrk : r ≤ k)
    (hPpow : 2 ^ (100 * k ^ 4) ≤ P)
    (ha1Phi : a1 = fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ)))
    (ha2r : a2 = 1 / (r : ℝ))
    (ha1lo : 1 / (k + 1 : ℝ) ≤ a1)
    (ha2lo : 1 / (k + 1 : ℝ) ≤ a2)
    (hgap : a1 + 2 * a2 ≤ (9 / 10 : ℝ))
    (hC : 0 ≤ C)
    (hlambda : 0 ≤ lambda (s : ℝ) (k : ℝ) Delta)
    (hJ : ∀ N : ℕ, 1 ≤ N →
      (completeMoment s k N : ℝ) ≤ C * (N : ℝ) ^ lambda (s : ℝ) (k : ℝ) Delta) :
    (completeMoment (s + k) k P : ℝ) ≤
      (2 : ℝ) ^ (8192 * k ^ 5) * C *
        (P : ℝ) ^ lambda (s + k) (k : ℝ)
          (fordDeltaNext (k : ℝ) Delta ((k : ℝ) - (r : ℝ))) := by
  have hP1 : 1 ≤ P := by
    have hbase : 1 ≤ 2 ^ (100 * k ^ 4) := Nat.one_le_pow _ _ (by norm_num)
    exact hbase.trans hPpow
  have hlarge := threshold_large hk hPpow
  have ha2nonneg : 0 ≤ a2 := by
    have : 0 ≤ (1 / (k + 1 : ℝ)) := by positivity
    exact this.trans ha2lo
  have ha1le : a1 ≤ 1 := by nlinarith [hgap, ha2nonneg]
  have hb : 1 / (r : ℝ) ≤ 1 - a1 := by
    rw [← ha2r]
    nlinarith [hgap, ha2nonneg]
  have hsep0 : a1 + (1 / 10 : ℝ) ≤ 1 := by
    nlinarith [hgap, ha2nonneg]
  have hsep1 : 1 / (r : ℝ) + (1 / 10 : ℝ) ≤ 1 - a1 := by
    rw [← ha2r]
    nlinarith [hgap, ha2nonneg]
  have hsrc1 := source_floor_native hk hPpow ha1lo
  have hsrc2 :
      k ≤ Nat.floor ((P : ℝ) ^ (1 / (r : ℝ))) ∧
        P ≤ (Nat.floor ((P : ℝ) ^ (1 / (r : ℝ))) + 1) ^ (k + 1) := by
    exact source_floor_native hk hPpow (by simpa [ha2r] using ha2lo)
  let M1 : ℕ := Nat.floor ((P : ℝ) ^ a1)
  let M2 : ℕ := Nat.floor ((P : ℝ) ^ (1 / (r : ℝ)))
  let Q1 : ℕ := Nat.floor ((P : ℝ) ^ (1 - a1))
  let B : ℕ := 2 ^ (k ^ 3)
  have hM1 : k ≤ M1 := by simpa [M1] using hsrc1.1
  have hM2 : k ≤ M2 := by simpa [M2] using hsrc2.1
  have hPsource1 : P ≤ (M1 + 1) ^ (k + 1) := by
    simpa [M1] using hsrc1.2
  have hPsource2 : P ≤ (M2 + 1) ^ (k + 1) := by
    simpa [M2] using hsrc2.2
  have hnative0 : (4 * s) ^ 2 * B * M1 ≤ P := by
    dsimp [B, M1]
    simpa using (floor_native_step hk hs1 hPpow hs hsep0)
  have hnative1 : (4 * s) ^ 2 * B * M2 ≤ Q1 := by
    dsimp [B, M2, Q1]
    simpa using (floor_native_step hk hs1 hPpow hs hsep1)
  have hLarge := large_recurrence_bound
    (s := s) (k := k) (r := r) (P := P) (M1 := M1) (M2 := M2)
    (Q1 := Q1) (B := B) (a := a1) (Delta := Delta) (C := C)
    (by omega) hs1 hr hrk hP1 hlarge ha1Phi ha1le hb
    (by rfl) hM1 hPsource1 (by rfl) hM2 hPsource2 (by rfl)
    (by rfl) hnative0 hnative1 hC hlambda hJ
  have hcost := terminalCstep_pos_and_bound hk hs hr hrk
  calc
    (completeMoment (s + k) k P : ℝ) ≤
        terminalCstep s k r * C *
          (P : ℝ) ^ lambda (s + k) (k : ℝ)
            (fordDeltaNext (k : ℝ) Delta ((k : ℝ) - (r : ℝ))) := by
      simpa [terminalCstep, stepCoefficient, B] using hLarge
    _ ≤ (2 : ℝ) ^ (8192 * k ^ 5) * C *
          (P : ℝ) ^ lambda (s + k) (k : ℝ)
            (fordDeltaNext (k : ℝ) Delta ((k : ℝ) - (r : ℝ))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcost.2 hC) (by positivity)

end FordJ2LargeUniform
#print axioms FordJ2LargeUniform.large_uniform_bound
