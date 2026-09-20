import MRTProposition61HighPolylogBudgetV3
import MRTProposition61TypeIIParameterAbsorptionV3

/-!
# Independent scalar absorption for the D12 envelope

The constant `C` and the natural logarithmic exponent `E` are fixed before
the logarithmic parameter `B`.  The lemma is independent of the D12 source
geometry and absorbs only the three literal scalar terms supplied by that
source interface.
-/

namespace MRTDynamicD12ScalarAbsorptionV3

open Filter
open MRTProposition61HighPolylogBudgetV3
open MRTProposition61TypeIIParameterAbsorptionV3

noncomputable section

set_option maxHeartbeats 1200000

theorem exists_d12_scalar_absorption
    (C : ℝ) (E : ℕ) (A delta : ℝ)
    (hC : 0 < C) (hA : 0 < A)
    (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 240) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∀ᶠ X : ℝ in atTop,
        C * Real.rpow (Real.log X) (E : ℝ) *
            (X * Real.rpow ((Real.log X) ^ B) (-3 / 8 : ℝ) +
              Real.rpow X (1 + delta - 2 / 15) *
                Real.rpow ((Real.log X) ^ B) (5 / 8 : ℝ) +
              Real.rpow X (439 / 2000 : ℝ) *
                Real.rpow ((Real.log X) ^ B) (13 / 8 : ℝ)) ≤
          X * Real.rpow (Real.log X) (-A) / 30 := by
  obtain ⟨B₀, hB₀⟩ := exists_nat_gt ((8 / 3 : ℝ) * ((E : ℝ) + A + 1))
  refine ⟨B₀, ?_⟩
  intro B hB
  have hB' : (B₀ : ℝ) ≤ B := by exact_mod_cast hB
  have hBexp : (E : ℝ) - 3 * (B : ℝ) / 8 < -A := by
    linarith
  have hgap2 : 0 < 2 / 15 - delta := by linarith
  have hgap3 : 0 < (1561 / 2000 : ℝ) := by norm_num
  have h1 := eventually_const_log_power_le_decay
    (90 * C) ((E : ℝ) - 3 * (B : ℝ) / 8) A (by linarith)
  have h2 := eventually_const_polylog_mul_neg_rpow_le_log_decay
    (90 * C) ((E : ℝ) + 5 * (B : ℝ) / 8) A (2 / 15 - delta)
      (by positivity) hgap2
  have h3 := eventually_const_polylog_mul_neg_rpow_le_log_decay
    (90 * C) ((E : ℝ) + 13 * (B : ℝ) / 8) A (1561 / 2000)
      (by positivity) hgap3
  filter_upwards [h1, h2, h3, eventually_gt_atTop (1 : ℝ)] with X h1 h2 h3 hX
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hLpos : 0 < Real.log X := Real.log_pos hX
  have hLnonneg : 0 ≤ Real.log X := hLpos.le
  have hQ (a : ℝ) :
      Real.rpow ((Real.log X) ^ B) a =
        Real.rpow (Real.log X) ((B : ℝ) * a) := by
    simpa only [Real.rpow_eq_pow] using
      (Real.rpow_natCast_mul hLnonneg B a).symm
  have hpow1 : 90 *
      (C * Real.rpow (Real.log X) (E : ℝ) *
        (X * Real.rpow ((Real.log X) ^ B) (-3 / 8 : ℝ))) ≤
      X * Real.rpow (Real.log X) (-A) := by
    have hm := mul_le_mul_of_nonneg_left h1
      (Real.rpow_nonneg hXpos.le 1)
    have hm' : X * (90 * C * Real.rpow (Real.log X)
        ((E : ℝ) - 3 * (B : ℝ) / 8)) ≤
        X * Real.rpow (Real.log X) (-A) := by
      simpa only [Real.rpow_one] using hm
    calc
      _ = X * (90 * C * Real.rpow (Real.log X)
          ((E : ℝ) - 3 * (B : ℝ) / 8)) := by
            rw [hQ]
            calc
              _ = X * (90 * C *
                  (Real.rpow (Real.log X) (E : ℝ) *
                    Real.rpow (Real.log X) ((B : ℝ) * (-3 / 8 : ℝ)))) := by ring
              _ = _ := by
                have hcombine := (Real.rpow_add hLpos (E : ℝ)
                  ((B : ℝ) * (-3 / 8 : ℝ))).symm
                apply congrArg (fun z => X * (90 * C * z))
                calc
                  _ = Real.rpow (Real.log X)
                      ((E : ℝ) + (B : ℝ) * (-3 / 8 : ℝ)) := hcombine
                  _ = Real.rpow (Real.log X)
                      ((E : ℝ) - 3 * (B : ℝ) / 8) := by
                    congr 1
                    ring
      _ ≤ _ := hm'
  have hpow2 : 90 *
      (C * Real.rpow (Real.log X) (E : ℝ) *
        (Real.rpow X (1 + delta - 2 / 15) *
          Real.rpow ((Real.log X) ^ B) (5 / 8 : ℝ))) ≤
      X * Real.rpow (Real.log X) (-A) := by
    have hm := mul_le_mul_of_nonneg_left h2
      (Real.rpow_nonneg hXpos.le 1)
    have hm' : X * (90 * C * Real.rpow (Real.log X)
        ((E : ℝ) + 5 * (B : ℝ) / 8) *
        Real.rpow X (-(2 / 15 - delta))) ≤
        X * Real.rpow (Real.log X) (-A) := by
      simpa only [Real.rpow_one] using hm
    have hx2 : X * Real.rpow X (-(2 / 15 - delta)) =
        Real.rpow X (1 + delta - 2 / 15) := by
      have hxone : Real.rpow X 1 = X := Real.rpow_one X
      calc
        _ = Real.rpow X 1 * Real.rpow X (-(2 / 15 - delta)) := by rw [hxone]
        _ = Real.rpow X (1 + (-(2 / 15 - delta))) :=
          (Real.rpow_add hXpos _ _).symm
        _ = _ := by congr 1; ring
    calc
      _ = X * (90 * C * Real.rpow (Real.log X)
            ((E : ℝ) + 5 * (B : ℝ) / 8) *
            Real.rpow X (-(2 / 15 - delta))) := by
            rw [hQ]
            calc
              _ = Real.rpow X (1 + delta - 2 / 15) *
                  (90 * C *
                    (Real.rpow (Real.log X) (E : ℝ) *
                      Real.rpow (Real.log X) ((B : ℝ) * (5 / 8 : ℝ)))) := by ring
              _ = _ := by
                have hc : Real.rpow (Real.log X) (E : ℝ) *
                    Real.rpow (Real.log X) ((B : ℝ) * (5 / 8 : ℝ)) =
                    Real.rpow (Real.log X)
                      ((E : ℝ) + 5 * (B : ℝ) / 8) := by
                  calc
                    _ = Real.rpow (Real.log X)
                        ((E : ℝ) + (B : ℝ) * (5 / 8 : ℝ)) :=
                      (Real.rpow_add hLpos _ _).symm
                    _ = _ := by congr 1; ring
                rw [hc, ← hx2]
                ring
      _ ≤ _ := hm'
  have hpow3 : 90 *
      (C * Real.rpow (Real.log X) (E : ℝ) *
        (Real.rpow X (439 / 2000 : ℝ) *
          Real.rpow ((Real.log X) ^ B) (13 / 8 : ℝ))) ≤
      X * Real.rpow (Real.log X) (-A) := by
    have hm := mul_le_mul_of_nonneg_left h3
      (Real.rpow_nonneg hXpos.le 1)
    have hm' : X * (90 * C * Real.rpow (Real.log X)
        ((E : ℝ) + 13 * (B : ℝ) / 8) *
        Real.rpow X (-(1561 / 2000 : ℝ))) ≤
        X * Real.rpow (Real.log X) (-A) := by
      simpa only [Real.rpow_one] using hm
    have hx3 : X * Real.rpow X (-(1561 / 2000 : ℝ)) =
        Real.rpow X (439 / 2000 : ℝ) := by
      have hxone : Real.rpow X 1 = X := Real.rpow_one X
      calc
        _ = Real.rpow X 1 * Real.rpow X (-(1561 / 2000 : ℝ)) := by rw [hxone]
        _ = Real.rpow X (1 + (-(1561 / 2000 : ℝ))) :=
          (Real.rpow_add hXpos _ _).symm
        _ = _ := by congr 1; norm_num
    calc
      _ = X * (90 * C * Real.rpow (Real.log X)
              ((E : ℝ) + 13 * (B : ℝ) / 8) *
            Real.rpow X (-(1561 / 2000 : ℝ))) := by
            rw [hQ]
            have hc : Real.rpow (Real.log X) (E : ℝ) *
                Real.rpow (Real.log X) ((B : ℝ) * (13 / 8 : ℝ)) =
                Real.rpow (Real.log X) ((E : ℝ) + 13 * (B : ℝ) / 8) := by
              calc
                _ = Real.rpow (Real.log X)
                    ((E : ℝ) + (B : ℝ) * (13 / 8 : ℝ)) :=
                  (Real.rpow_add hLpos _ _).symm
                _ = _ := by congr 1; ring
            calc
              _ = 90 * (C *
                  (Real.rpow (Real.log X) (E : ℝ) *
                    Real.rpow (Real.log X) ((B : ℝ) * (13 / 8 : ℝ))) *
                  Real.rpow X (439 / 2000 : ℝ)) := by ring
              _ = 90 * (C * Real.rpow (Real.log X)
                  ((E : ℝ) + 13 * (B : ℝ) / 8) *
                  Real.rpow X (439 / 2000 : ℝ)) := by rw [hc]
              _ = _ := by rw [← hx3]; ring
      _ ≤ _ := hm'
  linarith

end
end MRTDynamicD12ScalarAbsorptionV3

#print axioms MRTDynamicD12ScalarAbsorptionV3.exists_d12_scalar_absorption
