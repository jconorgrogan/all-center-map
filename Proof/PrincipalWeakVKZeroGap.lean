import KhaleAppendixBSourceReduction

/-!
# A single weak-VK gap for the conductor-one divisor

Low ordinates are a fixed finite set.  At ordinates at least three, the
literal `104` part of Khale Appendix B supplies the required region, including
the exact level-one to level-three transfer.
 -/

namespace MAPPrincipalWeakVKZeroGap

open Filter DirichletZeros
open MAPAPPrimitiveRegularLowGap MAPKhaleAppendixBSource

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

theorem exists_eventually_principal_weakVK_gap_of_appendixB
    (hKhale104 : AppendixBCorollary104) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ T : ℝ, T ≤ X →
        ∀ rho ∈ zeroSupport (1 : DirichletCharacter ℂ 1) 0 T,
          c * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤ 1 - rho.re := by
  obtain ⟨cLow, hcLow, hLow⟩ := exists_primitive_principal_regular_low_gap
  obtain ⟨cHigh, hcHigh, hHigh⟩ :=
    exists_eventually_primitive_regular_high_gap_of_appendixB
      hKhale104 1 (by norm_num)
  let c := min (1 / 5) (min cLow cHigh)
  have hc : 0 < c := lt_min (by norm_num) (lt_min hcLow hcHigh)
  have hdecay : ∀ᶠ X : ℝ in atTop,
      c * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤ c := by
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with X hX
    have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
    have hlogOne : 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hXpos]
      exact hX
    have hp : Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤ 1 := by
      calc
        Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤
            Real.rpow (Real.log X) 0 :=
          Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num)
        _ = 1 := Real.rpow_zero _
    exact (mul_le_mul_of_nonneg_left hp hc.le).trans_eq (mul_one c)
  have hqcap : ∀ᶠ X : ℝ in atTop,
      (1 : ℝ) ≤ Real.rpow (Real.log X) 1 := by
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with X hX
    have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
    have hlogOne : 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hXpos]
      exact hX
    simpa using hlogOne
  refine ⟨c, hc, ?_⟩
  filter_upwards [hHigh, hdecay, hqcap] with X hHighX hdecayX hqcapX
  have hlogOne : 1 ≤ Real.log X := by
    simpa using hqcapX
  have hlogNonneg : 0 ≤ Real.log X := by
    exact zero_le_one.trans hlogOne
  intro T hTX rho hrho
  by_cases hbeta : 4 / 5 < rho.re
  · by_cases him : |rho.im| < 3
    · have hprim : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
        show (1 : DirichletCharacter ℂ 1).conductor = 1
        rw [DirichletCharacter.conductor_one]
      have hsource := hLow 1 (1 : DirichletCharacter ℂ 1)
        hprim rfl T rho hrho hbeta him
      exact hdecayX.trans ((min_le_right (1 / 5) (min cLow cHigh)).trans
        (min_le_left cLow cHigh) |>.trans hsource)
    · have hrect := PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
        (1 : DirichletCharacter ℂ 1) 0 T hrho
      have himT : |rho.im| ≤ T := abs_le.mpr hrect.2
      have himX : |rho.im| ≤ X := himT.trans hTX
      have hprim : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
        show (1 : DirichletCharacter ℂ 1).conductor = 1
        rw [DirichletCharacter.conductor_one]
      have hqcapNat : ((1 : ℕ) : ℝ) ≤ Real.rpow (Real.log X) 1 := by
        simpa using hqcapX
      have hsource := hHighX (1 : ℕ) (1 : DirichletCharacter ℂ 1)
        hprim hqcapNat T rho hrho hbeta (le_of_not_gt him) himX
      exact mul_le_mul_of_nonneg_right
        ((min_le_right (1 / 5) (min cLow cHigh)).trans
          (min_le_right cLow cHigh))
        (Real.rpow_nonneg hlogNonneg _) |>.trans hsource
  · have hgap : (1 / 5 : ℝ) ≤ 1 - rho.re := by linarith
    exact hdecayX.trans ((min_le_left (1 / 5) (min cLow cHigh)).trans hgap)

end
end MAPPrincipalWeakVKZeroGap

#print axioms MAPPrincipalWeakVKZeroGap.exists_eventually_principal_weakVK_gap_of_appendixB
