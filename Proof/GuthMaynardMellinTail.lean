import GuthMaynardMellinDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exact quadratic Mellin-tail truncation

This file certifies the improper-integral estimate used after the cutoff's
Mellin transform is shown to decay.  It deliberately exposes the limitation
of two integrations by parts: quadratic decay gives a tail of size `C / R`.
Obtaining Guth--Maynard's `T⁻¹⁰⁰` error with a subpower cutoff therefore still
requires the source's arbitrary-order repeated integration by parts.
-/

namespace GuthMaynardMellinTail

open MeasureTheory Set

noncomputable section

theorem norm_positiveQuadraticTail_le
    {F : ℝ → ℂ} {C R : ℝ}
    (hR : 0 < R)
    (hbound : ∀ r, R < r → ‖F r‖ ≤ C * r ^ (-2 : ℝ)) :
    ‖∫ r : ℝ in Ioi R, F r‖ ≤ C / R := by
  have hpow : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hR
  have hmajor : Integrable (fun r : ℝ => C * r ^ (-2 : ℝ))
      (volume.restrict (Ioi R)) := hpow.const_mul C
  calc
    ‖∫ r : ℝ in Ioi R, F r‖ ≤
      ∫ r : ℝ in Ioi R, C * r ^ (-2 : ℝ) := by
        apply norm_integral_le_of_norm_le hmajor
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact hbound r hr
    _ = C / R := by
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt (by norm_num) hR]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num]
      rw [Real.rpow_neg_one]
      field_simp [hR.ne']

theorem norm_negativeQuadraticTail_le
    {F : ℝ → ℂ} {C R : ℝ}
    (hR : 0 < R)
    (hbound : ∀ r, r < -R → ‖F r‖ ≤ C * (-r) ^ (-2 : ℝ)) :
    ‖∫ r : ℝ in Iic (-R), F r‖ ≤ C / R := by
  rw [← integral_comp_neg_Ioi]
  apply norm_positiveQuadraticTail_le hR
  intro r hr
  simpa using hbound (-r) (by linarith)

/-- The two-sided exterior tail.  Integrability is stated explicitly only to
justify splitting the set integral; each one-sided numerical estimate is
already forced by its integrable majorant. -/
theorem norm_twoSidedQuadraticTail_le
    {F : ℝ → ℂ} {C R : ℝ}
    (hR : 0 < R)
    (hFneg : IntegrableOn F (Iic (-R)))
    (hFpos : IntegrableOn F (Ioi R))
    (hboundPos : ∀ r, R < r → ‖F r‖ ≤ C * r ^ (-2 : ℝ))
    (hboundNeg : ∀ r, r < -R → ‖F r‖ ≤ C * (-r) ^ (-2 : ℝ)) :
    ‖∫ r : ℝ in (Iic (-R) ∪ Ioi R), F r‖ ≤ 2 * C / R := by
  rw [integral_union_ae
    (Set.Iic_disjoint_Ioi (by linarith : -R ≤ R)).aedisjoint
    measurableSet_Ioi.nullMeasurableSet hFneg hFpos]
  calc
    ‖(∫ r : ℝ in Iic (-R), F r) + ∫ r : ℝ in Ioi R, F r‖ ≤
      ‖∫ r : ℝ in Iic (-R), F r‖ +
        ‖∫ r : ℝ in Ioi R, F r‖ := norm_add_le _ _
    _ ≤ C / R + C / R := add_le_add
      (norm_negativeQuadraticTail_le hR hboundNeg)
      (norm_positiveQuadraticTail_le hR hboundPos)
    _ = 2 * C / R := by ring

/-- Arbitrary natural-power positive tail.  This is the exact improper
integral behind the source's selectable repeated-IBP exponent. -/
theorem norm_positiveNatPowerTail_le
    {F : ℝ → ℂ} {C R : ℝ} {k : ℕ}
    (hk : 2 ≤ k) (hR : 0 < R)
    (hbound : ∀ r, R < r → ‖F r‖ ≤ C * r ^ (-(k : ℝ))) :
    ‖∫ r : ℝ in Ioi R, F r‖ ≤
      C * (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
  have hkR : (1 : ℝ) < k := by
    exact_mod_cast (show (1 : ℕ) < k by omega)
  have hexp : -(k : ℝ) < -1 := by linarith
  have hpow : IntegrableOn (fun r : ℝ => r ^ (-(k : ℝ))) (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt hexp hR
  have hmajor : Integrable (fun r : ℝ => C * r ^ (-(k : ℝ)))
      (volume.restrict (Ioi R)) := hpow.const_mul C
  calc
    ‖∫ r : ℝ in Ioi R, F r‖ ≤
      ∫ r : ℝ in Ioi R, C * r ^ (-(k : ℝ)) := by
        apply norm_integral_le_of_norm_le hmajor
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact hbound r hr
    _ = C * (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt hexp hR]
      congr 1
      rw [show -(k : ℝ) + 1 = 1 - k by ring]
      rw [show 1 - (k : ℝ) = -((k : ℝ) - 1) by ring]
      have hkne : (k : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
      field_simp [hkne]

end

end GuthMaynardMellinTail

#print axioms GuthMaynardMellinTail.norm_positiveQuadraticTail_le
#print axioms GuthMaynardMellinTail.norm_negativeQuadraticTail_le
#print axioms GuthMaynardMellinTail.norm_twoSidedQuadraticTail_le
#print axioms GuthMaynardMellinTail.norm_positiveNatPowerTail_le
