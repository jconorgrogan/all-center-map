import GuthMaynardLemma62ReflectionSubstitution

/-!
# Absolute Mellin tails for Guth--Maynard Lemma 6.2

The source truncates the Mellin line by absolute values.  A bound merely on
the norm of the tail integral would not suffice once the reflection kernel is
inserted.  These lemmas record the required stronger `L¹` tail directly from
the arbitrary-order pointwise Schwartz estimate.
-/

namespace GuthMaynardLemma62AbsoluteMellinTail

open Real Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap
open GuthMaynardMellinRapidDecay
open GuthMaynardSectionThreeCutoff
open GuthMaynardLemma62MellinInversion

noncomputable section

def sectionThreeMellinSeminorm (k : ℕ) : ℝ :=
  SchwartzMap.seminorm ℂ k 0
    (𝓕 (mellinLogLiftSchwartz sectionThreeCutoff
      (mellinLogLift_hasCompactSupport
        (by norm_num) (by norm_num) sectionThreeCutoff_supported)
      (mellinLogLift_contDiff sectionThreeCutoff_contDiff)) : 𝓢(ℝ, ℂ))

theorem sectionThreeMellinSeminorm_nonneg (k : ℕ) :
    0 ≤ sectionThreeMellinSeminorm k := by
  unfold sectionThreeMellinSeminorm
  exact NonnegHomClass.apply_nonneg _ _

/-- Positive absolute Mellin tail, with arbitrary selectable order. -/
theorem integral_Ioi_norm_sectionThreeMellin_le
    {R : ℝ} {k : ℕ} (hk : 2 ≤ k) (hR : 0 < R) :
    (∫ r : ℝ in Set.Ioi R,
        ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖) ≤
      ((2 * Real.pi) ^ k * sectionThreeMellinSeminorm k) *
        (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hexp : -(k : ℝ) < -1 := by linarith
  let C : ℝ := (2 * Real.pi) ^ k * sectionThreeMellinSeminorm k
  have hC : 0 ≤ C := mul_nonneg (by positivity)
    (sectionThreeMellinSeminorm_nonneg k)
  have hpow : IntegrableOn (fun r : ℝ => r ^ (-(k : ℝ))) (Set.Ioi R) :=
    integrableOn_Ioi_rpow_of_lt hexp hR
  have hmajor : IntegrableOn (fun r : ℝ => C * r ^ (-(k : ℝ))) (Set.Ioi R) :=
    hpow.const_mul C
  have hMellin : IntegrableOn (fun r : ℝ =>
      ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖) (Set.Ioi R) :=
    sectionThreeCutoff_verticalIntegrable.norm.integrableOn
  calc
    (∫ r : ℝ in Set.Ioi R,
        ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖) ≤
      ∫ r : ℝ in Set.Ioi R, C * r ^ (-(k : ℝ)) := by
        apply setIntegral_mono_on hMellin hmajor measurableSet_Ioi
        intro r hr
        have hr0 : r ≠ 0 := ne_of_gt (hR.trans hr)
        have hraw := norm_mellin_line_one_le_seminorm_div_scaledPower
          (by norm_num) (by norm_num) sectionThreeCutoff_supported
          sectionThreeCutoff_contDiff k hr0
        unfold C sectionThreeMellinSeminorm
        apply hraw.trans_eq
        rw [abs_of_pos (div_pos (hR.trans hr) (by positivity))]
        rw [div_pow]
        rw [Real.rpow_neg (hR.trans hr).le, Real.rpow_natCast]
        field_simp [hr0, Real.pi_ne_zero, pow_ne_zero]
    _ = C * (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt hexp hR]
      congr 1
      rw [show -(k : ℝ) + 1 = 1 - k by ring]
      rw [show 1 - (k : ℝ) = -((k : ℝ) - 1) by ring]
      have hkne : (k : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
      field_simp [hkne]
    _ = _ := rfl

/-- Matching negative absolute Mellin tail. -/
theorem integral_Iic_norm_sectionThreeMellin_le
    {R : ℝ} {k : ℕ} (hk : 2 ≤ k) (hR : 0 < R) :
    (∫ r : ℝ in Set.Iic (-R),
        ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖) ≤
      ((2 * Real.pi) ^ k * sectionThreeMellinSeminorm k) *
        (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
  rw [← integral_comp_neg_Ioi]
  have hkR : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hexp : -(k : ℝ) < -1 := by linarith
  let C : ℝ := (2 * Real.pi) ^ k * sectionThreeMellinSeminorm k
  have hC : 0 ≤ C := mul_nonneg (by positivity)
    (sectionThreeMellinSeminorm_nonneg k)
  have hpow : IntegrableOn (fun r : ℝ => r ^ (-(k : ℝ))) (Set.Ioi R) :=
    integrableOn_Ioi_rpow_of_lt hexp hR
  have hmajor : IntegrableOn (fun r : ℝ => C * r ^ (-(k : ℝ))) (Set.Ioi R) :=
    hpow.const_mul C
  have hMellin : IntegrableOn (fun r : ℝ =>
      ‖mellin sectionThreeCutoff
        ((1 : ℂ) + ((-r : ℝ) : ℂ) * Complex.I)‖) (Set.Ioi R) :=
    sectionThreeCutoff_verticalIntegrable.comp_neg.norm.integrableOn
  calc
    (∫ r : ℝ in Set.Ioi R,
        ‖mellin sectionThreeCutoff
          ((1 : ℂ) + ((-r : ℝ) : ℂ) * Complex.I)‖) ≤
      ∫ r : ℝ in Set.Ioi R, C * r ^ (-(k : ℝ)) := by
        apply setIntegral_mono_on hMellin hmajor measurableSet_Ioi
        intro r hr
        have hr0 : r ≠ 0 := ne_of_gt (hR.trans hr)
        have hraw := norm_mellin_line_one_le_seminorm_div_scaledPower
          (by norm_num) (by norm_num) sectionThreeCutoff_supported
          sectionThreeCutoff_contDiff k (neg_ne_zero.mpr hr0)
        unfold C sectionThreeMellinSeminorm
        apply hraw.trans_eq
        rw [abs_div, abs_neg, abs_of_pos (hR.trans hr),
          abs_of_pos (by positivity : 0 < 2 * Real.pi)]
        rw [div_pow]
        rw [Real.rpow_neg (hR.trans hr).le, Real.rpow_natCast]
        field_simp [hr0, Real.pi_ne_zero, pow_ne_zero]
    _ = C * (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt hexp hR]
      congr 1
      rw [show -(k : ℝ) + 1 = 1 - k by ring]
      rw [show 1 - (k : ℝ) = -((k : ℝ) - 1) by ring]
      have hkne : (k : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
      field_simp [hkne]
    _ = _ := rfl

/-- Two-sided absolute tail used in the actual truncation. -/
theorem integral_exterior_norm_sectionThreeMellin_le
    {R : ℝ} {k : ℕ} (hk : 2 ≤ k) (hR : 0 < R) :
    (∫ r : ℝ in (Set.Iic (-R) ∪ Set.Ioi R),
        ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖) ≤
      2 * (((2 * Real.pi) ^ k * sectionThreeMellinSeminorm k) *
        (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1))) := by
  have hnegInt : IntegrableOn (fun r : ℝ =>
      ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖) (Set.Iic (-R)) :=
    sectionThreeCutoff_verticalIntegrable.norm.integrableOn
  have hposInt : IntegrableOn (fun r : ℝ =>
      ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖) (Set.Ioi R) :=
    sectionThreeCutoff_verticalIntegrable.norm.integrableOn
  rw [integral_union_ae
    (Set.Iic_disjoint_Ioi (by linarith : -R ≤ R)).aedisjoint
    measurableSet_Ioi.nullMeasurableSet hnegInt hposInt]
  linarith [integral_Iic_norm_sectionThreeMellin_le hk hR,
    integral_Ioi_norm_sectionThreeMellin_le hk hR]

end

end GuthMaynardLemma62AbsoluteMellinTail

#print axioms GuthMaynardLemma62AbsoluteMellinTail.integral_Ioi_norm_sectionThreeMellin_le
#print axioms GuthMaynardLemma62AbsoluteMellinTail.integral_exterior_norm_sectionThreeMellin_le
