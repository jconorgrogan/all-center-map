import KhaleAppendixBSourceReduction
import KhaleWeakVKConstantCorrection

/-!
# The literal Appendix-B height coefficient at `T₀ = exp 11450`

This closes the supremum hidden in Khale's Theorem B.1.  The proof uses a
uniform numerator bound over the entire ray, rather than the false printed
intermediate estimate `≤ 59.8`.
-/

namespace MAPKhaleAppendixBHeightCoefficientBound

open Set
open MAPKhaleAppendixBSource MAPKhaleWeakVKApplication

noncomputable section

def correctionUpper : ℝ :=
  (-2.89 * 2.234 + 14.44 * 4.347 + 3.59) / 9.345

theorem correctionUpper_pos : 0 < correctionUpper := by
  norm_num [correctionUpper]

theorem appendixBCorrection_le_correctionUpper
    {t : ℝ} (ht : Real.exp 11450 ≤ t) :
    appendixBCorrection 76.2 t ≤ correctionUpper := by
  have htpos : 0 < t := (Real.exp_pos 11450).trans_le ht
  have hlogt : (11450 : ℝ) ≤ Real.log t := by
    rw [← Real.log_exp 11450]
    exact Real.log_le_log (Real.exp_pos 11450) ht
  have hlogtpos : 0 < Real.log t := by linarith
  have hloglogt : Real.log 11450 ≤ Real.log (Real.log t) :=
    Real.log_le_log (by norm_num) hlogt
  have hloglogtpos : 0 < Real.log (Real.log t) :=
    (by norm_num : (0 : ℝ) < 9.345).trans
      (log_11450_gt.trans_le hloglogt)
  have hlog3t : Real.log (Real.log 11450) ≤
      Real.log (Real.log (Real.log t)) :=
    Real.log_le_log (lt_trans (by norm_num) log_11450_gt) hloglogt
  let numerator : ℝ :=
    -2.89 * Real.log (Real.log (Real.log t)) +
      14.44 * Real.log (76.2 + 1) + 3.59
  let numeratorUpper : ℝ :=
    -2.89 * 2.234 + 14.44 * 4.347 + 3.59
  have hn : numerator ≤ numeratorUpper := by
    dsimp [numerator, numeratorUpper]
    norm_num [show (76.2 : ℝ) + 1 = 77.2 by norm_num]
    nlinarith [log_log_11450_gt.trans_le hlog3t, log_77_2_lt]
  have hnumUpper : 0 ≤ numeratorUpper := by
    norm_num [numeratorUpper]
  have hfrac₁ : numerator / Real.log (Real.log t) ≤
      numeratorUpper / Real.log (Real.log t) :=
    (div_le_div_iff_of_pos_right hloglogtpos).2 hn
  have hden : (9.345 : ℝ) ≤ Real.log (Real.log t) :=
    log_11450_gt.le.trans hloglogt
  have hfrac₂ : numeratorUpper / Real.log (Real.log t) ≤
      numeratorUpper / 9.345 :=
    div_le_div_of_nonneg_left hnumUpper (by norm_num) hden
  dsimp [appendixBCorrection, correctionUpper]
  exact hfrac₁.trans hfrac₂

theorem appendixBHeightCoefficient_le :
    appendixBHeightCoefficient 76.2 (Real.exp 11450) ≤
      31.76 + correctionUpper := by
  have hnonempty :
      (appendixBCorrection 76.2 '' Set.Ici (Real.exp 11450)).Nonempty := by
    refine ⟨appendixBCorrection 76.2 (Real.exp 11450), ?_⟩
    exact ⟨Real.exp 11450, by simp, rfl⟩
  have hsup : sSup (appendixBCorrection 76.2 '' Set.Ici (Real.exp 11450)) ≤
      correctionUpper := by
    apply csSup_le hnonempty
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    exact appendixBCorrection_le_correctionUpper ht
  have hmax :
      max (sSup (appendixBCorrection 76.2 '' Set.Ici (Real.exp 11450))) 0 ≤
        correctionUpper :=
    max_le hsup correctionUpper_pos.le
  unfold appendixBHeightCoefficient
  linarith

theorem appendixBHeightCoefficient_mul_rpow_lt_104 :
    appendixBHeightCoefficient 76.2 (Real.exp 11450) *
        Real.rpow 4.45 (2 / 3 : ℝ) < 104 := by
  have hcoeff := appendixBHeightCoefficient_le
  have hpow := rpow_4_45_two_thirds_lt
  have hpow0 : 0 ≤ Real.rpow (4.45 : ℝ) (2 / 3 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have hupperPos : 0 < 31.76 + correctionUpper := by
    have := correctionUpper_pos
    linarith
  calc
    appendixBHeightCoefficient 76.2 (Real.exp 11450) *
          Real.rpow 4.45 (2 / 3 : ℝ) ≤
        (31.76 + correctionUpper) * Real.rpow 4.45 (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff hpow0
    _ < (31.76 + correctionUpper) * 2.708 :=
      mul_lt_mul_of_pos_left hpow hupperPos
    _ < 104 := by norm_num [correctionUpper]

end
end MAPKhaleAppendixBHeightCoefficientBound

#print axioms MAPKhaleAppendixBHeightCoefficientBound.appendixBCorrection_le_correctionUpper
#print axioms MAPKhaleAppendixBHeightCoefficientBound.appendixBHeightCoefficient_mul_rpow_lt_104
