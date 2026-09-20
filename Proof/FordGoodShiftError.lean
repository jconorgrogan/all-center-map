import FordSmallShiftCount
import FordDiscretePairCount
import FordScaleFloor

noncomputable section
namespace FordGoodShiftError
open FordDiscretePairCount FordSmallShiftCount

def goodShifts (Q : ℕ) (A : ℝ) : Finset ℕ :=
  (positiveRange Q).filter (fun h => (Q : ℝ) * A ≤ (h : ℝ))

theorem error_le {Q : ℕ} (hQ : 1 ≤ Q) {A : ℝ} (hA : 0 ≤ A) :
    2 / (Q : ℝ) + 4 * ((positiveRange Q \ goodShifts Q A).card : ℝ) / Q ≤
      4 * A + 6 / Q := by
  have hsub : positiveRange Q \ goodShifts Q A ⊆ smallShifts Q ((Q : ℝ) * A) := by
    intro h hh
    obtain ⟨hp, hg⟩ := Finset.mem_sdiff.mp hh
    have hlt : (h : ℝ) < (Q : ℝ) * A := by
      by_contra hn
      exact hg (Finset.mem_filter.mpr ⟨hp, le_of_not_gt hn⟩)
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, hlt⟩
  have hc : ((positiveRange Q \ goodShifts Q A).card : ℝ) ≤
      ((smallShifts Q ((Q : ℝ) * A)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hq : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hf := fraction_smallShifts_le hQ hA
  have hd := div_le_div_of_nonneg_right hc hq.le
  calc
    _ = 2 / (Q : ℝ) + 4 * (((positiveRange Q \ goodShifts Q A).card : ℝ) / Q) := by ring
    _ ≤ 4 * A + 6 / Q := by
      simp only [div_eq_mul_inv] at hf hd ⊢
      linarith

theorem inverse_scale_le {N : ℕ} {q eps : ℝ}
    (hN : 1 ≤ N) (heps : 0 ≤ eps) (heq : eps ≤ q) :
    1 / (FordScaleFloor.scale N q : ℝ) ≤ 2 * (N : ℝ) ^ (-eps) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hs := FordScaleFloor.scale_comparable hN (heps.trans heq)
  have hQ : (0 : ℝ) < FordScaleFloor.scale N q := by exact_mod_cast (show 0 < FordScaleFloor.scale N q by omega)
  have hp : (N : ℝ) ^ eps ≤ (N : ℝ) ^ q := Real.rpow_le_rpow_of_exponent_le hn heq
  have hp0 : 0 < (N : ℝ) ^ eps := Real.rpow_pos_of_pos hn0 _
  rw [Real.rpow_neg hn0.le]
  apply (div_le_iff₀ hQ).2
  have hh : (N : ℝ) ^ eps ≤ 2 * (FordScaleFloor.scale N q : ℝ) := by linarith [hs.2.2]
  have hm := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hp0.le)
  have hid : ((N : ℝ) ^ eps)⁻¹ * (N : ℝ) ^ eps = 1 := inv_mul_cancel₀ hp0.ne'
  nlinarith

theorem error_scale_le {N : ℕ} {q eps : ℝ}
    (hN : 1 ≤ N) (heps : 0 ≤ eps) (heq : eps ≤ q) :
    let Q := FordScaleFloor.scale N q
    let A := (N : ℝ) ^ (-eps)
    2 / (Q : ℝ) + 4 * ((positiveRange Q \ goodShifts Q A).card : ℝ) / Q ≤
      16 * A := by
  dsimp only
  have hQ := (FordScaleFloor.scale_comparable hN (heps.trans heq)).1
  have he := error_le hQ (Real.rpow_nonneg (Nat.cast_nonneg N) (-eps))
  have hi := inverse_scale_le hN heps heq
  simp only [div_eq_mul_inv] at he hi ⊢
  linarith

end FordGoodShiftError
#print axioms FordGoodShiftError.error_le
#print axioms FordGoodShiftError.inverse_scale_le
#print axioms FordGoodShiftError.error_scale_le
