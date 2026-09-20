import KhaleAppendixBSourceReduction
import KhaleWeakVKConstantCorrection

/-!
# Khale Appendix B, Theorem B.1 from its final reciprocal zero estimate

This file separates the last deterministic part of the proof of Theorem B.1
from the analytic argument producing the displayed reciprocal estimate.  The
remaining proposition is the literal estimate in the final display of the
published proof, including its stronger constants `3.495` and `17.49`.
-/

namespace MAPKhaleAppendixB1FinalReduction

open Set
open MAPKhaleAppendixBSource MAPKhaleWeakVKApplication

noncomputable section

/-- The height correction in the final displayed reciprocal estimate of the
proof.  Its constant `3.495` is strictly smaller than the `3.59` used in the
statement of Theorem B.1. -/
def appendixBFinalCorrection (A t : ℝ) : ℝ :=
  (-2.89 * Real.log (Real.log (Real.log t)) +
      14.44 * Real.log (A + 1) + 3.495) /
    Real.log (Real.log t)

/-- The exact last analytic estimate in the printed proof of Appendix-B
Theorem B.1.  Unlike the theorem itself, this is a conditional estimate about
an already existing zero and retains the reciprocal information from
`(lazykey)`.  The proof in Khale derives it from Lemma 4.1, equation (5.1),
Lemma 5.1, the cotangent bound, and the zeta bound. -/
abbrev AppendixBFinalReciprocalZeroEstimate : Prop :=
  ∀ (A B T₀ : ℝ),
    0 < A → 0 < B → B ≤ 4.45 →
    FordHurwitzEquation12 A B →
    Real.exp 10650 ≤ T₀ →
    5110.6 / B ≤ Real.log T₀ / Real.log (Real.log T₀) →
    183 / B ^ 2 ≤ Real.log (Real.log T₀) →
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
        (gamma beta : ℝ),
      3 ≤ q → T₀ ≤ gamma →
      1 - beta ≤ 1 /
        (18 * Real.log q + appendixBHeightCoefficient A T₀ *
          Real.rpow B (2 / 3 : ℝ) *
          Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)) →
      DirichletCharacter.LFunction chi
          ((beta : ℂ) + (gamma : ℂ) * Complex.I) = 0 →
      beta < 1 ∧
      1 / (1 - beta) ≤
        (31.76 + appendixBFinalCorrection A gamma) *
            Real.rpow B (2 / 3 : ℝ) *
            Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
            Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ) +
          17.49 * Real.log q

private theorem height_log_facts
    {T₀ t : ℝ} (hT₀ : Real.exp 10650 ≤ T₀) (ht : T₀ ≤ t) :
    1 ≤ Real.log (Real.log t) ∧
      0 ≤ Real.log (Real.log (Real.log t)) := by
  have htPos : 0 < t := (Real.exp_pos 10650).trans_le (hT₀.trans ht)
  have hlogt : (10650 : ℝ) ≤ Real.log t := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) (hT₀.trans ht)
  have hlogtPos : 0 < Real.log t := by linarith
  have hloglogt : Real.log 10650 ≤ Real.log (Real.log t) :=
    Real.log_le_log (by norm_num) hlogt
  have hone : (1 : ℝ) ≤ Real.log (Real.log t) := by
    have hlog10650 : 1 < Real.log (10650 : ℝ) := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 10650)]
      exact Real.exp_one_lt_three.trans (by norm_num)
    exact hlog10650.le.trans hloglogt
  exact ⟨hone, Real.log_nonneg hone⟩

private theorem appendixBCorrection_bddAbove
    {A T₀ : ℝ} (hA : 0 < A) (hT₀ : Real.exp 10650 ≤ T₀) :
    BddAbove (appendixBCorrection A '' Set.Ici T₀) := by
  let C : ℝ := 14.44 * Real.log (A + 1) + 3.59
  have hA1 : 1 < A + 1 := by linarith
  have hCpos : 0 < C := by
    dsimp [C]
    have := Real.log_pos hA1
    positivity
  refine ⟨C, ?_⟩
  intro y hy
  rcases hy with ⟨t, ht, rfl⟩
  have hfacts := height_log_facts hT₀ ht
  have hdenPos : 0 < Real.log (Real.log t) := zero_lt_one.trans_le hfacts.1
  apply (div_le_iff₀ hdenPos).2
  have hnum :
      -2.89 * Real.log (Real.log (Real.log t)) +
          14.44 * Real.log (A + 1) + 3.59 ≤ C := by
    dsimp [C]
    nlinarith [hfacts.2]
  have hCden : C ≤ C * Real.log (Real.log t) := by
    nlinarith [hfacts.1, hCpos]
  exact hnum.trans hCden

theorem appendixBFinalCorrection_le_heightMax
    {A T₀ t : ℝ} (hA : 0 < A) (hT₀ : Real.exp 10650 ≤ T₀)
    (ht : T₀ ≤ t) :
    31.76 + appendixBFinalCorrection A t ≤
      appendixBHeightCoefficient A T₀ := by
  have hbdd := appendixBCorrection_bddAbove hA hT₀
  have hmem : appendixBCorrection A t ∈
      appendixBCorrection A '' Set.Ici T₀ := ⟨t, ht, rfl⟩
  have hleSup : appendixBCorrection A t ≤
      sSup (appendixBCorrection A '' Set.Ici T₀) :=
    le_csSup hbdd hmem
  have hfinal : appendixBFinalCorrection A t ≤ appendixBCorrection A t := by
    have hfacts := height_log_facts hT₀ ht
    have hdenPos : 0 < Real.log (Real.log t) := zero_lt_one.trans_le hfacts.1
    unfold appendixBFinalCorrection appendixBCorrection
    apply (div_le_div_iff_of_pos_right hdenPos).2
    norm_num
  unfold appendixBHeightCoefficient
  linarith [hfinal.trans hleSup, le_max_left
    (sSup (appendixBCorrection A '' Set.Ici T₀)) 0]

/-- Every deterministic step after Khale's final reciprocal display.  This
proves Theorem B.1 from that display and leaves no zero-free-region statement
as an implicit convention. -/
theorem appendixBTheoremB1_of_finalReciprocalEstimate
    (hFinal : AppendixBFinalReciprocalZeroEstimate) :
    AppendixBTheoremB1 := by
  intro A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q _inst chi gamma beta hq hgamma hboundary
  intro hzero
  have hrecip := hFinal A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q chi gamma beta hq hgamma (by linarith [hboundary]) hzero
  let P : ℝ :=
    Real.rpow B (2 / 3 : ℝ) *
      Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
      Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)
  let D : ℝ := 18 * Real.log q + appendixBHeightCoefficient A T₀ * P
  have hfacts := height_log_facts hT₀ hgamma
  have hgammaPos : 0 < gamma :=
    (Real.exp_pos 10650).trans_le (hT₀.trans hgamma)
  have hloggammaPos : 0 < Real.log gamma := by
    have : (10650 : ℝ) ≤ Real.log gamma := by
      rw [← Real.log_exp 10650]
      exact Real.log_le_log (Real.exp_pos 10650) (hT₀.trans hgamma)
    linarith
  have hlogloggammaPos : 0 < Real.log (Real.log gamma) :=
    zero_lt_one.trans_le hfacts.1
  have hPpos : 0 < P := by
    dsimp [P]
    exact mul_pos
      (mul_pos (Real.rpow_pos_of_pos hB _)
        (Real.rpow_pos_of_pos hloggammaPos _))
      (Real.rpow_pos_of_pos hlogloggammaPos _)
  have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogqPos : 0 < Real.log q :=
    Real.log_pos ((by norm_num : (1 : ℝ) < 3).trans_le hqReal)
  have hcoeffPos : 0 < appendixBHeightCoefficient A T₀ := by
    unfold appendixBHeightCoefficient
    have : (0 : ℝ) ≤ max (sSup (appendixBCorrection A '' Set.Ici T₀)) 0 :=
      le_max_right _ _
    linarith
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hcorr := appendixBFinalCorrection_le_heightMax hA hT₀ hgamma
  have hRhsLeD :
      (31.76 + appendixBFinalCorrection A gamma) * P +
          17.49 * Real.log q ≤ D := by
    dsimp [D]
    have hmul := mul_le_mul_of_nonneg_right hcorr hPpos.le
    nlinarith
  have hrecip' : 1 / (1 - beta) ≤
      (31.76 + appendixBFinalCorrection A gamma) * P +
        17.49 * Real.log q := by
    simpa only [P, mul_assoc] using hrecip.2
  have hdeltaPos : 0 < 1 - beta := by linarith [hrecip.1]
  have hboundaryD : 1 - 1 / D < beta := by
    simpa only [D, P, mul_assoc] using hboundary
  have hdeltaLt : 1 - beta < 1 / D := by linarith
  have hDltRecip : D < 1 / (1 - beta) := by
    have hinv := one_div_lt_one_div_of_lt hdeltaPos hdeltaLt
    simpa only [one_div, inv_inv] using hinv
  exact (not_lt_of_ge (hrecip'.trans hRhsLeD)) hDltRecip

end
end MAPKhaleAppendixB1FinalReduction

#print axioms MAPKhaleAppendixB1FinalReduction.appendixBTheoremB1_of_finalReciprocalEstimate
