import KhaleAppendixB1HighZeroReduction

/-!
# The last numerical rounding in Khale Appendix B.1

The remaining premise in this file is the penultimate displayed inequality of
Khale's proof.  The conversion from its constants
`0.953, 16.66375, 30.26576, -2.7545, 13.75563, 3.33` to the theorem constants
is certified below, rather than trusted to decimal arithmetic.
-/

namespace MAPKhaleAppendixB1PenultimateReduction

open MAPKhaleAppendixBSource MAPKhaleAppendixB1FinalReduction
open MAPKhaleAppendixB1HighZeroReduction

noncomputable section

/-- Literal penultimate display in the proof of Appendix-B Theorem B.1. -/
abbrev AppendixBPenultimateZeroEstimate : Prop :=
  ∀ (A B T₀ : ℝ),
    0 < A → 0 < B → B ≤ 4.45 →
    FordHurwitzEquation12 A B →
    Real.exp 10650 ≤ T₀ →
    5110.6 / B ≤ Real.log T₀ / Real.log (Real.log T₀) →
    183 / B ^ 2 ≤ Real.log (Real.log T₀) →
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
        (gamma beta : ℝ),
      3 ≤ q → T₀ ≤ gamma →
      Real.rpow (q : ℝ) (1 / 100000 : ℝ) ≤ gamma →
      1 - beta ≤ 1 /
        (18 * Real.log q + appendixBHeightCoefficient A T₀ *
          Real.rpow B (2 / 3 : ℝ) *
          Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)) →
      DirichletCharacter.LFunction chi
          ((beta : ℂ) + (gamma : ℂ) * Complex.I) = 0 →
      beta < 1 ∧
      0.953 / (1 - beta) ≤
        16.66375 * Real.log q +
          (30.26576 +
            (-2.7545 * Real.log (Real.log (Real.log gamma)) +
              13.75563 * Real.log (A + 1) + 3.33) /
                Real.log (Real.log gamma)) *
            Real.rpow B (2 / 3 : ℝ) *
            Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
            Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)

private theorem penultimate_coefficient_le_final
    {A gamma : ℝ} (hA : 0 < A)
    (hgamma : Real.exp 10650 ≤ gamma) :
    30.26576 +
        (-2.7545 * Real.log (Real.log (Real.log gamma)) +
          13.75563 * Real.log (A + 1) + 3.33) /
            Real.log (Real.log gamma) ≤
      0.953 * (31.76 + appendixBFinalCorrection A gamma) := by
  have hgammaPos : 0 < gamma := (Real.exp_pos 10650).trans_le hgamma
  have hloggamma : (10650 : ℝ) ≤ Real.log gamma := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) hgamma
  have hlogloggamma : Real.log 10650 ≤ Real.log (Real.log gamma) :=
    Real.log_le_log (by norm_num) hloggamma
  have hlogloggammaPos : 0 < Real.log (Real.log gamma) := by
    exact Real.log_pos (by norm_num : (1 : ℝ) < 10650) |>.trans_le hlogloggamma
  have hlog3gammaNonneg :
      0 ≤ Real.log (Real.log (Real.log gamma)) :=
    Real.log_nonneg (show 1 ≤ Real.log (Real.log gamma) by
      have hone : (1 : ℝ) < Real.log 10650 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 10650)]
        exact Real.exp_one_lt_three.trans (by norm_num)
      exact hone.le.trans hlogloggamma)
  have hlogAPos : 0 < Real.log (A + 1) := Real.log_pos (by linarith)
  unfold appendixBFinalCorrection
  field_simp [ne_of_gt hlogloggammaPos]
  nlinarith

/-- The penultimate source display implies the exact high-zero reciprocal
estimate used by the deterministic theorem weld. -/
theorem highZeroReciprocalEstimate_of_penultimate
    (hPenultimate : AppendixBPenultimateZeroEstimate) :
    AppendixBHighZeroReciprocalEstimate := by
  intro A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q _inst chi gamma beta hq hgamma hqheight hgap hzero
  have hpen := hPenultimate A B T₀ hA hB hBtop hFord hT₀ hratio hloglog
    q chi gamma beta hq hgamma hqheight hgap hzero
  refine ⟨hpen.1, ?_⟩
  let P : ℝ := Real.rpow B (2 / 3 : ℝ) *
    Real.rpow (Real.log gamma) (2 / 3 : ℝ) *
    Real.rpow (Real.log (Real.log gamma)) (1 / 3 : ℝ)
  have hgamma0 : Real.exp 10650 ≤ gamma := hT₀.trans hgamma
  have hgammaPos : 0 < gamma := (Real.exp_pos 10650).trans_le hgamma0
  have hloggamma : (10650 : ℝ) ≤ Real.log gamma := by
    rw [← Real.log_exp 10650]
    exact Real.log_le_log (Real.exp_pos 10650) hgamma0
  have hloggammaPos : 0 < Real.log gamma := by linarith
  have hlogloggamma : Real.log 10650 ≤ Real.log (Real.log gamma) :=
    Real.log_le_log (by norm_num) hloggamma
  have hlogloggammaPos : 0 < Real.log (Real.log gamma) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 10650) |>.trans_le hlogloggamma
  have hPpos : 0 < P := by
    dsimp [P]
    exact mul_pos
      (mul_pos (Real.rpow_pos_of_pos hB _)
        (Real.rpow_pos_of_pos hloggammaPos _))
      (Real.rpow_pos_of_pos hlogloggammaPos _)
  let Cpen : ℝ := 30.26576 +
    (-2.7545 * Real.log (Real.log (Real.log gamma)) +
      13.75563 * Real.log (A + 1) + 3.33) /
        Real.log (Real.log gamma)
  let Cfinal : ℝ := 31.76 + appendixBFinalCorrection A gamma
  have hcoeff : Cpen ≤ 0.953 * Cfinal := by
    exact penultimate_coefficient_le_final hA hgamma0
  have hqlogNonneg : 0 ≤ Real.log q := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ q by omega)
  have hRhsCompare :
      16.66375 * Real.log q + Cpen * P ≤
        0.953 * (17.49 * Real.log q + Cfinal * P) := by
    have hcoefMul := mul_le_mul_of_nonneg_right hcoeff hPpos.le
    nlinarith
  have hpen' : 0.953 / (1 - beta) ≤
      16.66375 * Real.log q + Cpen * P := by
    simpa only [Cpen, P, mul_assoc] using hpen.2
  have hscaled : 0.953 / (1 - beta) ≤
      0.953 * (17.49 * Real.log q + Cfinal * P) :=
    hpen'.trans hRhsCompare
  have hfinal : 1 / (1 - beta) ≤
      17.49 * Real.log q + Cfinal * P := by
    have hconst : (0 : ℝ) < 0.953 := by norm_num
    have hscaled' : 0.953 * (1 / (1 - beta)) ≤
        0.953 * (17.49 * Real.log q + Cfinal * P) := by
      simpa [div_eq_mul_inv] using hscaled
    nlinarith [hscaled']
  simpa only [Cfinal, P, add_comm, mul_assoc] using hfinal

end
end MAPKhaleAppendixB1PenultimateReduction

#print axioms MAPKhaleAppendixB1PenultimateReduction.highZeroReciprocalEstimate_of_penultimate
