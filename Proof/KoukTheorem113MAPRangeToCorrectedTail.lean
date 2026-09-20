import KoukTheorem113SelectedHeightAggregation
import APSignedAlignedFamilyContourAperture

/-!
# MAP-range Koukoulopoulos source to the corrected AP tail

The full-support pointwise theorem is needed only at the mesoscopic MAP height.
This module verifies the eventual height inequalities, chooses one contour legal
for the finite AP family, and feeds the existing corrected-tail consumer.
-/

namespace KoukTheorem113MAPRangeToCorrectedTail

open Set Filter MeasureTheory
open MAPFixedScaleAPZeroRoute
open MAPAPSignedAlignedFamilyContourAperture
open MAPAPCorrectedCommonHeightContract
open MAPKoukTheorem113ToCorrectedTail
open KoukTheorem113SelectedHeightAggregation

noncomputable section

/-- The MAP zero height eventually leaves two full units below the lower
arithmetic endpoint.  The second unit is exactly the room used by the internal
nearby-good-height selection in the source proof. -/
theorem eventually_apZeroHeight_add_two_le_half
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop,
      apZeroHeight (min epsilon (1 / 10)) X + 2 ≤ X / 2 := by
  have hsmall : ∀ᶠ X : ℝ in atTop,
      Real.rpow X (-(2 / 15 : ℝ)) ≤ 1 / 4 := by
    have ht := tendsto_rpow_neg_atTop
      (show 0 < (2 / 15 : ℝ) by norm_num)
    have hnhds : Set.Iio (1 / 4 : ℝ) ∈ nhds (0 : ℝ) :=
      Iio_mem_nhds (by norm_num)
    exact (ht.eventually hnhds).mono fun _ h => h.le
  filter_upwards [hsmall, eventually_ge_atTop (8 : ℝ)] with X hsmallX hX
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hheight :
      apZeroHeight (min epsilon (1 / 10)) X ≤
        Real.rpow X (13 / 15 : ℝ) := by
    unfold apZeroHeight
    apply Real.rpow_le_rpow_of_exponent_le hXone
    have hreserve : 0 ≤ min epsilon (1 / 10) :=
      le_min hepsilon.le (by norm_num)
    linarith
  have hsplit : Real.rpow X (13 / 15 : ℝ) =
      X * Real.rpow X (-(2 / 15 : ℝ)) := by
    calc
      Real.rpow X (13 / 15 : ℝ) =
          Real.rpow X (1 + (-(2 / 15 : ℝ))) := by norm_num
      _ = Real.rpow X 1 * Real.rpow X (-(2 / 15 : ℝ)) :=
        Real.rpow_add hXpos 1 (-(2 / 15 : ℝ))
      _ = X * Real.rpow X (-(2 / 15 : ℝ)) := by
        rw [show Real.rpow X 1 = X by exact Real.rpow_one X]
  have hquarter : Real.rpow X (13 / 15 : ℝ) ≤ X / 4 := by
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left hsmallX hXpos.le]
  linarith [hheight, hquarter]

/-- The MAP height tends to infinity uniformly for the permitted reserve. -/
theorem eventually_four_le_apZeroHeight
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilonCap : epsilon ≤ 13 / 30) :
    ∀ᶠ X : ℝ in atTop,
      4 ≤ apZeroHeight (min epsilon (1 / 10)) X := by
  have hreserveLe : min epsilon (1 / 10) ≤ epsilon := min_le_left _ _
  have htau : 0 < 13 / 15 - min epsilon (1 / 10) / 2 := by
    linarith
  unfold apZeroHeight
  exact (tendsto_rpow_atTop htau).eventually (eventually_ge_atTop 4)

/-- The certified MAP-range pointwise theorem supplies the exact selected
common-height source contract.  The common contour is used only for legality;
the source estimate itself is valid at every height in that legal set. -/
theorem certifiedKoukTheorem113SelectedCommonHeight :
    KoukTheorem113SelectedCommonHeight := by
  rcases certifiedKoukTheorem113MAPRangePointwise with ⟨C, hC, hbound⟩
  intro K epsilon hK hepsilon hepsilonCap
  have htwo := eventually_apZeroHeight_add_two_le_half epsilon hepsilon
  have hfour := eventually_four_le_apZeroHeight epsilon hepsilon hepsilonCap
  have hlarge : ∀ᶠ X : ℝ in atTop, 2 * Real.exp 2 ≤ X :=
    eventually_ge_atTop (2 * Real.exp 2)
  have hall : ∀ᶠ X : ℝ in atTop,
      apZeroHeight (min epsilon (1 / 10)) X + 2 ≤ X / 2 ∧
      4 ≤ apZeroHeight (min epsilon (1 / 10)) X ∧
      2 * Real.exp 2 ≤ X := by
    filter_upwards [htwo, hfour, hlarge] with X h2 h4 hX
    exact ⟨h2, h4, hX⟩
  rw [eventually_atTop] at hall
  rcases hall with ⟨Xevent, hXevent⟩
  let X0 : ℝ := max 2 Xevent
  refine ⟨C, X0, hC, le_max_left 2 Xevent, ?_⟩
  intro X hXX0
  dsimp only
  let reserve := min epsilon (1 / 10)
  let H := apZeroHeight reserve X
  let Q := ⌊Real.rpow (Real.log X) K⌋₊
  have hXXevent : Xevent ≤ X :=
    (le_max_right 2 Xevent).trans hXX0
  have hscales := hXevent X hXXevent
  have hHpos : 0 < H := by dsimp [H]; linarith [hscales.2.1]
  obtain ⟨G, sigma, hGmeas, hGvolume, hGsub, hsigma, hGlegal⟩ :=
    exists_familyExerciseGoodHeightSmallEdgesLegal Q hHpos
      (show 0 < (1 / 4 : ℝ) by norm_num)
      (show (1 / 4 : ℝ) ≤ 1 / 2 by norm_num)
  have hGnonempty : G.Nonempty := by
    by_contra hGempty
    have hEq : G = ∅ := Set.not_nonempty_iff_eq_empty.mp hGempty
    rw [hEq] at hGvolume
    norm_num at hGvolume
  obtain ⟨T, hTG⟩ := hGnonempty
  have hTIoo : T ∈ Set.Ioo H (H + 1) := hGsub hTG
  refine ⟨T, hTIoo, sigma, ?_, ?_⟩
  · exact hGlegal T hTG
  · intro q hq chi
    letI : NeZero q := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
    intro t htIcc
    apply hbound q chi T t
    · linarith [hscales.2.1, hTIoo.1]
    · linarith [hscales.1, hTIoo.2, htIcc.1]
    · linarith [hscales.2.2, htIcc.1]

/-- Premise-free Koukoulopoulos contribution to the corrected AP endpoint. -/
theorem certifiedCorrectedAPExplicitFormulaTailFamilySquare :
    MAPAPCorrectedPaperEdgeTail.CorrectedAPExplicitFormulaTailFamilySquare :=
  correctedAPExplicitFormulaTailFamilySquare_of_selectedCommonHeight
    certifiedKoukTheorem113SelectedCommonHeight

#print axioms eventually_apZeroHeight_add_two_le_half
#print axioms eventually_four_le_apZeroHeight
#print axioms certifiedKoukTheorem113SelectedCommonHeight
#print axioms certifiedCorrectedAPExplicitFormulaTailFamilySquare

end
end KoukTheorem113MAPRangeToCorrectedTail
