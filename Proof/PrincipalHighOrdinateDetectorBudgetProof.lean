import PrincipalZetaStructuredSplitFromFourthMoment

/-!
# Close the high-ordinate crossed-pole detector budget

After the certified low-ordinate exception split, the pole residue and the
degree-six principal vertical tail both contain Gaussian/exponential decay at
least as strong as the paper's `B=(log T)^2` cutoff.  This file absorbs those
two terms together with the ordinary arithmetic tail and detector thresholds.
-/

namespace MAPPrincipalHighOrdinateDetectorBudgetProof

open Filter
open CGLProofDAG MAPAppendixA4DetectorDichotomy
open MAPAppendixA4RecenteredGammaRepair
open PostA5RecenteredDetectorAbsorption
open MAPPrincipalZetaDetectorPoleRemoval MAPPrincipalZetaDetectorDichotomy
open MAPPrincipalZetaStructuredSplitFromFourthMoment

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

/-- The explicit degree-six principal vertical tail is an arbitrary negative
power at the paper cutoff. -/
theorem principal_vertical_tail_le_rpow_neg
    {T u c d : ℝ} {U : ℕ} {rho : ℂ}
    (hT : 1 ≤ T)
    (hUscale : (U + 1 : ℝ) ≤ Real.rpow T u)
    (hheight : |rho.im| ≤ T)
    (hconst :
      (1 / (2 * Real.pi)) *
        (4 * (12 * 3200 * 5 ^ 6 * (2 : ℝ) ^ 7 *
          (Nat.factorial 7 : ℝ) * Real.exp (1 / 2))) ≤ Real.rpow T c)
    (hgap : 2 * (c + u + 6 + d) ≤ Real.log T) :
    (1 / (2 * Real.pi)) *
      (4 * (12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
        (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
          Real.exp (-(detectorVerticalCutoff T) / 2)) ≤
      Real.rpow T (-d) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hT0 : 0 ≤ T := hTpos.le
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlinear : 4 + |rho.im| ≤ 5 * T := by linarith
  have hsix : (4 + |rho.im|) ^ 6 ≤ 5 ^ 6 * T ^ 6 := by
    calc
      (4 + |rho.im|) ^ 6 ≤ (5 * T) ^ 6 := by gcongr
      _ = 5 ^ 6 * T ^ 6 := by ring
  let C : ℝ := (1 / (2 * Real.pi)) *
    (4 * (12 * 3200 * 5 ^ 6 * (2 : ℝ) ^ 7 *
      (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)))
  have hraw :
      (1 / (2 * Real.pi)) *
        (4 * (12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
          (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
            Real.exp (-(detectorVerticalCutoff T) / 2)) ≤
        C * (Real.rpow T u * T ^ 6) *
          Real.exp (-(Real.log T) ^ 2 / 2) := by
    unfold detectorVerticalCutoff
    dsimp [C]
    calc
      (1 / (2 * Real.pi)) *
          (4 * (12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
            (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
              Real.exp (-(Real.log T) ^ 2 / 2)) ≤
        (1 / (2 * Real.pi)) *
          (4 * (12 * 3200 * Real.rpow T u * (5 ^ 6 * T ^ 6) *
            (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
              Real.exp (-(Real.log T) ^ 2 / 2)) := by
        gcongr
        exact mul_nonneg (by positivity) (Real.rpow_nonneg hT0 _)
      _ = ((1 / (2 * Real.pi)) *
          (4 * (12 * 3200 * 5 ^ 6 * (2 : ℝ) ^ 7 *
            (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)))) *
          (Real.rpow T u * T ^ 6) *
            Real.exp (-(Real.log T) ^ 2 / 2) := by ring
  have hTpow : T ^ 6 = Real.rpow T (6 : ℝ) := by
    exact (Real.rpow_natCast T 6).symm
  have hmerge : Real.rpow T c * (Real.rpow T u * T ^ 6) =
      Real.rpow T (c + u + 6) := by
    rw [hTpow]
    calc
      Real.rpow T c * (Real.rpow T u * Real.rpow T (6 : ℝ)) =
          Real.rpow T c * Real.rpow T (u + 6) := by
        congr 1
        exact (Real.rpow_add hTpos _ _).symm
      _ = Real.rpow T (c + (u + 6)) :=
        (Real.rpow_add hTpos _ _).symm
      _ = Real.rpow T (c + u + 6) := by congr 1 <;> ring
  calc
    (1 / (2 * Real.pi)) *
        (4 * (12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
          (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
            Real.exp (-(detectorVerticalCutoff T) / 2)) ≤
        C * (Real.rpow T u * T ^ 6) *
          Real.exp (-(Real.log T) ^ 2 / 2) := hraw
    _ ≤ Real.rpow T c * (Real.rpow T u * T ^ 6) *
          Real.exp (-(Real.log T) ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconst
          (mul_nonneg (Real.rpow_nonneg hT0 _) (by positivity)))
        (Real.exp_nonneg _)
    _ = Real.rpow T (c + u + 6) *
          Real.exp (-(Real.log T) ^ 2 / 2) := by rw [hmerge]
    _ ≤ Real.rpow T (-d) :=
      rpow_mul_exp_neg_half_log_sq_le_rpow_neg hTpos hlog0 hgap

/-- The crossed-pole residue is an arbitrary negative power once
`|Im rho|` lies beyond the paper vertical cutoff. -/
theorem principal_residue_le_rpow_neg
    {T u c d : ℝ} {U : ℕ} {rho : ℂ}
    (hT : 1 ≤ T)
    (hzero : principalF rho = 0)
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    (hcut : detectorVerticalCutoff T ≤ |rho.im|)
    (hlogOne : 1 ≤ Real.log T)
    (hUscale : (U + 1 : ℝ) ≤ Real.rpow T u)
    (hconst : 24 ≤ Real.rpow T c)
    (hgap : c + 3 / 20 + u + d ≤ Real.log T) :
    ‖principalDetectorResidue rho U (Real.rpow T (1 / 2))‖ ≤
      Real.rpow T (-d) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hT0 : 0 ≤ T := hTpos.le
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hcutOne : 1 ≤ detectorVerticalCutoff T := by
    unfold detectorVerticalCutoff
    nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hlogOne]
  have himOne : 1 ≤ |rho.im| := hcutOne.trans hcut
  have hrhoOne : rho ≠ 1 := by
    intro hrho
    subst rho
    norm_num [principalRegularized_one] at hzero
  have hYpos : 0 < Real.rpow T (1 / 2) := Real.rpow_pos_of_pos hTpos _
  have hres := norm_principalDetectorResidue_le (U := U) hzero hrhoOne
    (by linarith) hbetaHigh himOne hYpos
  have hratio : (1 + |rho.im|) * (1 / |rho.im|) ≤ 2 := by
    have himpos : 0 < |rho.im| := zero_lt_one.trans_le himOne
    simpa [div_eq_mul_inv] using
      ((div_le_iff₀ himpos).2 (show 1 + |rho.im| ≤ 2 * |rho.im| by
        linarith))
  have hexp : Real.exp (-|rho.im|) ≤
      Real.exp (-(Real.log T) ^ 2) := by
    apply Real.exp_le_exp.mpr
    unfold detectorVerticalCutoff at hcut
    linarith
  have hYone : 1 ≤ Real.rpow T (1 / 2) :=
    Real.one_le_rpow hT (by norm_num)
  have hYbeta : Real.rpow (Real.rpow T (1 / 2)) (1 - rho.re) ≤
      Real.rpow (Real.rpow T (1 / 2)) (3 / 10) :=
    Real.rpow_le_rpow_of_exponent_le hYone (by linarith)
  have hYeval : Real.rpow (Real.rpow T (1 / 2)) (3 / 10) =
      Real.rpow T (3 / 20) := by
    calc
      Real.rpow (Real.rpow T (1 / 2)) (3 / 10) =
          Real.rpow T ((1 / 2 : ℝ) * (3 / 10)) :=
        (Real.rpow_mul hT0 _ _).symm
      _ = Real.rpow T (3 / 20) := by congr 1 <;> ring
  have hfront :
      12 * (1 + |rho.im|) * Real.exp (-|rho.im|) *
          (1 / |rho.im|) ≤
        24 * Real.exp (-(Real.log T) ^ 2) := by
    calc
      12 * (1 + |rho.im|) * Real.exp (-|rho.im|) *
          (1 / |rho.im|) =
        12 * ((1 + |rho.im|) * (1 / |rho.im|)) *
          Real.exp (-|rho.im|) := by ring
      _ ≤ 12 * 2 * Real.exp (-(Real.log T) ^ 2) := by
        gcongr
      _ = 24 * Real.exp (-(Real.log T) ^ 2) := by ring
  have hraw : ‖principalDetectorResidue rho U (Real.rpow T (1 / 2))‖ ≤
      24 * Real.rpow T (3 / 20) * Real.rpow T u *
        Real.exp (-(Real.log T) ^ 2) := by
    calc
      ‖principalDetectorResidue rho U (Real.rpow T (1 / 2))‖ ≤
          12 * (1 + |rho.im|) * Real.exp (-|rho.im|) *
            (1 / |rho.im|) *
            Real.rpow (Real.rpow T (1 / 2)) (1 - rho.re) *
            (U + 1) := hres
      _ ≤ (24 * Real.exp (-(Real.log T) ^ 2)) *
          Real.rpow (Real.rpow T (1 / 2)) (3 / 10) *
          Real.rpow T u := by
        gcongr
        · exact mul_nonneg
            (mul_nonneg (by norm_num) (Real.exp_nonneg _))
            (Real.rpow_nonneg (Real.rpow_nonneg hT0 _) _)
        · exact Real.rpow_nonneg (Real.rpow_nonneg hT0 _) _
      _ = 24 * Real.rpow T (3 / 20) * Real.rpow T u *
          Real.exp (-(Real.log T) ^ 2) := by rw [hYeval]; ring
  have hmerge : Real.rpow T c * Real.rpow T (3 / 20) *
      Real.rpow T u = Real.rpow T (c + 3 / 20 + u) := by
    change T ^ c * T ^ (3 / 20 : ℝ) * T ^ u =
      T ^ (c + 3 / 20 + u)
    calc
      T ^ c * T ^ (3 / 20 : ℝ) * T ^ u =
          T ^ (c + 3 / 20) * T ^ u := by
        rw [← Real.rpow_add hTpos]
      _ = T ^ ((c + 3 / 20) + u) :=
        (Real.rpow_add hTpos _ _).symm
      _ = T ^ (c + 3 / 20 + u) := by congr 1 <;> ring
  calc
    ‖principalDetectorResidue rho U (Real.rpow T (1 / 2))‖ ≤
        24 * Real.rpow T (3 / 20) * Real.rpow T u *
          Real.exp (-(Real.log T) ^ 2) := hraw
    _ ≤ Real.rpow T c * Real.rpow T (3 / 20) * Real.rpow T u *
          Real.exp (-(Real.log T) ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hconst
            (Real.rpow_nonneg hT0 _))
          (Real.rpow_nonneg hT0 _))
        (Real.exp_nonneg _)
    _ = Real.rpow T (c + 3 / 20 + u) *
          Real.exp (-(Real.log T) ^ 2) := by rw [hmerge]
    _ ≤ Real.rpow T (-d) :=
      rpow_mul_exp_neg_log_sq_le_rpow_neg hTpos hlog0 hgap

/-! ## Premise-free high-ordinate budget -/

/-- Once the low ordinates have been removed, the residue-aware principal
detector has the exact source-normalized budget required by the structured
split.  The proof charges the arithmetic tail, the degree-six vertical tail,
and the crossed-pole residue separately. -/
theorem principalHighOrdinateDetectorBudget_unconditional :
    PrincipalHighOrdinateDetectorBudget := by
  intro kappa eta hkappa hkappaCap heta
  let delta : ℝ := inputLoss kappa eta
  let Cvert : ℝ :=
    (1 / (2 * Real.pi)) *
      (4 * (12 * 3200 * 5 ^ 6 * (2 : ℝ) ^ 7 *
        (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)))
  let L : ℝ := max (2 * kappa + 1 + 1 / 2 + 1)
    (max (2 * (1 + 2 * kappa + 6 + 1))
      (1 + 3 / 20 + 2 * kappa + 1))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact inputLoss_pos hkappa heta
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop L)
  have hVgrow := (tendsto_rpow_atTop hdelta).eventually
    (eventually_ge_atTop 16)
  have hYgrow :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually
      (eventually_ge_atTop 2)
  have hpowGrow := (tendsto_rpow_atTop hkappa).eventually
    (eventually_ge_atTop 2)
  filter_upwards [hlog, hVgrow, hYgrow, hpowGrow,
    eventually_ge_atTop (Real.exp 1), eventually_ge_atTop Cvert,
    eventually_ge_atTop 24, eventually_ge_atTop 16] with
      T hlogT hVgrowT hYgrowT hpowGrowT hTexp hTvert hTres hT16
  intro rho hzero hbetaLow hbetaHigh hcut hheight
  have hT : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hT0 : 0 ≤ T := hTpos.le
  have hlogOne : 1 ≤ Real.log T := by
    exact (Real.le_log_iff_exp_le hTpos).2 hTexp
  have hUscale :
      (⌊Real.rpow T kappa⌋₊ + 1 : ℝ) ≤ Real.rpow T (2 * kappa) := by
    have hpow0 : 0 ≤ Real.rpow T kappa := Real.rpow_nonneg hT0 _
    have hfloor : (⌊Real.rpow T kappa⌋₊ : ℝ) ≤
        Real.rpow T kappa := Nat.floor_le hpow0
    have hpowGrowT' : 2 ≤ Real.rpow T kappa := by exact hpowGrowT
    have hquad : Real.rpow T kappa + 1 ≤
        Real.rpow T kappa * Real.rpow T kappa := by
      have hx : 0 ≤ Real.rpow T kappa - 2 := by linarith
      have hxx : 0 ≤ (Real.rpow T kappa - 2) *
          (Real.rpow T kappa - 2) := mul_nonneg hx hx
      nlinarith
    calc
      (⌊Real.rpow T kappa⌋₊ + 1 : ℝ) ≤
          Real.rpow T kappa + 1 := by linarith
      _ ≤ Real.rpow T kappa * Real.rpow T kappa := hquad
      _ = Real.rpow T (2 * kappa) := by
        change T ^ kappa * T ^ kappa = T ^ (2 * kappa)
        rw [← Real.rpow_add hTpos]
        congr 1
        ring
  have hconstArith : Real.exp 1 ≤ Real.rpow T (1 : ℝ) := by
    simpa [Real.rpow_one] using hTexp
  have hconstVert : Cvert ≤ Real.rpow T (1 : ℝ) := by
    simpa [Real.rpow_one] using hTvert
  have hconstRes : 24 ≤ Real.rpow T (1 : ℝ) := by
    simpa [Real.rpow_one] using hTres
  have hgapArith : 2 * kappa + 1 + 1 / 2 + 1 ≤ Real.log T :=
    (le_max_left _ _).trans hlogT
  have hgapVert : 2 * (1 + 2 * kappa + 6 + 1) ≤ Real.log T :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlogT)
  have hgapRes : 1 + 3 / 20 + 2 * kappa + 1 ≤ Real.log T :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlogT)
  have harith := arithmetic_detector_tail_le_rpow_neg
    (T := T) (u := 2 * kappa) (c := 1) (d := 1)
      (U := ⌊Real.rpow T kappa⌋₊)
      hT hUscale hconstArith hgapArith
  have hvert := principal_vertical_tail_le_rpow_neg
    (T := T) (u := 2 * kappa) (c := 1) (d := 1)
      (U := ⌊Real.rpow T kappa⌋₊) (rho := rho)
      hT hUscale hheight (by simpa [Cvert] using hconstVert) hgapVert
  have hresidue := principal_residue_le_rpow_neg
    (T := T) (u := 2 * kappa) (c := 1) (d := 1)
      (U := ⌊Real.rpow T kappa⌋₊) (rho := rho)
      hT hzero hbetaLow hbetaHigh hcut hlogOne hUscale hconstRes hgapRes
  have hTinv : Real.rpow T (-1) ≤ 1 / 16 := by
    rw [show Real.rpow T (-1) = T⁻¹ by
      change T ^ (-1 : ℝ) = T⁻¹
      simp [Real.rpow_neg_one]]
    simpa [one_div] using
      ((inv_le_inv₀ hTpos (by norm_num : (0 : ℝ) < 16)).2 hT16)
  have harithSmall :
      (⌊Real.rpow T kappa⌋₊ + 1 : ℝ) *
          (Real.exp (-(1 / Real.rpow T (1 / 2)))) ^
            (detectorArithmeticCutoff (Real.rpow T (1 / 2)) T + 1) *
          (1 - Real.exp (-(1 / Real.rpow T (1 / 2))))⁻¹ ≤ 1 / 16 :=
    harith.trans hTinv
  have hvertSmall :
      (1 / (2 * Real.pi)) *
        (4 * (12 * 3200 * (⌊Real.rpow T kappa⌋₊ + 1) *
          (4 + |rho.im|) ^ 6 * (2 : ℝ) ^ 7 *
          (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
            Real.exp (-(detectorVerticalCutoff T) / 2)) ≤ 1 / 16 :=
    hvert.trans hTinv
  have hresidueSmall :
      ‖principalDetectorResidue rho ⌊Real.rpow T kappa⌋₊
          (Real.rpow T (1 / 2))‖ ≤ 1 / 16 :=
    hresidue.trans hTinv
  have herrorSmall :
      principalPaperScaleTruncationError
          ⌊Real.rpow T kappa⌋₊ rho (Real.rpow T (1 / 2)) T ≤
        3 / 16 := by
    dsimp [principalPaperScaleTruncationError,
      principalDetectorTruncationError]
    calc
      _ ≤ 1 / 16 + 1 / 16 + 1 / 16 :=
        add_le_add (add_le_add harithSmall hvertSmall) hresidueSmall
      _ = 3 / 16 := by norm_num
  have hVsmall : Real.rpow T (-inputLoss kappa eta) ≤ 1 / 16 := by
    rw [show Real.rpow T (-inputLoss kappa eta) =
        (Real.rpow T (inputLoss kappa eta))⁻¹ by
      change T ^ (-inputLoss kappa eta) =
        (T ^ (inputLoss kappa eta))⁻¹
      exact Real.rpow_neg hT0 (inputLoss kappa eta)]
    simpa [one_div] using
      ((inv_le_inv₀ (Real.rpow_pos_of_pos hTpos (inputLoss kappa eta))
        (by norm_num : (0 : ℝ) < 16)).2 hVgrowT)
  have hinvY : 1 / Real.rpow T (1 / 2) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hYgrowT
  have hrhs : 1 / 2 ≤ Real.exp (-(1 / Real.rpow T (1 / 2))) := by
    have hadd := Real.add_one_le_exp (-(1 / Real.rpow T (1 / 2)))
    linarith
  calc
    principalPaperScaleTruncationError
          ⌊Real.rpow T kappa⌋₊ rho (Real.rpow T (1 / 2)) T +
        Real.rpow T (-inputLoss kappa eta) +
        Real.rpow T (-inputLoss kappa eta) ≤
      3 / 16 + 1 / 16 + 1 / 16 :=
        add_le_add (add_le_add herrorSmall hVsmall) hVsmall
    _ ≤ 1 / 2 := by norm_num
    _ ≤ Real.exp (-(1 / Real.rpow T (1 / 2))) := hrhs

/-- The exact live principal high-strip alias now needs only the classical
zeta fourth moment and the shared structured `30/13` large-value theorem. -/
theorem principalClosedHighStripSource_of_principalFourthMoment_unconditionalBudget
    (hfourth : PrincipalZetaDiscreteFourthMoment)
    (hStructured :
      CGLDetectorStructuredLargeValue.DetectorStructuredThirtyThirteenLargeValue) :
    MAPLiveEndpointWeld.PrincipalClosedHighStripSource :=
  principalClosedHighStripSource_of_principalFourthMoment
    principalHighOrdinateDetectorBudget_unconditional hfourth hStructured

end
end MAPPrincipalHighOrdinateDetectorBudgetProof

#print axioms MAPPrincipalHighOrdinateDetectorBudgetProof.principal_vertical_tail_le_rpow_neg
#print axioms MAPPrincipalHighOrdinateDetectorBudgetProof.principal_residue_le_rpow_neg
#print axioms MAPPrincipalHighOrdinateDetectorBudgetProof.principalHighOrdinateDetectorBudget_unconditional
#print axioms MAPPrincipalHighOrdinateDetectorBudgetProof.principalClosedHighStripSource_of_principalFourthMoment_unconditionalBudget
