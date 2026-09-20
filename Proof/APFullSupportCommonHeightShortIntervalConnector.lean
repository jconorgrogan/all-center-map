import APCorrectedTailToRemainderTransfer
import APZeroHeightPadding
import APSelectedHeightZeroFieldEnergy28
import APConditionalShortIntervalConnector
import EndpointPerronZeroCancellation

/-!
# Direct full-support common-height AP connector

This route keeps the full closed zero divisor `zeroSupport primitive 0 T`
at the selected common height.  It combines the full h27 energy with a
source-facing common-height explicit-formula transfer, so no positive-`sigma`
truncation or low-strip subtraction occurs.
-/

namespace MAPAPFullSupportCommonHeightShortIntervalConnector

open MeasureTheory Set
open scoped ENNReal
open APFoundation MAPFixedScaleAPZeroRoute
open MAPAPCorrectedTailToRemainderTransfer MAPAPZeroHeightPadding
open MAPAPSelectedHeightZeroFieldEnergy28

noncomputable section

/-- The canonical field is definitionally the complete `sigma = 0` divisor
with analytic multiplicity.  This is the field inserted into the selected
height energy below. -/
theorem primitiveActualZeroField_eq_fullSupport
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (T t : ℝ) :
    primitiveActualZeroField chi T t =
      (by
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        exact APExplicitFormulaMajorantAdapter.finiteZeroField
          (DirichletZeros.zeroSupport chi.primitiveCharacter 0 T)
          (DirichletZeros.zeroMultiplicity chi.primitiveCharacter 0 T) t) := by
  rfl

/-- The h27 mass uses the same complete divisor and the same multiplicity as
the full zero field. -/
theorem primitiveWeightedZeroMass_eq_fullSupport
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (X T : ℝ) :
    primitiveWeightedZeroMass chi X T =
      (by
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        exact ∑ rho ∈ DirichletZeros.zeroSupport chi.primitiveCharacter 0 T,
          (DirichletZeros.zeroMultiplicity chi.primitiveCharacter 0 T rho : ℝ) *
            Real.rpow X (2 * (rho.re - 1))) := by
  rfl

/-- Audit identity for the route we deliberately bypassed: every zero below a
positive contour edge remains in the full endpoint primitive, with
multiplicity transported exactly between the nested rectangles. -/
theorem fullSupportEndpoint_eq_positiveEdge_add_lowStrip
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T t : ℝ} (hsigma : 0 ≤ sigma) :
    MAPEndpointRegularizedZeroPrimitive.endpointMultiplicityWeightedZeroTerm
        chi 0 T t =
      EndpointPerronZeroCancellation.positiveEdgeEndpointZeroTerm
          chi sigma T t +
        EndpointPerronZeroCancellation.lowStripEndpointZeroTerm
          chi sigma T t :=
  EndpointPerronZeroCancellation.endpointMultiplicityWeightedZeroTerm_eq_positiveEdge_add_lowStrip
    chi hsigma

/-- Equation (2.7) plus a full-support common-height transfer imply the exact
simultaneous short-interval AP theorem.  The low-real-part zeros are already
inside `apZeroFieldEnergy`; no sigma-truncated field is introduced. -/
theorem simultaneousShortIntervalAP_of_weightedZeroMass_of_fullSupportTransfer
    (h27 : APWeightedZeroMassLogSaving)
    (htransfer : CommonHeightAPMaximalExplicitFormulaRemainderTransfer) :
    SimultaneousShortIntervalAP := by
  intro K A epsilon hK hA hepsilon hepsilonCap
  let reserve : ℝ := min epsilon (1 / 10)
  have hreservePos : 0 < reserve := by
    dsimp [reserve]
    exact lt_min hepsilon (by norm_num)
  have hreserveCap : reserve ≤ 1 / 10 := by
    dsimp [reserve]
    exact min_le_right _ _
  have hhalfPos : 0 < reserve / 2 := by positivity
  have hhalfCap : reserve / 2 ≤ 1 / 10 := by linarith
  have hA4 : 0 < A + 4 := by linarith
  rcases h27 K (A + 4) (reserve / 2)
      hK hA4 hhalfPos hhalfCap with
    ⟨Cz, Xz, hCz, hXz, hZ⟩
  rcases certifiedSelectedHeightAPZeroFieldEnergy28 K hK with
    ⟨Ce, Xe, hCe, hXe, henergy⟩
  rcases htransfer K A epsilon hK hA hepsilon hepsilonCap with
    ⟨Cr, Xr, hCr, hXr, htransferX⟩
  let Xp : ℝ := Real.exp (4 * Real.log 2 / reserve)
  let C : ℝ := Cr * Ce * Cz + Cr
  let X0 : ℝ := max (Real.exp 1) (max Xp (max Xz (max Xe Xr)))
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hX0 : 2 ≤ X0 := by
    have hexp : 2 < Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    exact hexp.le.trans (le_max_left _ _)
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X hXX0
  have hXexp : Real.exp 1 ≤ X := (le_max_left _ _).trans hXX0
  have hXXp : Xp ≤ X := by
    exact (le_max_left Xp (max Xz (max Xe Xr))).trans
      ((le_max_right (Real.exp 1) (max Xp (max Xz (max Xe Xr)))).trans hXX0)
  have hXXz : Xz ≤ X := by
    have : Xz ≤ max Xp (max Xz (max Xe Xr)) :=
      (le_max_left Xz (max Xe Xr)).trans
        (le_max_right Xp (max Xz (max Xe Xr)))
    exact this.trans
      ((le_max_right (Real.exp 1) (max Xp (max Xz (max Xe Xr)))).trans hXX0)
  have hXXe : Xe ≤ X := by
    have : Xe ≤ max Xp (max Xz (max Xe Xr)) :=
      (le_max_left Xe Xr).trans
        ((le_max_right Xz (max Xe Xr)).trans
          (le_max_right Xp (max Xz (max Xe Xr))))
    exact this.trans
      ((le_max_right (Real.exp 1) (max Xp (max Xz (max Xe Xr)))).trans hXX0)
  have hXXr : Xr ≤ X := by
    have : Xr ≤ max Xp (max Xz (max Xe Xr)) :=
      (le_max_right Xe Xr).trans
        ((le_max_right Xz (max Xe Xr)).trans
          (le_max_right Xp (max Xz (max Xe Xr))))
    exact this.trans
      ((le_max_right (Real.exp 1) (max Xp (max Xz (max Xe Xr)))).trans hXX0)
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hXexp
  have hlogOne : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hXexp
  have hlog : 0 < Real.log X := zero_lt_one.trans_le hlogOne
  let Q : ℕ := ⌊Real.rpow (Real.log X) K⌋₊
  let H0 : ℝ := apZeroHeight reserve X
  let Z : ℝ := apWeightedZeroMass Q X (apZeroHeight (reserve / 2) X)
  have hZnonneg : 0 ≤ Z := by
    exact MAPAPConditionalShortIntervalConnector.apWeightedZeroMass_nonneg
      Q hXpos.le (apZeroHeight (reserve / 2) X)
  have hZbound : Z ≤ Cz * Real.rpow (Real.log X) (-(A + 4)) := by
    simpa [Q, Z] using hZ X hXXz
  have hpad :
      apWeightedZeroMass Q X (H0 + 1) ≤ Z := by
    dsimp [H0, Z, Xp] at *
    exact apWeightedZeroMass_add_one_le_halfReserve
      Q hreservePos hreserveCap hXXp
  have hrawAtX := htransferX X hXXr
  dsimp only at hrawAtX
  rcases hrawAtX with ⟨T, hT, hraw⟩
  have hE := henergy Q reserve X H0 T
    (by rfl) hreservePos hreserveCap (by rfl) hT hXXe
  have hmassTop : 0 ≤ apWeightedZeroMass Q X (H0 + 1) :=
    MAPAPConditionalShortIntervalConnector.apWeightedZeroMass_nonneg
      Q hXpos.le (H0 + 1)
  have hEpad :
      apZeroFieldEnergy Q X T ≤
        ENNReal.ofReal (Ce * X * (Real.log X) ^ 2 * Z) := by
    refine hE.trans ?_
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hpad
      (show 0 ≤ Ce * X * (Real.log X) ^ 2 by positivity)
  change (∫⁻ x in Set.Icc (X / 2) (4 * X),
      simultaneousAPMax K epsilon X x) ≤ _
  calc
    (∫⁻ x in Set.Icc (X / 2) (4 * X),
        simultaneousAPMax K epsilon X x) ≤
        ENNReal.ofReal (Cr * (Real.log X) ^ 2) *
            apZeroFieldEnergy Q X T +
          ENNReal.ofReal
            (Cr * X * Real.rpow (Real.log X) (-A)) := by
      simpa [Q, H0] using hraw
    _ ≤ ENNReal.ofReal (Cr * (Real.log X) ^ 2) *
            ENNReal.ofReal (Ce * X * (Real.log X) ^ 2 * Z) +
          ENNReal.ofReal
            (Cr * X * Real.rpow (Real.log X) (-A)) := by
      gcongr
    _ = ENNReal.ofReal
          ((Cr * (Real.log X) ^ 2) *
            (Ce * X * (Real.log X) ^ 2 * Z)) +
          ENNReal.ofReal
            (Cr * X * Real.rpow (Real.log X) (-A)) := by
      congr 1
      exact (ENNReal.ofReal_mul
        (mul_nonneg hCr.le (sq_nonneg (Real.log X)))).symm
    _ ≤ ENNReal.ofReal
          (Cr * Ce * Cz * X * Real.rpow (Real.log X) (-A)) +
          ENNReal.ofReal
            (Cr * X * Real.rpow (Real.log X) (-A)) := by
      apply add_le_add_left
      apply ENNReal.ofReal_le_ofReal
      have hmul := mul_le_mul_of_nonneg_left hZbound
        (show 0 ≤ Cr * Ce * X * (Real.log X) ^ 4 by positivity)
      calc
        (Cr * (Real.log X) ^ 2) *
              (Ce * X * (Real.log X) ^ 2 * Z) =
            (Cr * Ce * X * (Real.log X) ^ 4) * Z := by ring
        _ ≤ (Cr * Ce * X * (Real.log X) ^ 4) *
              (Cz * Real.rpow (Real.log X) (-(A + 4))) := hmul
        _ = Cr * Ce * Cz * X * Real.rpow (Real.log X) (-A) := by
          calc
            (Cr * Ce * X * (Real.log X) ^ 4) *
                (Cz * Real.rpow (Real.log X) (-(A + 4))) =
              Cr * Ce * Cz * X *
                ((Real.log X) ^ 4 *
                  Real.rpow (Real.log X) (-(A + 4))) := by ring
            _ = Cr * Ce * Cz * X * Real.rpow (Real.log X) (-A) := by
              rw [MAPAPConditionalShortIntervalConnector.log_pow_four_mul_rpow_neg_add_four hlog]
    _ = ENNReal.ofReal
          ((Cr * Ce * Cz + Cr) * X *
            Real.rpow (Real.log X) (-A)) := by
      rw [← ENNReal.ofReal_add]
      · congr 1
        ring
      · have hp : 0 ≤ Real.rpow (Real.log X) (-A) :=
          Real.rpow_nonneg hlog.le _
        positivity
      · have hp : 0 ≤ Real.rpow (Real.log X) (-A) :=
          Real.rpow_nonneg hlog.le _
        positivity
    _ = ENNReal.ofReal
          (C * X * Real.rpow (Real.log X) (-A)) := by rfl

/-- Source-facing wrapper: the corrected common-height endpoint remainder is
kept with the full closed zero divisor and fed directly to the full-support
connector. -/
theorem simultaneousShortIntervalAP_of_weightedZeroMass_of_correctedTail
    (h27 : APWeightedZeroMassLogSaving)
    (htail : MAPAPCorrectedPaperEdgeTail.CorrectedAPExplicitFormulaTailFamilySquare) :
    SimultaneousShortIntervalAP :=
  simultaneousShortIntervalAP_of_weightedZeroMass_of_fullSupportTransfer h27
    (commonHeightRemainderTransfer_of_correctedTailFamilySquare htail)

end
end MAPAPFullSupportCommonHeightShortIntervalConnector

#print axioms MAPAPFullSupportCommonHeightShortIntervalConnector.simultaneousShortIntervalAP_of_weightedZeroMass_of_fullSupportTransfer
#print axioms MAPAPFullSupportCommonHeightShortIntervalConnector.simultaneousShortIntervalAP_of_weightedZeroMass_of_correctedTail
#print axioms MAPAPFullSupportCommonHeightShortIntervalConnector.fullSupportEndpoint_eq_positiveEdge_add_lowStrip
