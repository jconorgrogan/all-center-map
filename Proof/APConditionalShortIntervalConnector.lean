import CertifiedAPZeroFieldEnergy28

/-!
# Conditional explicit-formula to AP connector

Equation (2.8) is now certified independently.  This file keeps the remaining
number-theoretic inputs visibly separate:

* `APWeightedZeroMassLogSaving` is manuscript (2.7), including its
  exceptional-zero saving;
* `APMaximalExplicitFormulaRemainderTransfer` is the quantitative truncated
  explicit-formula/remainder bridge.  Its right side contains the *raw*
  equation-(2.8) zero-field energy, so it is strictly below the AP conclusion.

The theorem at the end proves the exact `SimultaneousShortIntervalAP` target
from those two inputs and the premise-free certified equation (2.8).  Four
logarithms are reserved in (2.7): two for (2.8) and two for the deliberately
generous maximal/remainder transfer coefficient.
-/

namespace MAPAPConditionalShortIntervalConnector

open MeasureTheory Set
open scoped ENNReal
open APFoundation MAPFixedScaleAPZeroRoute

noncomputable section

/-- The smallest remaining AP-side analytic contract after certified (2.8).

The contract is source-facing rather than conclusion-shaped.  It says that
the exact simultaneous progression error is bounded by a polylogarithmic
multiple of the literal finite zero-field energy, plus an arbitrarily
log-saving explicit-formula remainder.  The primitive/imprimitive correction,
the `Re rho = 0` endpoint, and the Perron/contour truncation all belong in the
second term.  No zero-density saving is built into this proposition. -/
def APMaximalExplicitFormulaRemainderTransfer : Prop :=
  ∀ K A epsilon : ℝ,
    0 < K → 0 < A → 0 < epsilon → epsilon ≤ 13 / 30 →
    ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        let reserve := min epsilon (1 / 10)
        let Q := ⌊Real.rpow (Real.log X) K⌋₊
        (∫⁻ x in Set.Icc (X / 2) (4 * X), simultaneousAPMax K epsilon X x) ≤
          ENNReal.ofReal (C * (Real.log X) ^ 2) *
              apZeroFieldEnergy Q X (apZeroHeight reserve X) +
            ENNReal.ofReal (C * X * Real.rpow (Real.log X) (-A))

lemma primitiveWeightedZeroMass_nonneg {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {X : ℝ} (hX : 0 ≤ X) (T : ℝ) :
    0 ≤ primitiveWeightedZeroMass chi X T := by
  unfold primitiveWeightedZeroMass
  apply Finset.sum_nonneg
  intro rho hrho
  exact mul_nonneg (Nat.cast_nonneg _)
    (Real.rpow_nonneg hX _)

lemma weightedZeroMassAtLevel_nonneg (q : ℕ) {X : ℝ} (hX : 0 ≤ X) (T : ℝ) :
    0 ≤ weightedZeroMassAtLevel q X T := by
  unfold weightedZeroMassAtLevel
  split_ifs with hq
  · norm_num
  · letI : NeZero q := ⟨hq⟩
    apply Finset.sum_nonneg
    intro chi hchi
    exact primitiveWeightedZeroMass_nonneg chi hX T

lemma apWeightedZeroMass_nonneg (Q : ℕ) {X : ℝ} (hX : 0 ≤ X) (T : ℝ) :
    0 ≤ apWeightedZeroMass Q X T := by
  unfold apWeightedZeroMass
  apply Finset.sum_nonneg
  intro q hq
  exact weightedZeroMassAtLevel_nonneg q hX T

/-- Exact logarithm cancellation used by the connector. -/
lemma log_pow_four_mul_rpow_neg_add_four
    {X A : ℝ} (hlog : 0 < Real.log X) :
    (Real.log X) ^ 4 * Real.rpow (Real.log X) (-(A + 4)) =
      Real.rpow (Real.log X) (-A) := by
  have hpow : (Real.log X) ^ (4 : ℕ) =
      Real.rpow (Real.log X) (4 : ℝ) := by
    exact (Real.rpow_natCast (Real.log X) 4).symm
  calc
    (Real.log X) ^ 4 * Real.rpow (Real.log X) (-(A + 4)) =
        Real.rpow (Real.log X) 4 *
          Real.rpow (Real.log X) (-(A + 4)) := by rw [hpow]
    _ = Real.rpow (Real.log X) (4 + -(A + 4)) :=
      (Real.rpow_add hlog 4 (-(A + 4))).symm
    _ = Real.rpow (Real.log X) (-A) := by
      congr 1
      ring

/-- The exact conditional connector.  The only assumptions are the weighted
zero-mass estimate (2.7) and the quantitative explicit-formula remainder
transfer.  Equation (2.8) is supplied by its certified inhabitant. -/
theorem simultaneousShortIntervalAP_of_weightedZeroMass_of_remainderTransfer
    (h27 : APWeightedZeroMassLogSaving)
    (htransfer : APMaximalExplicitFormulaRemainderTransfer) :
    SimultaneousShortIntervalAP := by
  intro K A epsilon hK hA hepsilon hepsilonCap
  let reserve : ℝ := min epsilon (1 / 10)
  have hreservePos : 0 < reserve := by
    dsimp [reserve]
    exact lt_min hepsilon (by norm_num)
  have hreserveCap : reserve ≤ 1 / 10 := by
    dsimp [reserve]
    exact min_le_right _ _
  have hA4 : 0 < A + 4 := by linarith
  rcases h27 K (A + 4) reserve hK hA4 hreservePos hreserveCap with
    ⟨Cz, Xz, hCz, hXz, hZ⟩
  rcases MAPCertifiedAPZeroFieldEnergy28.certifiedAPZeroFieldEnergy28 K hK with
    ⟨Ce, Xe, hCe, hXe, henergy⟩
  rcases htransfer K A epsilon hK hA hepsilon hepsilonCap with
    ⟨Cr, Xr, hCr, hXr, htransferX⟩
  let C : ℝ := Cr * Ce * Cz + Cr
  let X₀ : ℝ := max (Real.exp 1) (max Xz (max Xe Xr))
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hX₀ : 2 ≤ X₀ := by
    have hexp : 2 < Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    exact hexp.le.trans (le_max_left _ _)
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X hX
  have hXexp : Real.exp 1 ≤ X :=
    (le_max_left _ _).trans hX
  have hXz' : Xz ≤ X := by
    exact (le_max_left Xz (max Xe Xr)).trans
      ((le_max_right (Real.exp 1) (max Xz (max Xe Xr))).trans hX)
  have hXe' : Xe ≤ X := by
    have : Xe ≤ max Xz (max Xe Xr) :=
      (le_max_left Xe Xr).trans (le_max_right Xz (max Xe Xr))
    exact this.trans
      ((le_max_right (Real.exp 1) (max Xz (max Xe Xr))).trans hX)
  have hXr' : Xr ≤ X := by
    have : Xr ≤ max Xz (max Xe Xr) :=
      (le_max_right Xe Xr).trans (le_max_right Xz (max Xe Xr))
    exact this.trans
      ((le_max_right (Real.exp 1) (max Xz (max Xe Xr))).trans hX)
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hXexp
  have hlogOne : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hXexp
  have hlog : 0 < Real.log X := zero_lt_one.trans_le hlogOne
  let Q : ℕ := ⌊Real.rpow (Real.log X) K⌋₊
  let Z : ℝ := apWeightedZeroMass Q X (apZeroHeight reserve X)
  have hZnonneg : 0 ≤ Z := by
    exact apWeightedZeroMass_nonneg Q hXpos.le (apZeroHeight reserve X)
  have hZbound : Z ≤ Cz * Real.rpow (Real.log X) (-(A + 4)) := by
    simpa [Q, Z] using hZ X hXz'
  have hE :
      apZeroFieldEnergy Q X (apZeroHeight reserve X) ≤
        ENNReal.ofReal (Ce * X * (Real.log X) ^ 2 * Z) := by
    exact henergy Q reserve X (by rfl) hreservePos hreserveCap hXe'
  have hraw := htransferX X hXr'
  dsimp only at hraw
  change (∫⁻ x in Set.Icc (X / 2) (4 * X),
      simultaneousAPMax K epsilon X x) ≤ _
  calc
    (∫⁻ x in Set.Icc (X / 2) (4 * X),
        simultaneousAPMax K epsilon X x) ≤
        ENNReal.ofReal (Cr * (Real.log X) ^ 2) *
            apZeroFieldEnergy Q X (apZeroHeight reserve X) +
          ENNReal.ofReal
            (Cr * X * Real.rpow (Real.log X) (-A)) := by
      simpa [reserve, Q] using hraw
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
              rw [log_pow_four_mul_rpow_neg_add_four hlog]
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

end
end MAPAPConditionalShortIntervalConnector

#print axioms MAPAPConditionalShortIntervalConnector.log_pow_four_mul_rpow_neg_add_four
#print axioms MAPAPConditionalShortIntervalConnector.simultaneousShortIntervalAP_of_weightedZeroMass_of_remainderTransfer
