import FejerArcBridge
import FejerMAPInterfaceWeld
import WindowArcBoundaryWeld
import SupportBoundaryWeld
import MajorArcPrimePairWeld
import MAPCertifiedEndpoint
import MAPQ4Bridge

/-!
# Local MAP to translated variance: exact last-mile weld

This module contains only measure-theoretic and finite algebra.  The upstream
local minor-arc estimate and the deterministic major-arc/support approximation
enter as ordinary hypotheses of the final transfer theorems.  Neither
hypothesis restates a variance or Q4 conclusion.
-/

namespace MAPVarianceTransferWeld

open AddCircle MeasureTheory
open scoped BigOperators ComplexConjugate ArithmeticFunction

noncomputable section

open PrimePairEndpoints MAPHarmonicEndpoint

/-- The non-minor part of the public Hardy--Littlewood error.  At nonzero
frequency it is exactly the major coefficient plus the support-boundary term
minus the public `X * singularSeriesTotal h` model. -/
def deterministicRemainder
    (X : ℝ) (B D : ℕ) (h : ℤ) : ℂ :=
  majorCoefficient X B D h +
    (SupportBoundaryWeld.supportBoundaryCorrection X h : ℂ) -
      ((X * singularSeriesTotal h : ℝ) : ℂ)

/-- The deterministic remainder energy, deleting the deliberately totalized
zero shift just as `primePairSignal` does. -/
def deterministicRemainderEnergy
    (X H h₀ : ℝ) (B D : ℕ) : ℝ :=
  ∑ h ∈ translatedWindow H h₀,
    if h = 0 then 0 else ‖deterministicRemainder X B D h‖ ^ 2

/-- Exact nonzero-frequency error decomposition. -/
theorem primePairError_eq_minor_add_deterministicRemainder
    (X : ℝ) (B D : ℕ) {h : ℤ} (hh : h ≠ 0) :
    ((primePairError X h : ℝ) : ℂ) =
      minorCoefficient X B D h + deterministicRemainder X B D h := by
  rw [primePairError, primePairSignal, if_neg hh]
  push_cast
  rw [SupportBoundaryWeld.primePairCorrelation_eq_major_add_minor_add_boundary]
  unfold deterministicRemainder
  push_cast
  ring

/-- Square norm of a two-term complex error. -/
theorem norm_add_sq_le_two_mul
    (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have hab := norm_add_le a b
  have ha : 0 ≤ ‖a‖ := norm_nonneg _
  have hb : 0 ≤ ‖b‖ := norm_nonneg _
  have hab0 : 0 ≤ ‖a + b‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- Exact finite passage from the harmonic minor coefficients and the
deterministic major/support remainder to the public translated variance. -/
theorem primePairVariance_le_minor_add_remainder
    (X H h₀ : ℝ) (B D : ℕ) :
    primePairVariance X H h₀ ≤
      2 * (∑ h ∈ translatedWindow H h₀,
        ‖minorCoefficient X B D h‖ ^ 2) +
      2 * deterministicRemainderEnergy X H h₀ B D := by
  classical
  unfold primePairVariance deterministicRemainderEnergy
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h hhwin
  by_cases hh : h = 0
  · subst h
    simp [primePairError, primePairSignal, singularSeriesTotal]
  · rw [if_neg hh]
    have hid := primePairError_eq_minor_add_deterministicRemainder X B D hh
    have hnorm := congrArg norm hid
    have hsquare := norm_add_sq_le_two_mul
      (minorCoefficient X B D h) (deterministicRemainder X B D h)
    rw [Complex.norm_real, Real.norm_eq_abs] at hnorm
    rw [hnorm]
    exact hsquare

/-- The minor coefficient is literally the Fourier coefficient of the
positive minor density used by the Fejer theorem. -/
theorem circleCoefficient_minorWeight
    (X : ℝ) (B D : ℕ) (h : ℤ) :
    circleCoefficient (minorWeight X B D) h =
      minorCoefficient X B D h := rfl

/-- The positive minor density is pointwise bounded by the full square
density, so its total mass is controlled by the elementary Parseval bound. -/
theorem integral_minorWeight_le_global
    {X : ℝ} (hX : 1 ≤ X) (B D : ℕ) :
    (∫ a : UnitAddCircle, minorWeight X B D a
      ∂AddCircle.haarAddCircle) ≤
      2 * X * (Real.log (2 * X)) ^ 2 := by
  have hmono :
      (∫ a : UnitAddCircle, minorWeight X B D a
        ∂AddCircle.haarAddCircle) ≤
      ∫ a : UnitAddCircle, ‖primeExponentialSum X a‖ ^ 2
        ∂AddCircle.haarAddCircle := by
    apply integral_mono
    · exact minorWeight_integrable X B D
    · exact normSq_primeExponentialSum_integrable X
    · intro a
      unfold minorWeight
      by_cases ha : a ∈ minorArcs X B D
      · simp only [Set.indicator_of_mem ha]
        exact le_rfl
      · simp only [Set.indicator_of_notMem ha]
        positivity
  exact hmono.trans
    (FejerMAPInterfaceWeld.integral_normSq_primeExponentialSum_le_log_sq hX)

/-- For `X ≥ 2`, replacing `log(2X)` by `2 log X` is harmless and explicit. -/
theorem log_two_mul_le_two_log
    {X : ℝ} (hX : 2 ≤ X) :
    Real.log (2 * X) ≤ 2 * Real.log X := by
  have hXpos : 0 < X := by linarith
  have h2pos : (0 : ℝ) < 2 := by norm_num
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXpos.ne']
  have hlog := Real.log_le_log h2pos hX
  linarith

/-- Public total minor mass in the convenient `8 X log^2 X` form. -/
theorem integral_minorWeight_le_eight_log_sq
    {X : ℝ} (hX : 2 ≤ X) (B D : ℕ) :
    (∫ a : UnitAddCircle, minorWeight X B D a
      ∂AddCircle.haarAddCircle) ≤
      8 * X * (Real.log X) ^ 2 := by
  have hbase := integral_minorWeight_le_global (one_le_two.trans hX) B D
  have hlog := log_two_mul_le_two_log hX
  have hlog0 : 0 ≤ Real.log (2 * X) := by
    apply Real.log_nonneg
    nlinarith
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (one_le_two.trans hX)
  have hsq : (Real.log (2 * X)) ^ 2 ≤ (2 * Real.log X) ^ 2 := by
    nlinarith
  calc
    (∫ a : UnitAddCircle, minorWeight X B D a
      ∂AddCircle.haarAddCircle) ≤
        2 * X * (Real.log (2 * X)) ^ 2 := hbase
    _ ≤ 2 * X * (2 * Real.log X) ^ 2 := by gcongr
    _ = 8 * X * (Real.log X) ^ 2 := by ring

/-- Exact Fejer transfer with the constant left existentially quantified by
the already certified spatial theorem.  This preserves the real window
center, both integer endpoints, and normalized Haar measure. -/
theorem exists_minorCoefficientWindowConstant :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (X H h₀ totalBound localBound : ℝ) (B D : ℕ),
        1 ≤ H → 0 ≤ totalBound → 0 ≤ localBound →
        (∫ a : UnitAddCircle, minorWeight X B D a
          ∂AddCircle.haarAddCircle) ≤ totalBound →
        (∀ center : UnitAddCircle,
          (∫ a in centeredArc H center, minorWeight X B D a
            ∂AddCircle.haarAddCircle) ≤ localBound) →
        (∑ h ∈ translatedWindow H h₀,
          ‖minorCoefficient X B D h‖ ^ 2) ≤
            C₀ * H * totalBound * localBound := by
  rcases exists_positiveMeasureFejerLocalFourierConstant with
    ⟨C₀, hC₀, hfejer⟩
  refine ⟨C₀, hC₀, ?_⟩
  intro X H h₀ totalBound localBound B D hH htotal0 hlocal0
    htotal hlocal
  simpa only [circleCoefficient_minorWeight] using
    hfejer (minorWeight X B D) H h₀ totalBound localBound
      (minorWeight_integrable X B D) (minorWeight_nonneg X B D)
      hH htotal0 hlocal0 htotal hlocal

/-- Fixed-scale last-mile variance transfer.  The local hypothesis is exactly
an arc-mass estimate; the second analytic hypothesis concerns only the
deterministic major/support remainder. -/
theorem primePairVariance_le_of_localMAP_and_remainder
    {C₀ X H h₀ totalBound localBound remainderBound : ℝ}
    {B D : ℕ}
    (hfejer :
      ∀ (X H h₀ totalBound localBound : ℝ) (B D : ℕ),
        1 ≤ H → 0 ≤ totalBound → 0 ≤ localBound →
        (∫ a : UnitAddCircle, minorWeight X B D a
          ∂AddCircle.haarAddCircle) ≤ totalBound →
        (∀ center : UnitAddCircle,
          (∫ a in centeredArc H center, minorWeight X B D a
            ∂AddCircle.haarAddCircle) ≤ localBound) →
        (∑ h ∈ translatedWindow H h₀,
          ‖minorCoefficient X B D h‖ ^ 2) ≤
            C₀ * H * totalBound * localBound)
    (hH : 1 ≤ H) (htotal0 : 0 ≤ totalBound)
    (hlocal0 : 0 ≤ localBound)
    (htotal : (∫ a : UnitAddCircle, minorWeight X B D a
      ∂AddCircle.haarAddCircle) ≤ totalBound)
    (hlocal : ∀ center : UnitAddCircle,
      (∫ a in centeredArc H center, minorWeight X B D a
        ∂AddCircle.haarAddCircle) ≤ localBound)
    (hremainder : deterministicRemainderEnergy X H h₀ B D ≤ remainderBound) :
    primePairVariance X H h₀ ≤
      2 * C₀ * H * totalBound * localBound + 2 * remainderBound := by
  have hminor := hfejer X H h₀ totalBound localBound B D hH
    htotal0 hlocal0 htotal hlocal
  calc
    primePairVariance X H h₀ ≤
        2 * (∑ h ∈ translatedWindow H h₀,
          ‖minorCoefficient X B D h‖ ^ 2) +
        2 * deterministicRemainderEnergy X H h₀ B D :=
      primePairVariance_le_minor_add_remainder X H h₀ B D
    _ ≤ 2 * (C₀ * H * totalBound * localBound) +
        2 * remainderBound := by gcongr
    _ = 2 * C₀ * H * totalBound * localBound +
        2 * remainderBound := by ring

/-- The public Q4 objects are definitionally the generic finite Q4 objects. -/
theorem public_q4_deviation_le_variance
    (X H h₀ : ℝ) :
    |q4Quantity X H h₀ - X ^ 2 * singularSquareMain H h₀| ≤
      primePairVariance X H h₀ +
        2 * |X| * Real.sqrt
          (singularSquareMain H h₀ * primePairVariance X H h₀) := by
  simpa [q4Quantity, singularSquareMain, primePairVariance,
    primePairError, MAPQ4Bridge.q4Moment, MAPQ4Bridge.modelSecondMoment,
    MAPQ4Bridge.variance, MAPQ4Bridge.modelMain, sq_abs] using
      MAPQ4Bridge.q4_deviation_le
        (translatedWindow H h₀) (primePairSignal X)
        singularSeriesTotal X

/-- Fixed-scale public Q4 endpoint from a variance bound and a singular-series
second-moment bound. -/
theorem public_q4_deviation_le_of_bounds
    {X H h₀ varianceBound modelBound : ℝ}
    (hX : 0 ≤ X) (hmodel0 : 0 ≤ modelBound)
    (hvariance : primePairVariance X H h₀ ≤ varianceBound)
    (hmodel : singularSquareMain H h₀ ≤ modelBound) :
    |q4Quantity X H h₀ - X ^ 2 * singularSquareMain H h₀| ≤
      varianceBound + 2 * X * Real.sqrt (modelBound * varianceBound) := by
  have hbase := public_q4_deviation_le_variance X H h₀
  have hvarnonneg : 0 ≤ primePairVariance X H h₀ := by
    unfold primePairVariance
    positivity
  have hmodelnonneg : 0 ≤ singularSquareMain H h₀ := by
    unfold singularSquareMain
    positivity
  have hprod :
      singularSquareMain H h₀ * primePairVariance X H h₀ ≤
        modelBound * varianceBound :=
    mul_le_mul hmodel hvariance hvarnonneg hmodel0
  calc
    |q4Quantity X H h₀ - X ^ 2 * singularSquareMain H h₀| ≤
        primePairVariance X H h₀ +
          2 * |X| * Real.sqrt
            (singularSquareMain H h₀ * primePairVariance X H h₀) := hbase
    _ ≤ varianceBound + 2 * X * Real.sqrt (modelBound * varianceBound) := by
      rw [abs_of_nonneg hX]
      gcongr

/-- The exact public exceptional set follows immediately at fixed scale. -/
theorem exceptionalShifts_card_le_of_variance_bound
    {A X H h₀ varianceBound : ℝ}
    (hX : 1 ≤ X)
    (hvariance : primePairVariance X H h₀ ≤ varianceBound) :
    ((exceptionalShifts A X H h₀).card : ℝ) *
        (X * Real.rpow (Real.log X) (-A)) ^ 2 ≤ varianceBound := by
  exact (exceptionalShifts_card_mul_threshold_sq_le_variance
    A X H h₀ hX).trans hvariance

/-- The logarithmic rate conversion used by the family-level transfer. -/
theorem log_sq_mul_stronger_rpow_le
    {L A : ℝ} (hL : 1 ≤ L) :
    L ^ 2 * Real.rpow L (-(A + 3)) ≤ Real.rpow L (-A) := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have heq :
      L ^ 2 * Real.rpow L (-(A + 3)) =
        Real.rpow L (2 + (-(A + 3))) := by
    rw [← Real.rpow_two]
    exact (Real.rpow_add hLpos 2 (-(A + 3))).symm
  rw [heq]
  apply Real.rpow_le_rpow_of_exponent_le hL
  linarith

/-- Auxiliary transfer under a uniform-in-cutoffs remainder hypothesis. This
surface is intentionally not the manuscript-facing endpoint: arbitrary saving
need not hold for small cutoffs. Use the selectable-cutoff theorem in
`MAPVarianceTransferCutoffWeld` for the paper's actual quantifier order. -/
theorem varianceFamily_of_allCenterLocalMAP_and_uniform_remainder
    (hMAP : AllCenterLocalMAP)
    (hRemainder :
      ∀ A ε : ℝ, 0 < A → 0 < ε →
        ∀ B D : ℕ, ∃ C X₀ : ℝ,
          0 < C ∧ 2 ≤ X₀ ∧
          ∀ X H h₀ : ℝ, X₀ ≤ X →
            LegalParameters ε X H h₀ →
            deterministicRemainderEnergy X H h₀ B D ≤
              C * H * X ^ 2 * Real.rpow (Real.log X) (-A)) :
    VarianceFamily := by
  rcases exists_minorCoefficientWindowConstant with ⟨C₀, hC₀, hfejer⟩
  intro A ε hA hε
  have hAmap : 0 < A + 3 := by linarith
  obtain ⟨B, D, Cmap, Xmap, hCmap, hXmap, hlocal⟩ :=
    FejerMAPInterfaceWeld.allCenterLocalMAP_minorWeight hMAP
      (A + 3) ε hAmap hε
  obtain ⟨Crem, Xrem, hCrem, hXrem, hrem⟩ :=
    hRemainder A ε hA hε B D
  let C : ℝ := 16 * C₀ * Cmap + 2 * Crem
  let X₀ : ℝ := max 3 (max Xmap Xrem)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hX₀ : 2 ≤ X₀ := by
    dsimp [X₀]
    exact le_trans (by norm_num) (le_max_left 3 (max Xmap Xrem))
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X H h₀ hXX₀ hlegal
  have hX3 : 3 ≤ X :=
    (le_max_left 3 (max Xmap Xrem)).trans hXX₀
  have hXmap' : Xmap ≤ X :=
    (le_trans (le_max_left Xmap Xrem)
      (le_max_right 3 (max Xmap Xrem))).trans hXX₀
  have hXrem' : Xrem ≤ X :=
    (le_trans (le_max_right Xmap Xrem)
      (le_max_right 3 (max Xmap Xrem))).trans hXX₀
  have hX2 : 2 ≤ X := by linarith
  have hX1 : 1 ≤ X := one_le_two.trans hX2
  have hXpos : 0 < X := zero_lt_one.trans_le hX1
  have hLpos : 0 < Real.log X := Real.log_pos (lt_of_lt_of_le (by norm_num) hX2)
  have hL3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
      Real.exp_one_lt_three
  have hlog3X : Real.log 3 ≤ Real.log X :=
    Real.log_le_log (by norm_num) hX3
  have hL : 1 ≤ Real.log X := hL3.le.trans hlog3X
  have hexp0 : 0 ≤ 2 / 15 + ε := by linarith
  have hH1 : 1 ≤ H :=
    (Real.one_le_rpow hX1 hexp0).trans hlegal.1
  let totalBound : ℝ := 8 * X * (Real.log X) ^ 2
  let localBound : ℝ :=
    Cmap * X * Real.rpow (Real.log X) (-(A + 3))
  let remainderBound : ℝ :=
    Crem * H * X ^ 2 * Real.rpow (Real.log X) (-A)
  have htotal0 : 0 ≤ totalBound := by
    dsimp [totalBound]
    positivity
  have hlocal0 : 0 ≤ localBound := by
    dsimp [localBound]
    positivity
  have htotal :
      (∫ a : UnitAddCircle, minorWeight X B D a
        ∂AddCircle.haarAddCircle) ≤ totalBound := by
    simpa [totalBound] using integral_minorWeight_le_eight_log_sq hX2 B D
  have hlocal' : ∀ center : UnitAddCircle,
      (∫ a in centeredArc H center, minorWeight X B D a
        ∂AddCircle.haarAddCircle) ≤ localBound := by
    intro center
    simpa [localBound] using hlocal X H hXmap' hlegal.1 center
  have hrem' :
      deterministicRemainderEnergy X H h₀ B D ≤ remainderBound := by
    simpa [remainderBound] using hrem X H h₀ hXrem' hlegal
  have hfixed := primePairVariance_le_of_localMAP_and_remainder
    hfejer hH1 htotal0 hlocal0 htotal hlocal' hrem'
  have hrate := log_sq_mul_stronger_rpow_le (L := Real.log X) (A := A) hL
  have hH0 : 0 ≤ H := zero_le_one.trans hH1
  have hpowA0 : 0 ≤ Real.rpow (Real.log X) (-A) := Real.rpow_nonneg hLpos.le _
  calc
    primePairVariance X H h₀ ≤
        2 * C₀ * H * totalBound * localBound + 2 * remainderBound := hfixed
    _ = 16 * C₀ * Cmap * H * X ^ 2 *
          ((Real.log X) ^ 2 * Real.rpow (Real.log X) (-(A + 3))) +
        2 * Crem * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
      dsimp [totalBound, localBound, remainderBound]
      ring
    _ ≤ 16 * C₀ * Cmap * H * X ^ 2 *
          Real.rpow (Real.log X) (-A) +
        2 * Crem * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
      gcongr
    _ = C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
      dsimp [C]
      ring

/-- Exact logarithmic identity used under the Q4 square root. -/
theorem natPow_mul_rpow_neg_sum
    {L A : ℝ} (hL : 0 < L) (k : ℕ) :
    L ^ k * Real.rpow L (-(2 * A + (k : ℝ))) =
      Real.rpow L (-(2 * A)) := by
  calc
    L ^ k * Real.rpow L (-(2 * A + (k : ℝ))) =
        Real.rpow L (k : ℝ) * Real.rpow L (-(2 * A + (k : ℝ))) := by
          congr 1
          exact (Real.rpow_natCast L k).symm
    _ = Real.rpow L ((k : ℝ) + (-(2 * A + (k : ℝ)))) :=
      (Real.rpow_add hL (k : ℝ) (-(2 * A + (k : ℝ)))).symm
    _ = Real.rpow L (-(2 * A)) := by
      congr 1
      ring

/-- The square of the target logarithmic rate is the doubled-exponent rate. -/
theorem rpow_neg_sq
    {L A : ℝ} (hL : 0 < L) :
    Real.rpow L (-A) ^ 2 = Real.rpow L (-(2 * A)) := by
  rw [pow_two]
  calc
    Real.rpow L (-A) * Real.rpow L (-A) =
        Real.rpow L ((-A) + (-A)) := (Real.rpow_add hL (-A) (-A)).symm
    _ = Real.rpow L (-(2 * A)) := by
      congr 1
      ring

/-- Family-level two-sided Q4 transfer.  The singular-series input is only a
polylogarithmic second-moment bound, with its exponent fixed before `X,H,h₀`.
The variance saving is strengthened to `2*A+k`, then Cauchy and the exact
finite Q4 identity recover the requested saving `A`. -/
theorem q4TwoSidedFamily_of_variance_and_singularSquare
    (hVariance : VarianceFamily)
    (hSingularSquare :
      ∀ ε : ℝ, 0 < ε →
        ∃ k : ℕ, ∃ C X₀ : ℝ,
          0 < C ∧ 2 ≤ X₀ ∧
          ∀ X H h₀ : ℝ, X₀ ≤ X →
            LegalParameters ε X H h₀ →
            singularSquareMain H h₀ ≤
              C * H * (Real.log X) ^ k) :
    Q4TwoSidedFamily := by
  intro A ε hA hε
  obtain ⟨k, Cs, Xs, hCs, hXs, hsbound⟩ := hSingularSquare ε hε
  let Av : ℝ := 2 * A + (k : ℝ)
  have hAv : 0 < Av := by
    dsimp [Av]
    positivity
  obtain ⟨Cv, Xv, hCv, hXv, hvbound⟩ := hVariance Av ε hAv hε
  let Cc : ℝ := Cs + Cv + 1
  let C : ℝ := Cv + 2 * Cc
  let X₀ : ℝ := max 3 (max Xs Xv)
  have hCs0 : 0 ≤ Cs := hCs.le
  have hCv0 : 0 ≤ Cv := hCv.le
  have hCc : 0 < Cc := by
    dsimp [Cc]
    linarith
  have hCc0 : 0 ≤ Cc := hCc.le
  have hCsCc : Cs ≤ Cc := by
    dsimp [Cc]
    linarith
  have hCvCc : Cv ≤ Cc := by
    dsimp [Cc]
    linarith
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hX₀ : 2 ≤ X₀ := by
    dsimp [X₀]
    exact le_trans (by norm_num) (le_max_left 3 (max Xs Xv))
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X H h₀ hXX₀ hlegal
  have hX3 : 3 ≤ X :=
    (le_max_left 3 (max Xs Xv)).trans hXX₀
  have hXs' : Xs ≤ X :=
    (le_trans (le_max_left Xs Xv)
      (le_max_right 3 (max Xs Xv))).trans hXX₀
  have hXv' : Xv ≤ X :=
    (le_trans (le_max_right Xs Xv)
      (le_max_right 3 (max Xs Xv))).trans hXX₀
  have hX0 : 0 ≤ X := by linarith
  have hX2 : 2 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hL3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
      Real.exp_one_lt_three
  have hlog3X : Real.log 3 ≤ Real.log X :=
    Real.log_le_log (by norm_num) hX3
  have hL : 1 ≤ Real.log X := hL3.le.trans hlog3X
  have hH0 : 0 ≤ H := by
    have hexp0 : 0 ≤ 2 / 15 + ε := by linarith
    have hH1 := (Real.one_le_rpow (one_le_two.trans hX2) hexp0).trans hlegal.1
    exact zero_le_one.trans hH1
  let modelBound : ℝ := Cs * H * (Real.log X) ^ k
  let varianceBound : ℝ :=
    Cv * H * X ^ 2 * Real.rpow (Real.log X) (-Av)
  have hmodel0 : 0 ≤ modelBound := by
    dsimp [modelBound]
    positivity
  have hvariance0 : 0 ≤ varianceBound := by
    dsimp [varianceBound]
    positivity
  have hmodel : singularSquareMain H h₀ ≤ modelBound := by
    simpa [modelBound] using hsbound X H h₀ hXs' hlegal
  have hvariance : primePairVariance X H h₀ ≤ varianceBound := by
    simpa [varianceBound] using hvbound X H h₀ hXv' hlegal
  have hbase := public_q4_deviation_le_of_bounds hX0 hmodel0
    hvariance hmodel
  have hrateV :
      Real.rpow (Real.log X) (-Av) ≤
        Real.rpow (Real.log X) (-A) := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hAAv : A ≤ Av := by
      dsimp [Av]
      linarith
    exact Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg hAAv)
  have hvarianceRate :
      varianceBound ≤ Cv * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
    dsimp [varianceBound]
    exact mul_le_mul_of_nonneg_left hrateV (by positivity)
  have hprodEq :
      modelBound * varianceBound =
        (Cs * Cv) * H ^ 2 * X ^ 2 * Real.rpow (Real.log X) (-(2 * A)) := by
    dsimp only [modelBound, varianceBound]
    change
      (Cs * H * (Real.log X) ^ k) *
          (Cv * H * X ^ 2 *
            Real.rpow (Real.log X) (-(2 * A + (k : ℝ)))) = _
    calc
      (Cs * H * (Real.log X) ^ k) *
          (Cv * H * X ^ 2 *
            Real.rpow (Real.log X) (-(2 * A + (k : ℝ)))) =
        (Cs * Cv) * H ^ 2 * X ^ 2 *
          ((Real.log X) ^ k *
            Real.rpow (Real.log X) (-(2 * A + (k : ℝ)))) := by ring
      _ = (Cs * Cv) * H ^ 2 * X ^ 2 *
          Real.rpow (Real.log X) (-(2 * A)) := by
        rw [natPow_mul_rpow_neg_sum hLpos k]
  have hconstSq : Cs * Cv ≤ Cc ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hCsCc) (sub_nonneg.mpr hCvCc)]
  have hprodBound :
      modelBound * varianceBound ≤
        (Cc * H * X * Real.rpow (Real.log X) (-A)) ^ 2 := by
    rw [hprodEq]
    have hfactor0 :
        0 ≤ H ^ 2 * X ^ 2 * Real.rpow (Real.log X) (-(2 * A)) := by
      exact mul_nonneg (mul_nonneg (sq_nonneg H) (sq_nonneg X))
        (Real.rpow_nonneg hLpos.le _)
    calc
      (Cs * Cv) * H ^ 2 * X ^ 2 * Real.rpow (Real.log X) (-(2 * A)) =
          (Cs * Cv) *
            (H ^ 2 * X ^ 2 * Real.rpow (Real.log X) (-(2 * A))) := by ring
      _ ≤ Cc ^ 2 *
            (H ^ 2 * X ^ 2 * Real.rpow (Real.log X) (-(2 * A))) :=
        mul_le_mul_of_nonneg_right hconstSq hfactor0
      _ = (Cc * H * X * Real.rpow (Real.log X) (-A)) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, rpow_neg_sq hLpos]
        ring
  have hrootBound :
      Real.sqrt (modelBound * varianceBound) ≤
        Cc * H * X * Real.rpow (Real.log X) (-A) := by
    calc
      Real.sqrt (modelBound * varianceBound) ≤
          Real.sqrt ((Cc * H * X * Real.rpow (Real.log X) (-A)) ^ 2) :=
        Real.sqrt_le_sqrt hprodBound
      _ = |Cc * H * X * Real.rpow (Real.log X) (-A)| :=
        Real.sqrt_sq_eq_abs _
      _ = Cc * H * X * Real.rpow (Real.log X) (-A) := by
        rw [abs_of_nonneg]
        exact mul_nonneg
          (mul_nonneg (mul_nonneg hCc0 hH0) hX0)
          (Real.rpow_nonneg hLpos.le _)
  calc
    |q4Quantity X H h₀ - X ^ 2 * singularSquareMain H h₀| ≤
        varianceBound + 2 * X * Real.sqrt (modelBound * varianceBound) := hbase
    _ ≤ Cv * H * X ^ 2 * Real.rpow (Real.log X) (-A) +
        2 * X * (Cc * H * X * Real.rpow (Real.log X) (-A)) := by
      gcongr
    _ = C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
      dsimp [C]
      ring

/-- Auxiliary endpoint under the same deliberately strong uniform-cutoff
premise. The manuscript-facing endpoint is the selectable-cutoff theorem in
`MAPVarianceTransferCutoffWeld`. -/
theorem certifiedMAPEndpoint_of_localMAP_uniformRemainder_singularSquare
    (hMAP : AllCenterLocalMAP)
    (hRemainder :
      ∀ A ε : ℝ, 0 < A → 0 < ε →
        ∀ B D : ℕ, ∃ C X₀ : ℝ,
          0 < C ∧ 2 ≤ X₀ ∧
          ∀ X H h₀ : ℝ, X₀ ≤ X →
            LegalParameters ε X H h₀ →
            deterministicRemainderEnergy X H h₀ B D ≤
              C * H * X ^ 2 * Real.rpow (Real.log X) (-A))
    (hSingularSquare :
      ∀ ε : ℝ, 0 < ε →
        ∃ k : ℕ, ∃ C X₀ : ℝ,
          0 < C ∧ 2 ≤ X₀ ∧
          ∀ X H h₀ : ℝ, X₀ ≤ X →
            LegalParameters ε X H h₀ →
            singularSquareMain H h₀ ≤
              C * H * (Real.log X) ^ k) :
    CertifiedMAPEndpoint := by
  have hVariance := varianceFamily_of_allCenterLocalMAP_and_uniform_remainder
    hMAP hRemainder
  have hQ4 := q4TwoSidedFamily_of_variance_and_singularSquare
    hVariance hSingularSquare
  exact certifiedMAPEndpoint_of_map_variance_q4TwoSided hMAP hVariance hQ4

end

end MAPVarianceTransferWeld
