import CertifiedMAPEndpointFinalWeld
import SupportBoundaryQuantitative

/-!
# Deterministic last-mile connector for the all-center MAP endpoint

The public endpoint weld currently accepts a bound for the combined
major/support deterministic remainder.  The support-boundary contribution is
already certified.  This module splits the combined energy exactly and leaves
only the genuine major-coefficient approximation as an analytic input.
-/

namespace MAPFinalDeterministicConnector

open scoped BigOperators
open PrimePairEndpoints MAPHarmonicEndpoint
open MAPVarianceTransferWeld

noncomputable section

/-- Error of the major Fourier coefficient against the public `X*S(h)`
model.  The overlap correction can be absorbed here by a source-faithful
major-arc proof; no minor coefficient occurs in this definition. -/
def majorModelError (X : ℝ) (B D : ℕ) (h : ℤ) : ℂ :=
  majorCoefficient X B D h -
    ((X * singularSeriesTotal h : ℝ) : ℂ)

/-- Translated square energy of the genuine major-model error, with the same
zero-shift deletion as the public prime-pair signal. -/
def majorModelErrorEnergy (X H h₀ : ℝ) (B D : ℕ) : ℝ :=
  ∑ h ∈ translatedWindow H h₀,
    if h = 0 then 0 else ‖majorModelError X B D h‖ ^ 2

/-- The already-certified one-sided/twice-supported boundary energy. -/
def boundaryCorrectionEnergy (X H h₀ : ℝ) : ℝ :=
  ∑ h ∈ translatedWindow H h₀,
    if h = 0 then 0 else
      |SupportBoundaryWeld.supportBoundaryCorrection X h| ^ 2

/-- Error against the overlap model which is the literal target of the
certified continuous-kernel major-arc weld. -/
def majorOverlapError (X : ℝ) (B D : ℕ) (h : ℤ) : ℂ :=
  majorCoefficient X B D h - MAPMajorArcWeld.primePairMajorModel X h

/-- Translated square energy of the genuine overlap-model major-arc error. -/
def majorOverlapErrorEnergy (X H h₀ : ℝ) (B D : ℕ) : ℝ :=
  ∑ h ∈ translatedWindow H h₀,
    if h = 0 then 0 else ‖majorOverlapError X B D h‖ ^ 2

/-- The deterministic difference between the overlap model
`(X-|h|) * S(h)` and the public variance model `X * S(h)`.  The zero term is
already zero because `singularSeriesTotal 0 = 0`. -/
def overlapCorrectionEnergy (_X H h₀ : ℝ) : ℝ :=
  ∑ h ∈ translatedWindow H h₀,
    |(h : ℝ)| ^ 2 * (singularSeriesTotal h) ^ 2

theorem deterministicRemainder_eq_majorModelError_add_boundary
    (X : ℝ) (B D : ℕ) (h : ℤ) :
    deterministicRemainder X B D h =
      majorModelError X B D h +
        (SupportBoundaryWeld.supportBoundaryCorrection X h : ℂ) := by
  unfold deterministicRemainder majorModelError
  push_cast
  ring

/-- Exact decomposition at the overlap-model boundary used by the major-arc
modules. -/
theorem deterministicRemainder_eq_overlapError_add_boundary_sub_overlap
    (X : ℝ) (B D : ℕ) (h : ℤ) :
    deterministicRemainder X B D h =
      majorOverlapError X B D h +
        (SupportBoundaryWeld.supportBoundaryCorrection X h : ℂ) -
          ((|(h : ℝ)| * singularSeriesTotal h : ℝ) : ℂ) := by
  unfold deterministicRemainder majorOverlapError
    MAPMajorArcWeld.primePairMajorModel
  push_cast
  ring

/-- Three-term square-energy separation at the literal overlap model. -/
theorem deterministicRemainderEnergy_le_overlap_add_corrections
    (X H h₀ : ℝ) (B D : ℕ) :
    deterministicRemainderEnergy X H h₀ B D ≤
      4 * majorOverlapErrorEnergy X H h₀ B D +
        4 * boundaryCorrectionEnergy X H h₀ +
          2 * overlapCorrectionEnergy X H h₀ := by
  classical
  unfold deterministicRemainderEnergy majorOverlapErrorEnergy
    boundaryCorrectionEnergy overlapCorrectionEnergy
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h hh
  by_cases hh0 : h = 0
  · subst h
    simp [singularSeriesTotal]
  · simp only [if_neg hh0]
    rw [deterministicRemainder_eq_overlapError_add_boundary_sub_overlap]
    let a : ℂ := majorOverlapError X B D h
    let b : ℂ := (SupportBoundaryWeld.supportBoundaryCorrection X h : ℂ)
    let c : ℂ := -((|(h : ℝ)| * singularSeriesTotal h : ℝ) : ℂ)
    have hab := norm_add_sq_le_two_mul a b
    have habc := norm_add_sq_le_two_mul (a + b) c
    have hc : ‖c‖ ^ 2 = |(h : ℝ)| ^ 2 * (singularSeriesTotal h) ^ 2 := by
      dsimp [c]
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul, mul_pow]
      simp only [abs_abs, sq_abs]
    change ‖a + b + c‖ ^ 2 ≤
      4 * ‖a‖ ^ 2 +
        4 * |SupportBoundaryWeld.supportBoundaryCorrection X h| ^ 2 +
          2 * (|(h : ℝ)| ^ 2 * singularSeriesTotal h ^ 2)
    have hbcast : ‖b‖ =
        |SupportBoundaryWeld.supportBoundaryCorrection X h| := by
      simp [b, Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖a + b + c‖ ^ 2 ≤ 2 * ‖a + b‖ ^ 2 + 2 * ‖c‖ ^ 2 := habc
      _ ≤ 2 * (2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2) + 2 * ‖c‖ ^ 2 := by
        gcongr
      _ = 4 * ‖a‖ ^ 2 +
          4 * |SupportBoundaryWeld.supportBoundaryCorrection X h| ^ 2 +
            2 * (|(h : ℝ)| ^ 2 * singularSeriesTotal h ^ 2) := by
        rw [hbcast, hc]
        ring

/-- Exact square-energy separation.  This is finite algebra, not a major-arc
or MAP estimate. -/
theorem deterministicRemainderEnergy_le_major_add_boundary
    (X H h₀ : ℝ) (B D : ℕ) :
    deterministicRemainderEnergy X H h₀ B D ≤
      2 * majorModelErrorEnergy X H h₀ B D +
        2 * boundaryCorrectionEnergy X H h₀ := by
  classical
  unfold deterministicRemainderEnergy majorModelErrorEnergy
    boundaryCorrectionEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h hh
  by_cases hh0 : h = 0
  · simp [hh0]
  · simp only [if_neg hh0]
    rw [deterministicRemainder_eq_majorModelError_add_boundary]
    have hsquare := norm_add_sq_le_two_mul
      (majorModelError X B D h)
      (SupportBoundaryWeld.supportBoundaryCorrection X h : ℂ)
    simpa [Complex.norm_real, Real.norm_eq_abs] using hsquare

/-- The quantitative support-boundary theorem, expressed in the exact energy
used by the deterministic split. -/
theorem boundaryCorrectionEnergy_le_logSaving :
    ∀ A ε : ℝ, 0 < A → 0 < ε →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X H h₀ : ℝ, X₀ ≤ X →
          LegalParameters ε X H h₀ →
          boundaryCorrectionEnergy X H h₀ ≤
            C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
  intro A ε hA hε
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ :=
    SupportBoundaryQuantitative.supportBoundary_sq_sum_le_logSaving
      A ε hA hε
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X H h₀ hXX₀ hlegal
  have hbase := hbound X H h₀ hXX₀ hlegal
  unfold boundaryCorrectionEnergy
  calc
    (∑ h ∈ translatedWindow H h₀,
        if h = 0 then 0 else
          |SupportBoundaryWeld.supportBoundaryCorrection X h| ^ 2) =
      ∑ h ∈ translatedWindow H h₀,
        |primePairSignal X h -
          SupportBoundaryQuantitative.dyadicSignal X h| ^ 2 := by
        apply Finset.sum_congr rfl
        intro h hh
        by_cases hh0 : h = 0
        · subst h
          simp [primePairSignal, SupportBoundaryQuantitative.dyadicSignal]
        · simp only [if_neg hh0]
          rw [SupportBoundaryQuantitative.primePairSignal_sub_dyadicSignal hh0]
    _ ≤ C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := hbase

/-- Pointwise shift-size extraction from the overlap correction, summed on the
exact translated window. -/
theorem overlapCorrectionEnergy_le_rpow_mul_singularSquare
    {X H h₀ ε : ℝ} (hX : 0 < X)
    (hlegal : LegalParameters ε X H h₀) :
    overlapCorrectionEnergy X H h₀ ≤
      4 * Real.rpow X (2 - 2 * ε) * singularSquareMain H h₀ := by
  unfold overlapCorrectionEnergy singularSquareMain
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  have habsNat := SupportBoundaryQuantitative.natAbs_shift_le_two_rpow hlegal hh
  have habsEq : (h.natAbs : ℝ) = |(h : ℝ)| := by
    rw [← Int.cast_abs]
    norm_num
  have habs : |(h : ℝ)| ≤ 2 * Real.rpow X (1 - ε) := by
    rw [← habsEq]
    exact habsNat
  have hright0 : 0 ≤ 2 * Real.rpow X (1 - ε) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hX.le _)
  have hsq : |(h : ℝ)| ^ 2 ≤
      4 * Real.rpow X (2 - 2 * ε) := by
    calc
      |(h : ℝ)| ^ 2 ≤ (2 * Real.rpow X (1 - ε)) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) hright0).2 habs
      _ = 4 * (Real.rpow X (1 - ε) * Real.rpow X (1 - ε)) := by ring
      _ = 4 * Real.rpow X ((1 - ε) + (1 - ε)) := by
        exact congrArg (fun z : ℝ => 4 * z)
          (Real.rpow_add hX (1 - ε) (1 - ε)).symm
      _ = 4 * Real.rpow X (2 - 2 * ε) := by ring_nf
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- Six-logarithm version of the power/log trade used for the overlap-model
correction. -/
theorem power_log_six_trade
    {A ε X : ℝ} (hX : 1 < X)
    (hpoly : Real.rpow (Real.log X) (A + 6) ≤
      Real.rpow X (2 * ε)) :
    Real.rpow X (2 - 2 * ε) * (Real.log X) ^ 6 ≤
      X ^ 2 * Real.rpow (Real.log X) (-A) := by
  have hXpos : 0 < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos hX
  have hneg0 : 0 ≤ Real.rpow (Real.log X) (-A) :=
    Real.rpow_nonneg hlogpos.le _
  have hm := mul_le_mul_of_nonneg_right hpoly hneg0
  have hleft : Real.rpow (Real.log X) (A + 6) *
      Real.rpow (Real.log X) (-A) = (Real.log X) ^ 6 := by
    calc
      Real.rpow (Real.log X) (A + 6) *
          Real.rpow (Real.log X) (-A) =
          Real.rpow (Real.log X) ((A + 6) + (-A)) :=
        (Real.rpow_add hlogpos _ _).symm
      _ = Real.rpow (Real.log X) (6 : ℝ) := by ring_nf
      _ = (Real.log X) ^ 6 := Real.rpow_natCast _ 6
  have hlogtrade : (Real.log X) ^ 6 ≤
      Real.rpow X (2 * ε) * Real.rpow (Real.log X) (-A) := by
    rw [← hleft]
    exact hm
  have hmul := mul_le_mul_of_nonneg_left hlogtrade
    (Real.rpow_nonneg hXpos.le (2 - 2 * ε))
  have hxprod : Real.rpow X (2 - 2 * ε) * Real.rpow X (2 * ε) =
      X ^ 2 := by
    calc
      Real.rpow X (2 - 2 * ε) * Real.rpow X (2 * ε) =
          Real.rpow X ((2 - 2 * ε) + (2 * ε)) :=
        (Real.rpow_add hXpos _ _).symm
      _ = Real.rpow X (2 : ℝ) := by ring_nf
      _ = X ^ 2 := Real.rpow_natCast X 2
  calc
    Real.rpow X (2 - 2 * ε) * (Real.log X) ^ 6 ≤
        Real.rpow X (2 - 2 * ε) *
          (Real.rpow X (2 * ε) * Real.rpow (Real.log X) (-A)) := hmul
    _ = (Real.rpow X (2 - 2 * ε) * Real.rpow X (2 * ε)) *
          Real.rpow (Real.log X) (-A) := by ring
    _ = X ^ 2 * Real.rpow (Real.log X) (-A) := by rw [hxprod]

/-- The overlap-to-public-model correction is a certified logarithmic-saving
error on every legal translated window. -/
theorem overlapCorrectionEnergy_le_logSaving :
    ∀ A ε : ℝ, 0 < A → 0 < ε →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X H h₀ : ℝ, X₀ ≤ X →
          LegalParameters ε X H h₀ →
          overlapCorrectionEnergy X H h₀ ≤
            C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
  intro A ε hA hε
  obtain ⟨Cs, Xs, hCs, hXs, hs⟩ :=
    SingularSeriesSquareMean.translated_singularSquareMain_le ε hε
  have hpoly := SupportBoundaryQuantitative.polylog_absorption
    (A + 6) (2 * ε) (by positivity)
  have hall : ∀ᶠ X : ℝ in Filter.atTop,
      3 ≤ X ∧
      Real.rpow (Real.log X) (A + 6) ≤ Real.rpow X (2 * ε) := by
    filter_upwards [Filter.eventually_ge_atTop (3 : ℝ), hpoly] with X hX hp
    exact ⟨hX, hp⟩
  rcases Filter.eventually_atTop.1 hall with ⟨threshold, hthreshold⟩
  let C : ℝ := 4 * Cs
  let X₀ : ℝ := max Xs threshold
  refine ⟨C, X₀, by dsimp [C]; positivity,
    le_trans hXs (le_max_left _ _), ?_⟩
  intro X H h₀ hXX₀ hlegal
  have hXXs : Xs ≤ X := (le_max_left Xs threshold).trans hXX₀
  have hXt : threshold ≤ X := (le_max_right Xs threshold).trans hXX₀
  obtain ⟨hX3, hpolyX⟩ := hthreshold X hXt
  have hH1 := SupportBoundaryQuantitative.one_le_H_of_legal
    (by linarith : 1 ≤ X) hε hlegal
  have henergy := overlapCorrectionEnergy_le_rpow_mul_singularSquare
    (by linarith : 0 < X) hlegal
  have hsingular := hs X H h₀ hXXs hlegal
  have hmulSingular :
      4 * Real.rpow X (2 - 2 * ε) * singularSquareMain H h₀ ≤
        4 * Real.rpow X (2 - 2 * ε) *
          (Cs * H * (Real.log X) ^ 6) := by
    exact mul_le_mul_of_nonneg_left hsingular
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _))
  have htrade := power_log_six_trade (by linarith : 1 < X) hpolyX
  have hfactor0 : 0 ≤ 4 * Cs * H := by positivity
  calc
    overlapCorrectionEnergy X H h₀ ≤
        4 * Real.rpow X (2 - 2 * ε) * singularSquareMain H h₀ := henergy
    _ ≤ 4 * Real.rpow X (2 - 2 * ε) *
          (Cs * H * (Real.log X) ^ 6) := hmulSingular
    _ = (4 * Cs * H) *
          (Real.rpow X (2 - 2 * ε) * (Real.log X) ^ 6) := by ring
    _ ≤ (4 * Cs * H) *
          (X ^ 2 * Real.rpow (Real.log X) (-A)) :=
      mul_le_mul_of_nonneg_left htrade hfactor0
    _ = C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
      dsimp [C]
      ring

/-- A selectable major-coefficient approximation plus the certified boundary
estimate yields exactly the selectable deterministic-remainder premise used by
the cutoff-faithful variance weld. -/
theorem selectableRemainder_of_selectableMajorModelError
    (hMajor :
      ∀ A ε : ℝ, 0 < A → 0 < ε →
        ∀ B₀ D₀ : ℕ,
          ∃ B D : ℕ, B₀ ≤ B ∧ D₀ ≤ D ∧
            ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
              ∀ X H h₀ : ℝ, X₀ ≤ X →
                LegalParameters ε X H h₀ →
                majorModelErrorEnergy X H h₀ B D ≤
                  C * H * X ^ 2 * Real.rpow (Real.log X) (-A)) :
    ∀ A ε : ℝ, 0 < A → 0 < ε →
      ∀ B₀ D₀ : ℕ,
        ∃ B D : ℕ, B₀ ≤ B ∧ D₀ ≤ D ∧
          ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
            ∀ X H h₀ : ℝ, X₀ ≤ X →
              LegalParameters ε X H h₀ →
              deterministicRemainderEnergy X H h₀ B D ≤
                C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
  intro A ε hA hε B₀ D₀
  obtain ⟨B, D, hB, hD, Cmajor, Xmajor, hCmajor, hXmajor, hmajor⟩ :=
    hMajor A ε hA hε B₀ D₀
  obtain ⟨Cboundary, Xboundary, hCboundary, hXboundary, hboundary⟩ :=
    boundaryCorrectionEnergy_le_logSaving A ε hA hε
  let C := 2 * Cmajor + 2 * Cboundary
  let X₀ := max Xmajor Xboundary
  refine ⟨B, D, hB, hD, C, X₀, by dsimp [C]; positivity,
    le_trans hXmajor (le_max_left _ _), ?_⟩
  intro X H h₀ hXX₀ hlegal
  have hXM : Xmajor ≤ X := (le_max_left Xmajor Xboundary).trans hXX₀
  have hXB : Xboundary ≤ X := (le_max_right Xmajor Xboundary).trans hXX₀
  have hsplit := deterministicRemainderEnergy_le_major_add_boundary
    X H h₀ B D
  have hm := hmajor X H h₀ hXM hlegal
  have hb := hboundary X H h₀ hXB hlegal
  calc
    deterministicRemainderEnergy X H h₀ B D ≤
        2 * majorModelErrorEnergy X H h₀ B D +
          2 * boundaryCorrectionEnergy X H h₀ := hsplit
    _ ≤ 2 * (Cmajor * H * X ^ 2 * Real.rpow (Real.log X) (-A)) +
        2 * (Cboundary * H * X ^ 2 * Real.rpow (Real.log X) (-A)) := by
      gcongr
    _ = C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
      dsimp [C]
      ring

/-- Stronger source-facing adapter: it accepts only the selectable energy
bound against the continuous overlap model which the existing major-arc weld
actually produces.  The support collar and the change from `(X-|h|)S(h)` to
`X*S(h)` are discharged here. -/
theorem selectableRemainder_of_selectableMajorOverlapError
    (hMajor :
      ∀ A ε : ℝ, 0 < A → 0 < ε →
        ∀ B₀ D₀ : ℕ,
          ∃ B D : ℕ, B₀ ≤ B ∧ D₀ ≤ D ∧
            ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
              ∀ X H h₀ : ℝ, X₀ ≤ X →
                LegalParameters ε X H h₀ →
                majorOverlapErrorEnergy X H h₀ B D ≤
                  C * H * X ^ 2 * Real.rpow (Real.log X) (-A)) :
    ∀ A ε : ℝ, 0 < A → 0 < ε →
      ∀ B₀ D₀ : ℕ,
        ∃ B D : ℕ, B₀ ≤ B ∧ D₀ ≤ D ∧
          ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
            ∀ X H h₀ : ℝ, X₀ ≤ X →
              LegalParameters ε X H h₀ →
              deterministicRemainderEnergy X H h₀ B D ≤
                C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
  intro A ε hA hε B₀ D₀
  obtain ⟨B, D, hB, hD, Cmajor, Xmajor, hCmajor, hXmajor, hmajor⟩ :=
    hMajor A ε hA hε B₀ D₀
  obtain ⟨Cboundary, Xboundary, hCboundary, hXboundary, hboundary⟩ :=
    boundaryCorrectionEnergy_le_logSaving A ε hA hε
  obtain ⟨Coverlap, Xoverlap, hCoverlap, hXoverlap, hoverlap⟩ :=
    overlapCorrectionEnergy_le_logSaving A ε hA hε
  let C := 4 * Cmajor + 4 * Cboundary + 2 * Coverlap
  let X₀ := max Xmajor (max Xboundary Xoverlap)
  refine ⟨B, D, hB, hD, C, X₀, by dsimp [C]; positivity,
    le_trans hXmajor (le_max_left _ _), ?_⟩
  intro X H h₀ hXX₀ hlegal
  have hXM : Xmajor ≤ X :=
    (le_max_left Xmajor (max Xboundary Xoverlap)).trans hXX₀
  have hXB : Xboundary ≤ X :=
    (le_trans (le_max_left Xboundary Xoverlap)
      (le_max_right Xmajor (max Xboundary Xoverlap))).trans hXX₀
  have hXO : Xoverlap ≤ X :=
    (le_trans (le_max_right Xboundary Xoverlap)
      (le_max_right Xmajor (max Xboundary Xoverlap))).trans hXX₀
  have hsplit := deterministicRemainderEnergy_le_overlap_add_corrections
    X H h₀ B D
  have hm := hmajor X H h₀ hXM hlegal
  have hb := hboundary X H h₀ hXB hlegal
  have ho := hoverlap X H h₀ hXO hlegal
  calc
    deterministicRemainderEnergy X H h₀ B D ≤
        4 * majorOverlapErrorEnergy X H h₀ B D +
          4 * boundaryCorrectionEnergy X H h₀ +
            2 * overlapCorrectionEnergy X H h₀ := hsplit
    _ ≤ 4 * (Cmajor * H * X ^ 2 * Real.rpow (Real.log X) (-A)) +
        4 * (Cboundary * H * X ^ 2 * Real.rpow (Real.log X) (-A)) +
          2 * (Coverlap * H * X ^ 2 * Real.rpow (Real.log X) (-A)) := by
      gcongr
    _ = C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
      dsimp [C]
      ring

/-- Final two-input endpoint connector.  Q4, density one, the singular-square
mean, and the support-boundary contribution are discharged internally. -/
theorem certifiedMAPEndpoint_of_localMAP_selectableMajorModelError
    (hMAP : AllCenterLocalMAP)
    (hMajor :
      ∀ A ε : ℝ, 0 < A → 0 < ε →
        ∀ B₀ D₀ : ℕ,
          ∃ B D : ℕ, B₀ ≤ B ∧ D₀ ≤ D ∧
            ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
              ∀ X H h₀ : ℝ, X₀ ≤ X →
                LegalParameters ε X H h₀ →
                majorModelErrorEnergy X H h₀ B D ≤
                  C * H * X ^ 2 * Real.rpow (Real.log X) (-A)) :
    CertifiedMAPEndpoint := by
  exact CertifiedMAPEndpointFinalWeld.certifiedMAPEndpoint_of_localMAP_selectableRemainder
    hMAP (selectableRemainder_of_selectableMajorModelError hMajor)

/-- Compatibility projection to the package's headline endpoint surface. -/
theorem fullUnconditionalMAPEndpoint_of_localMAP_selectableMajorModelError
    (hMAP : AllCenterLocalMAP)
    (hMajor :
      ∀ A ε : ℝ, 0 < A → 0 < ε →
        ∀ B₀ D₀ : ℕ,
          ∃ B D : ℕ, B₀ ≤ B ∧ D₀ ≤ D ∧
            ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
              ∀ X H h₀ : ℝ, X₀ ≤ X →
                LegalParameters ε X H h₀ →
                majorModelErrorEnergy X H h₀ B D ≤
                  C * H * X ^ 2 * Real.rpow (Real.log X) (-A)) :
    FullUnconditionalMAPEndpoint := by
  exact PrimePairEndpoints.certifiedMAPEndpoint_implies_fullUnconditionalMAPEndpoint
    (certifiedMAPEndpoint_of_localMAP_selectableMajorModelError hMAP hMajor)

/-- Final endpoint using the exact overlap-model major error as the only
deterministic analytic premise. -/
theorem certifiedMAPEndpoint_of_localMAP_selectableMajorOverlapError
    (hMAP : AllCenterLocalMAP)
    (hMajor :
      ∀ A ε : ℝ, 0 < A → 0 < ε →
        ∀ B₀ D₀ : ℕ,
          ∃ B D : ℕ, B₀ ≤ B ∧ D₀ ≤ D ∧
            ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
              ∀ X H h₀ : ℝ, X₀ ≤ X →
                LegalParameters ε X H h₀ →
                majorOverlapErrorEnergy X H h₀ B D ≤
                  C * H * X ^ 2 * Real.rpow (Real.log X) (-A)) :
    CertifiedMAPEndpoint := by
  exact CertifiedMAPEndpointFinalWeld.certifiedMAPEndpoint_of_localMAP_selectableRemainder
    hMAP (selectableRemainder_of_selectableMajorOverlapError hMajor)

/-- Compatibility projection of the overlap-model connector to the original
headline endpoint. -/
theorem fullUnconditionalMAPEndpoint_of_localMAP_selectableMajorOverlapError
    (hMAP : AllCenterLocalMAP)
    (hMajor :
      ∀ A ε : ℝ, 0 < A → 0 < ε →
        ∀ B₀ D₀ : ℕ,
          ∃ B D : ℕ, B₀ ≤ B ∧ D₀ ≤ D ∧
            ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
              ∀ X H h₀ : ℝ, X₀ ≤ X →
                LegalParameters ε X H h₀ →
                majorOverlapErrorEnergy X H h₀ B D ≤
                  C * H * X ^ 2 * Real.rpow (Real.log X) (-A)) :
    FullUnconditionalMAPEndpoint := by
  exact PrimePairEndpoints.certifiedMAPEndpoint_implies_fullUnconditionalMAPEndpoint
    (certifiedMAPEndpoint_of_localMAP_selectableMajorOverlapError hMAP hMajor)

end

end MAPFinalDeterministicConnector

#print axioms MAPFinalDeterministicConnector.deterministicRemainderEnergy_le_overlap_add_corrections
#print axioms MAPFinalDeterministicConnector.boundaryCorrectionEnergy_le_logSaving
#print axioms MAPFinalDeterministicConnector.overlapCorrectionEnergy_le_logSaving
#print axioms MAPFinalDeterministicConnector.selectableRemainder_of_selectableMajorOverlapError
