import KoukSelectedHeightRealEndpointFormula
import FullStripA5Family
import PrincipalZetaFullStrip
import LocalZeroCountSlice

/-!
# Transporting the full zero cutoff in Koukoulopoulos Theorem 11.3

The contour in the proof of Theorem 11.3 is moved at a nearby good height
`T' ∈ [T,T+1]`.  The theorem itself is stated with the originally requested
cutoff `T`.  This module records the exact finite-divisor difference and
the source-faithful thin-band majorant.  No contour estimate occurs here.
-/

namespace KoukTheorem113ZeroCutoffTransport

open Complex Set
open scoped BigOperators
open DirichletZeros MAPMellinDetectorLeaf MAPLocalZeroWindow
open MAPEndpointRegularizedZeroPrimitive
open PrimitiveExplicitFormulaSpine

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The zeros added when a full closed cutoff is raised from `T` to `T'`. -/
def cutoffBandSupport (chi : DirichletCharacter ℂ q)
    (T T' : ℝ) : Finset ℂ :=
  zeroSupport chi 0 T' \ zeroSupport chi 0 T

def positiveCutoffBand (chi : DirichletCharacter ℂ q)
    (T T' : ℝ) : Finset ℂ :=
  (cutoffBandSupport chi T T').filter fun rho => 0 ≤ rho.im

def negativeCutoffBand (chi : DirichletCharacter ℂ q)
    (T T' : ℝ) : Finset ℂ :=
  (cutoffBandSupport chi T T').filter fun rho => rho.im < 0

/-- Multiplicities in the smaller and larger rectangles agree on their
common support. -/
theorem zeroMultiplicity_eq_of_cutoff_le
    (chi : DirichletCharacter ℂ q) {T T' : ℝ} (hTT' : T ≤ T')
    {rho : ℂ} (hrho : rho ∈ zeroSupport chi 0 T) :
    zeroMultiplicity chi 0 T rho = zeroMultiplicity chi 0 T' rho := by
  have hinner := mem_zeroRectangle_of_mem_zeroSupport chi 0 T hrho
  have houter := zeroRectangle_mono (sigmaOuter := (0 : ℝ))
    (sigmaInner := (0 : ℝ)) le_rfl hTT' hinner
  exact zeroMultiplicity_eq_of_mem_rectangles chi hinner houter

/-- Exact cutoff transport for the endpoint-regularized zero primitive. -/
theorem endpointZeroTerm_sub_eq_bandSum
    (chi : DirichletCharacter ℂ q) {T T' t : ℝ} (hTT' : T ≤ T') :
    endpointMultiplicityWeightedZeroTerm chi 0 T' t -
        endpointMultiplicityWeightedZeroTerm chi 0 T t =
      ∑ rho ∈ cutoffBandSupport chi T T',
        (zeroMultiplicity chi 0 T' rho : ℂ) *
          endpointRegularizedZeroTerm t rho := by
  classical
  let outer := zeroSupport chi 0 T'
  let inner := zeroSupport chi 0 T
  let f : ℂ → ℂ := fun rho =>
    (zeroMultiplicity chi 0 T' rho : ℂ) *
      endpointRegularizedZeroTerm t rho
  have hsub : inner ⊆ outer := zeroSupport_mono chi le_rfl hTT'
  have hinner :
      (∑ rho ∈ inner,
          (zeroMultiplicity chi 0 T rho : ℂ) *
            endpointRegularizedZeroTerm t rho) =
        ∑ rho ∈ inner, f rho := by
    apply Finset.sum_congr rfl
    intro rho hrho
    simp only [f, zeroMultiplicity_eq_of_cutoff_le chi hTT' hrho]
  have hsdiff := Finset.sum_sdiff_eq_sub (f := f) hsub
  unfold endpointMultiplicityWeightedZeroTerm endpointFiniteZeroPrimitive
    cutoffBandSupport
  change (∑ rho ∈ outer, f rho) -
      (∑ rho ∈ inner,
        (zeroMultiplicity chi 0 T rho : ℂ) *
          endpointRegularizedZeroTerm t rho) =
      ∑ rho ∈ outer \ inner, f rho
  rw [hinner]
  exact hsdiff.symm

/-- A zero in the added band has ordinate strictly outside the old closed
rectangle. -/
theorem lt_abs_im_of_mem_cutoffBand
    (chi : DirichletCharacter ℂ q) {T T' : ℝ} (hT : 0 ≤ T)
    {rho : ℂ} (hrho : rho ∈ cutoffBandSupport chi T T') :
    T < |rho.im| := by
  have hnot : rho ∉ zeroSupport chi 0 T :=
    (Finset.mem_sdiff.mp hrho).2
  have houter : rho ∈ zeroSupport chi 0 T' :=
    (Finset.mem_sdiff.mp hrho).1
  have houterRect := mem_zeroRectangle_of_mem_zeroSupport chi 0 T' houter
  by_contra h
  have him : |rho.im| ≤ T := le_of_not_gt h
  have hrect : rho ∈ zeroRectangle 0 T := by
    rw [zeroRectangle, Complex.mem_reProdIm]
    exact ⟨houterRect.1, abs_le.mp him⟩
  have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport chi 0 T' houter
  have hmem := (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
    chi 0 T hrect).2 hzero
  exact hnot hmem

/-- On the added band, every endpoint kernel is bounded by `2t/T`. -/
theorem norm_endpointRegularizedZeroTerm_le_two_mul_div
    (chi : DirichletCharacter ℂ q) {T T' t : ℝ}
    (hT : 0 < T) (ht : 1 ≤ t)
    {rho : ℂ} (hrho : rho ∈ cutoffBandSupport chi T T') :
    ‖endpointRegularizedZeroTerm t rho‖ ≤ 2 * t / T := by
  have him := lt_abs_im_of_mem_cutoffBand chi hT.le hrho
  have hrho0 : rho ≠ 0 := by
    intro hz
    subst rho
    simpa using (hT.trans him)
  have houter : rho ∈ zeroSupport chi 0 T' :=
    (Finset.mem_sdiff.mp hrho).1
  have hrect := mem_zeroRectangle_of_mem_zeroSupport chi 0 T' houter
  have hre0 : 0 ≤ rho.re := hrect.1.1
  have hre1 : rho.re ≤ 1 := hrect.1.2
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hpow : t ^ rho.re ≤ t := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le ht hre1
  have hden : T ≤ ‖rho‖ := by
    exact him.le.trans (Complex.abs_im_le_norm rho)
  have hnum : ‖(t : ℂ) ^ rho - 1‖ ≤ 2 * t := by
    calc
      ‖(t : ℂ) ^ rho - 1‖ ≤ ‖(t : ℂ) ^ rho‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = t ^ rho.re + 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        norm_num
      _ ≤ t + 1 := by linarith
      _ ≤ 2 * t := by linarith
  simp [endpointRegularizedZeroTerm,
    APFoundation.regularizedZeroTerm, hrho0]
  exact (div_le_div_of_nonneg_right hnum (norm_nonneg rho)).trans
    (div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * t) hT hden)

/-- The complex cutoff correction is bounded by its band multiplicity. -/
theorem norm_endpointZeroTerm_cutoffDifference_le_bandMass
    (chi : DirichletCharacter ℂ q) {T T' t : ℝ}
    (hT : 0 < T) (hTT' : T ≤ T') (ht : 1 ≤ t) :
    ‖endpointMultiplicityWeightedZeroTerm chi 0 T' t -
        endpointMultiplicityWeightedZeroTerm chi 0 T t‖ ≤
      (2 * t / T) *
        ∑ rho ∈ cutoffBandSupport chi T T',
          (zeroMultiplicity chi 0 T' rho : ℝ) := by
  rw [endpointZeroTerm_sub_eq_bandSum chi hTT']
  calc
    ‖∑ rho ∈ cutoffBandSupport chi T T',
        (zeroMultiplicity chi 0 T' rho : ℂ) *
          endpointRegularizedZeroTerm t rho‖ ≤
      ∑ rho ∈ cutoffBandSupport chi T T',
        ‖(zeroMultiplicity chi 0 T' rho : ℂ) *
          endpointRegularizedZeroTerm t rho‖ := norm_sum_le _ _
    _ ≤ ∑ rho ∈ cutoffBandSupport chi T T',
        (zeroMultiplicity chi 0 T' rho : ℝ) * (2 * t / T) := by
      apply Finset.sum_le_sum
      intro rho hrho
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        (norm_endpointRegularizedZeroTerm_le_two_mul_div
          chi hT ht hrho) (Nat.cast_nonneg _)
    _ = (2 * t / T) *
        ∑ rho ∈ cutoffBandSupport chi T T',
          (zeroMultiplicity chi 0 T' rho : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho hrho
      ring

/-- The positive half of a unit cutoff band lies in the positive local
unit-window support based at the requested height. -/
theorem positiveCutoffBand_subset_closedUnitWindow
    (chi : DirichletCharacter ℂ q) {T T' : ℝ}
    (hT : 0 ≤ T) (hTT' : T ≤ T') (hT' : T' ≤ T + 1) :
    positiveCutoffBand chi T T' ⊆
      closedUnitWindowSupport chi 0 T := by
  intro rho hrho
  have hband : rho ∈ cutoffBandSupport chi T T' :=
    (Finset.mem_filter.mp hrho).1
  have him0 : 0 ≤ rho.im := (Finset.mem_filter.mp hrho).2
  have habs := lt_abs_im_of_mem_cutoffBand chi hT hband
  have himLower : T ≤ rho.im := by
    rw [abs_of_nonneg him0] at habs
    exact habs.le
  have houter : rho ∈ zeroSupport chi 0 T' :=
    (Finset.mem_sdiff.mp hband).1
  have houterRect := mem_zeroRectangle_of_mem_zeroSupport chi 0 T' houter
  have himUpper : rho.im ≤ T + 1 := houterRect.2.2.trans hT'
  have hlocalRect : rho ∈ zeroRectangle 0 (windowHeight T) := by
    rw [zeroRectangle, Complex.mem_reProdIm]
    constructor
    · exact houterRect.1
    · unfold windowHeight
      rw [abs_of_nonneg hT]
      constructor
      · linarith
      · linarith
  have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport chi 0 T' houter
  rw [closedUnitWindowSupport, Finset.mem_filter]
  exact ⟨(MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
    chi 0 (windowHeight T) hlocalRect).2 hzero,
    ⟨himLower, himUpper⟩⟩

/-- The negative half of a unit cutoff band lies in the negative local
unit-window support based at `-T-1`. -/
theorem negativeCutoffBand_subset_closedUnitWindow
    (chi : DirichletCharacter ℂ q) {T T' : ℝ}
    (hT : 0 ≤ T) (hTT' : T ≤ T') (hT' : T' ≤ T + 1) :
    negativeCutoffBand chi T T' ⊆
      closedUnitWindowSupport chi 0 (-T - 1) := by
  intro rho hrho
  have hband : rho ∈ cutoffBandSupport chi T T' :=
    (Finset.mem_filter.mp hrho).1
  have himNeg : rho.im < 0 := (Finset.mem_filter.mp hrho).2
  have habs := lt_abs_im_of_mem_cutoffBand chi hT hband
  have himUpper : rho.im ≤ -T := by
    rw [abs_of_neg himNeg] at habs
    linarith
  have houter : rho ∈ zeroSupport chi 0 T' :=
    (Finset.mem_sdiff.mp hband).1
  have houterRect := mem_zeroRectangle_of_mem_zeroSupport chi 0 T' houter
  have himLower : -T - 1 ≤ rho.im := by linarith [houterRect.2.1, hT']
  have hlocalRect : rho ∈ zeroRectangle 0 (windowHeight (-T - 1)) := by
    rw [zeroRectangle, Complex.mem_reProdIm]
    constructor
    · exact houterRect.1
    · unfold windowHeight
      constructor
      · have : -|-T - 1| ≤ -T - 1 := neg_abs_le (-T - 1)
        linarith
      · have : -T - 1 ≤ |-T - 1| := le_abs_self (-T - 1)
        linarith
  have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport chi 0 T' houter
  rw [closedUnitWindowSupport, Finset.mem_filter]
  exact ⟨(MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
    chi 0 (windowHeight (-T - 1)) hlocalRect).2 hzero,
    ⟨himLower, by linarith⟩⟩

private theorem positiveCutoffBand_multiplicity_eq_local
    (chi : DirichletCharacter ℂ q) {T T' : ℝ}
    (hT : 0 ≤ T) (hTT' : T ≤ T') (hT' : T' ≤ T + 1)
    {rho : ℂ} (hrho : rho ∈ positiveCutoffBand chi T T') :
    zeroMultiplicity chi 0 T' rho =
      zeroMultiplicity chi 0 (windowHeight T) rho := by
  have houter : rho ∈ zeroSupport chi 0 T' :=
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hrho).1).1
  exact zeroMultiplicity_eq_of_mem_rectangles chi
    (mem_zeroRectangle_of_mem_zeroSupport chi 0 T' houter)
    (closedUnitWindowSupport_mem_rectangle chi
      (positiveCutoffBand_subset_closedUnitWindow chi hT hTT' hT' hrho))

private theorem negativeCutoffBand_multiplicity_eq_local
    (chi : DirichletCharacter ℂ q) {T T' : ℝ}
    (hT : 0 ≤ T) (hTT' : T ≤ T') (hT' : T' ≤ T + 1)
    {rho : ℂ} (hrho : rho ∈ negativeCutoffBand chi T T') :
    zeroMultiplicity chi 0 T' rho =
      zeroMultiplicity chi 0 (windowHeight (-T - 1)) rho := by
  have houter : rho ∈ zeroSupport chi 0 T' :=
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hrho).1).1
  exact zeroMultiplicity_eq_of_mem_rectangles chi
    (mem_zeroRectangle_of_mem_zeroSupport chi 0 T' houter)
    (closedUnitWindowSupport_mem_rectangle chi
      (negativeCutoffBand_subset_closedUnitWindow chi hT hTT' hT' hrho))

/-- Lemma 11.4(a) interface: a unit displacement of the cutoff costs at
most the two full-strip closed unit-window counts. -/
theorem cutoffBandMultiplicity_le_twoLocalCounts
    (chi : DirichletCharacter ℂ q) {T T' : ℝ}
    (hT : 0 ≤ T) (hTT' : T ≤ T') (hT' : T' ≤ T + 1) :
    (∑ rho ∈ cutoffBandSupport chi T T',
        zeroMultiplicity chi 0 T' rho) ≤
      closedUnitWindowCount chi 0 T +
        closedUnitWindowCount chi 0 (-T - 1) := by
  classical
  have hpartition :
      positiveCutoffBand chi T T' ∪ negativeCutoffBand chi T T' =
        cutoffBandSupport chi T T' := by
    ext rho
    simp only [positiveCutoffBand, negativeCutoffBand, Finset.mem_union,
      Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      by_cases hi : 0 ≤ rho.im
      · exact Or.inl ⟨h, hi⟩
      · exact Or.inr ⟨h, lt_of_not_ge hi⟩
  have hdisjoint : Disjoint (positiveCutoffBand chi T T')
      (negativeCutoffBand chi T T') := by
    rw [Finset.disjoint_left]
    intro rho hp hn
    exact (not_lt_of_ge (Finset.mem_filter.mp hp).2)
      (Finset.mem_filter.mp hn).2
  rw [← hpartition, Finset.sum_union hdisjoint]
  apply add_le_add
  · unfold closedUnitWindowCount
    calc
      (∑ rho ∈ positiveCutoffBand chi T T',
          zeroMultiplicity chi 0 T' rho) =
        ∑ rho ∈ positiveCutoffBand chi T T',
          zeroMultiplicity chi 0 (windowHeight T) rho := by
            apply Finset.sum_congr rfl
            intro rho hrho
            exact positiveCutoffBand_multiplicity_eq_local
              chi hT hTT' hT' hrho
      _ ≤ ∑ rho ∈ closedUnitWindowSupport chi 0 T,
          zeroMultiplicity chi 0 (windowHeight T) rho :=
        Finset.sum_le_sum_of_subset
          (positiveCutoffBand_subset_closedUnitWindow chi hT hTT' hT')
  · unfold closedUnitWindowCount
    calc
      (∑ rho ∈ negativeCutoffBand chi T T',
          zeroMultiplicity chi 0 T' rho) =
        ∑ rho ∈ negativeCutoffBand chi T T',
          zeroMultiplicity chi 0 (windowHeight (-T - 1)) rho := by
            apply Finset.sum_congr rfl
            intro rho hrho
            exact negativeCutoffBand_multiplicity_eq_local
              chi hT hTT' hT' hrho
      _ ≤ ∑ rho ∈ closedUnitWindowSupport chi 0 (-T - 1),
          zeroMultiplicity chi 0 (windowHeight (-T - 1)) rho :=
        Finset.sum_le_sum_of_subset
          (negativeCutoffBand_subset_closedUnitWindow chi hT hTT' hT')

/-- For a primitive nonprincipal character, the unit cutoff-band mass is
bounded by the two literal full-strip Lemma 11.4(a) logarithmic scales. -/
theorem cutoffBandMultiplicity_nonprincipal_le_logScales
    (chi : DirichletCharacter ℂ q) (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {T T' : ℝ} (hT : 0 ≤ T) (hTT' : T ≤ T') (hT' : T' ≤ T + 1) :
    (∑ rho ∈ cutoffBandSupport chi T T',
        (zeroMultiplicity chi 0 T' rho : ℝ)) ≤
      2 + 306 * Real.log (arithmeticScale q T) +
        306 * Real.log (arithmeticScale q (-T - 1)) := by
  have hband := cutoffBandMultiplicity_le_twoLocalCounts
    chi hT hTT' hT'
  have hcast :
      (∑ rho ∈ cutoffBandSupport chi T T',
          (zeroMultiplicity chi 0 T' rho : ℝ)) ≤
        (closedUnitWindowCount chi 0 T : ℝ) +
          (closedUnitWindowCount chi 0 (-T - 1) : ℝ) := by
    exact_mod_cast hband
  have hpos := MAPFullStripA5Family.certifiedFullStripClosedLocalZeroCount
    chi hprim hchi T
  have hneg := MAPFullStripA5Family.certifiedFullStripClosedLocalZeroCount
    chi hprim hchi (-T - 1)
  have hreflect : -(-T - 1) - 1 = T := by ring
  rw [hreflect] at hneg
  exact hcast.trans (by linarith)

/-- Conductor-one principal specialization of the unit cutoff-band mass. -/
theorem cutoffBandMultiplicity_principal_le_logScales
    {T T' : ℝ} (hT : 0 ≤ T) (hTT' : T ≤ T') (hT' : T' ≤ T + 1) :
    (∑ rho ∈ cutoffBandSupport
        (1 : DirichletCharacter ℂ 1) T T',
        (zeroMultiplicity (1 : DirichletCharacter ℂ 1) 0 T' rho : ℝ)) ≤
      1683 * Real.log (arithmeticScale 1 T) +
        1683 * Real.log (arithmeticScale 1 (-T - 1)) := by
  have hband := cutoffBandMultiplicity_le_twoLocalCounts
    (1 : DirichletCharacter ℂ 1) hT hTT' hT'
  have hcast :
      (∑ rho ∈ cutoffBandSupport
          (1 : DirichletCharacter ℂ 1) T T',
          (zeroMultiplicity (1 : DirichletCharacter ℂ 1) 0 T' rho : ℝ)) ≤
        (closedUnitWindowCount (1 : DirichletCharacter ℂ 1) 0 T : ℝ) +
          (closedUnitWindowCount (1 : DirichletCharacter ℂ 1) 0 (-T - 1) : ℝ) := by
    exact_mod_cast hband
  exact hcast.trans (add_le_add
    (MAPPrincipalZetaFullStrip.principal_fullStrip_count_le_log T)
    (MAPPrincipalZetaFullStrip.principal_fullStrip_count_le_log (-T - 1)))

private theorem one_le_two_mul_log_target
    {q : ℕ} [NeZero q] {t : ℝ} (ht : 1 ≤ t) :
    (1 : ℝ) ≤ 2 * Real.log (t * q + 2) := by
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have htarget : (2 : ℝ) ≤ t * q + 2 := by
    nlinarith [mul_nonneg (show 0 ≤ t by linarith) (show (0 : ℝ) ≤ q by positivity)]
  have hlogmono := Real.log_le_log (by norm_num : (0 : ℝ) < 2) htarget
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  linarith

/-- Both local arithmetic scales in a unit cutoff displacement are bounded by
twice the final Theorem 11.3 logarithm. -/
theorem log_arithmeticScale_cutoff_le_two_log_target
    {q : ℕ} [NeZero q] {T t : ℝ} (hT : 2 ≤ T) (hTt : T ≤ t) :
    Real.log (arithmeticScale q T) ≤ 2 * Real.log (t * q + 2) := by
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have ht : 2 ≤ t := hT.trans hTt
  have hscalePos : 0 < arithmeticScale q T := by
    unfold arithmeticScale
    positivity
  let y : ℝ := t * q
  have hy : 2 ≤ y := by
    dsimp [y]
    have := mul_le_mul_of_nonneg_left hq (by linarith : 0 ≤ t)
    nlinarith
  have hqy : (q : ℝ) ≤ y := by
    dsimp [y]
    have := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ t by linarith) (show (0 : ℝ) ≤ q by positivity)
    simpa [mul_comm] using this
  have hscale : arithmeticScale q T ≤ (t * q + 2) ^ 2 := by
    unfold arithmeticScale
    rw [abs_of_nonneg (by linarith : 0 ≤ T)]
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hleft : (q : ℝ) * (T + 2) ≤ q * (t + 2) := by
      exact mul_le_mul_of_nonneg_left (by linarith) hq0
    calc
      (q : ℝ) * (T + 2) ≤ q * (t + 2) := hleft
      _ ≤ (t * q + 2) ^ 2 := by
        dsimp [y] at hy hqy
        nlinarith
  have hlog := Real.log_le_log hscalePos hscale
  rw [Real.log_pow] at hlog
  norm_num at hlog ⊢
  exact hlog

theorem log_arithmeticScale_reflectedCutoff_le_two_log_target
    {q : ℕ} [NeZero q] {T t : ℝ} (hT : 2 ≤ T) (hTt : T ≤ t) :
    Real.log (arithmeticScale q (-T - 1)) ≤
      2 * Real.log (t * q + 2) := by
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have ht : 2 ≤ t := hT.trans hTt
  have hscalePos : 0 < arithmeticScale q (-T - 1) := by
    unfold arithmeticScale
    positivity
  let y : ℝ := t * q
  have hy : 2 ≤ y := by
    dsimp [y]
    have := mul_le_mul_of_nonneg_left hq (by linarith : 0 ≤ t)
    nlinarith
  have hqy : (q : ℝ) ≤ y := by
    dsimp [y]
    have := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ t by linarith) (show (0 : ℝ) ≤ q by positivity)
    simpa [mul_comm] using this
  have hscale : arithmeticScale q (-T - 1) ≤ (t * q + 2) ^ 2 := by
    unfold arithmeticScale
    rw [show |-T - 1| = T + 1 by
      rw [abs_of_nonpos] <;> linarith]
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hleft : (q : ℝ) * (T + 3) ≤ q * (t + 3) := by
      exact mul_le_mul_of_nonneg_left (by linarith) hq0
    change (q : ℝ) * (T + 1 + 2) ≤ _
    calc
      (q : ℝ) * (T + 1 + 2) = q * (T + 3) := by ring
      _ ≤ q * (t + 3) := hleft
      _ ≤ (t * q + 2) ^ 2 := by
        dsimp [y] at hy hqy
        nlinarith
  have hlog := Real.log_le_log hscalePos hscale
  rw [Real.log_pow] at hlog
  norm_num at hlog ⊢
  exact hlog

/-- Exact nonprincipal cutoff-transport estimate before the harmless logarithmic
simplification in Theorem 11.3. -/
theorem norm_endpointZeroTerm_cutoffDifference_nonprincipal_le
    (chi : DirichletCharacter ℂ q) (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {T T' t : ℝ} (hT : 0 < T) (hTT' : T ≤ T')
    (hT' : T' ≤ T + 1) (ht : 1 ≤ t) :
    ‖endpointMultiplicityWeightedZeroTerm chi 0 T' t -
        endpointMultiplicityWeightedZeroTerm chi 0 T t‖ ≤
      (2 * t / T) *
        (2 + 306 * Real.log (arithmeticScale q T) +
          306 * Real.log (arithmeticScale q (-T - 1))) := by
  exact (norm_endpointZeroTerm_cutoffDifference_le_bandMass
    chi hT hTT' ht).trans (mul_le_mul_of_nonneg_left
      (cutoffBandMultiplicity_nonprincipal_le_logScales
        chi hprim hchi hT.le hTT' hT') (by positivity))

/-- Exact conductor-one cutoff-transport estimate before logarithmic
simplification. -/
theorem norm_endpointZeroTerm_cutoffDifference_principal_le
    {T T' t : ℝ} (hT : 0 < T) (hTT' : T ≤ T')
    (hT' : T' ≤ T + 1) (ht : 1 ≤ t) :
    ‖endpointMultiplicityWeightedZeroTerm
          (1 : DirichletCharacter ℂ 1) 0 T' t -
        endpointMultiplicityWeightedZeroTerm
          (1 : DirichletCharacter ℂ 1) 0 T t‖ ≤
      (2 * t / T) *
        (1683 * Real.log (arithmeticScale 1 T) +
          1683 * Real.log (arithmeticScale 1 (-T - 1))) := by
  exact (norm_endpointZeroTerm_cutoffDifference_le_bandMass
    (1 : DirichletCharacter ℂ 1) hT hTT' ht).trans
      (mul_le_mul_of_nonneg_left
        (cutoffBandMultiplicity_principal_le_logScales
          hT.le hTT' hT') (by positivity))

/-- Source-form nonprincipal cutoff correction: the unit good-height shift is
absorbed by one final logarithm. -/
theorem norm_endpointZeroTerm_cutoffDifference_nonprincipal_le_source
    (chi : DirichletCharacter ℂ q) (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {T T' t : ℝ} (hT : 2 ≤ T) (hTT' : T ≤ T')
    (hT' : T' ≤ T + 1) (hTt : T ≤ t) :
    ‖endpointMultiplicityWeightedZeroTerm chi 0 T' t -
        endpointMultiplicityWeightedZeroTerm chi 0 T t‖ ≤
      2456 * t * Real.log (t * q + 2) / T := by
  have hraw := norm_endpointZeroTerm_cutoffDifference_nonprincipal_le
    chi hprim hchi (show 0 < T by linarith) hTT' hT'
      (show 1 ≤ t by linarith)
  have hlog1 := log_arithmeticScale_cutoff_le_two_log_target
    (q := q) hT hTt
  have hlog2 := log_arithmeticScale_reflectedCutoff_le_two_log_target
    (q := q) hT hTt
  have hone := one_le_two_mul_log_target (q := q)
    (show 1 ≤ t by linarith)
  have hmass :
      2 + 306 * Real.log (arithmeticScale q T) +
          306 * Real.log (arithmeticScale q (-T - 1)) ≤
        1228 * Real.log (t * q + 2) := by
    nlinarith
  calc
    _ ≤ (2 * t / T) *
        (2 + 306 * Real.log (arithmeticScale q T) +
          306 * Real.log (arithmeticScale q (-T - 1))) := hraw
    _ ≤ (2 * t / T) * (1228 * Real.log (t * q + 2)) := by
      exact mul_le_mul_of_nonneg_left hmass
        (div_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
    _ = 2456 * t * Real.log (t * q + 2) / T := by ring

/-- Source-form conductor-one cutoff correction. -/
theorem norm_endpointZeroTerm_cutoffDifference_principal_le_source
    {T T' t : ℝ} (hT : 2 ≤ T) (hTT' : T ≤ T')
    (hT' : T' ≤ T + 1) (hTt : T ≤ t) :
    ‖endpointMultiplicityWeightedZeroTerm
          (1 : DirichletCharacter ℂ 1) 0 T' t -
        endpointMultiplicityWeightedZeroTerm
          (1 : DirichletCharacter ℂ 1) 0 T t‖ ≤
      13464 * t * Real.log (t + 2) / T := by
  have hraw := norm_endpointZeroTerm_cutoffDifference_principal_le
    (show 0 < T by linarith) hTT' hT' (show 1 ≤ t by linarith)
  have hlog1 := log_arithmeticScale_cutoff_le_two_log_target
    (q := 1) hT hTt
  have hlog2 := log_arithmeticScale_reflectedCutoff_le_two_log_target
    (q := 1) hT hTt
  norm_num only [Nat.cast_one, mul_one] at hlog1 hlog2
  have hmass :
      1683 * Real.log (arithmeticScale 1 T) +
          1683 * Real.log (arithmeticScale 1 (-T - 1)) ≤
        6732 * Real.log (t + 2) := by
    linarith
  calc
    _ ≤ (2 * t / T) *
        (1683 * Real.log (arithmeticScale 1 T) +
          1683 * Real.log (arithmeticScale 1 (-T - 1))) := hraw
    _ ≤ (2 * t / T) * (6732 * Real.log (t + 2)) := by
      exact mul_le_mul_of_nonneg_left hmass
        (div_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
    _ = 13464 * t * Real.log (t + 2) / T := by ring

/-- Pure algebraic transport of an endpoint explicit-formula residual from a
nearby good height back to the requested cutoff. -/
theorem norm_residual_at_cutoff_le_goodHeight_add_band
    (chi : DirichletCharacter ℂ q) {T T' t : ℝ} (A P : ℂ) :
    ‖A - (P - endpointMultiplicityWeightedZeroTerm chi 0 T t)‖ ≤
      ‖A - (P - endpointMultiplicityWeightedZeroTerm chi 0 T' t)‖ +
      ‖endpointMultiplicityWeightedZeroTerm chi 0 T' t -
        endpointMultiplicityWeightedZeroTerm chi 0 T t‖ := by
  have hid :
      A - (P - endpointMultiplicityWeightedZeroTerm chi 0 T t) =
        (A - (P - endpointMultiplicityWeightedZeroTerm chi 0 T' t)) +
          (endpointMultiplicityWeightedZeroTerm chi 0 T t -
            endpointMultiplicityWeightedZeroTerm chi 0 T' t) := by ring
  rw [hid]
  simpa only [norm_sub_rev] using norm_add_le
    (A - (P - endpointMultiplicityWeightedZeroTerm chi 0 T' t))
    (endpointMultiplicityWeightedZeroTerm chi 0 T t -
      endpointMultiplicityWeightedZeroTerm chi 0 T' t)

/-- Koukoulopoulos' requested-cutoff transport for a primitive nonprincipal
character, retaining a caller-supplied good-height error. -/
theorem norm_residual_at_requestedCutoff_nonprincipal_le
    (chi : DirichletCharacter ℂ q) (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {T T' t E : ℝ} (hT : 2 ≤ T) (hTT' : T ≤ T')
    (hT' : T' ≤ T + 1) (hTt : T ≤ t) (hE : 0 ≤ E)
    {A P : ℂ}
    (hgood : ‖A - (P - endpointMultiplicityWeightedZeroTerm chi 0 T' t)‖ ≤ E) :
    ‖A - (P - endpointMultiplicityWeightedZeroTerm chi 0 T t)‖ ≤
      E + 2456 * t * Real.log (t * q + 2) / T := by
  exact (norm_residual_at_cutoff_le_goodHeight_add_band chi A P).trans
    (add_le_add hgood
      (norm_endpointZeroTerm_cutoffDifference_nonprincipal_le_source
        chi hprim hchi hT hTT' hT' hTt))

/-- Principal conductor-one requested-cutoff transport. -/
theorem norm_residual_at_requestedCutoff_principal_le
    {T T' t E : ℝ} (hT : 2 ≤ T) (hTT' : T ≤ T')
    (hT' : T' ≤ T + 1) (hTt : T ≤ t) (hE : 0 ≤ E)
    {A P : ℂ}
    (hgood : ‖A - (P - endpointMultiplicityWeightedZeroTerm
        (1 : DirichletCharacter ℂ 1) 0 T' t)‖ ≤ E) :
    ‖A - (P - endpointMultiplicityWeightedZeroTerm
        (1 : DirichletCharacter ℂ 1) 0 T t)‖ ≤
      E + 13464 * t * Real.log (t + 2) / T := by
  exact (norm_residual_at_cutoff_le_goodHeight_add_band
    (1 : DirichletCharacter ℂ 1) A P).trans
      (add_le_add hgood
        (norm_endpointZeroTerm_cutoffDifference_principal_le_source
          hT hTT' hT' hTt))

end

end KoukTheorem113ZeroCutoffTransport

#print axioms KoukTheorem113ZeroCutoffTransport.endpointZeroTerm_sub_eq_bandSum
#print axioms KoukTheorem113ZeroCutoffTransport.norm_endpointZeroTerm_cutoffDifference_le_bandMass
