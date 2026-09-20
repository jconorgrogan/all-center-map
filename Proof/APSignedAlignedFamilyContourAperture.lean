import KoukExercise12TwoLocalHorizontalAperture
import APSignedAlignedContourSelection

/-!
# One quantitative contour aperture for the finite AP family

The pointwise Exercise 12.2 aperture chooses its height after fixing one
character.  Here the real and imaginary obstruction coordinates are united
over every ambient character with modulus at most `Q`.  A single quantitative
finite-avoidance step then chooses one common left edge and one common height.
This preserves the quantifier order needed by the signed family square.
-/

namespace MAPAPSignedAlignedFamilyContourAperture

open Set Complex DirichletZeros QuantitativeFiniteAperture MeasureTheory
open MAPKoukExercise12TwoContourAperture
open MAPKoukExercise12TwoLocalHorizontalAperture
open MAPAPSignedAlignedContourSelection
open scoped BigOperators ENNReal

noncomputable section

/-- All buffered real zero coordinates for primitive inducers in the finite
ambient family. -/
def familyExerciseBufferedRealCoordinates (Q : ℕ) (H : ℝ) : Finset ℝ :=
  (Finset.Icc 1 Q).biUnion fun q =>
    if hq0 : q = 0 then ∅ else
      letI : NeZero q := ⟨hq0⟩
      (Finset.univ : Finset (DirichletCharacter ℂ q)).biUnion fun chi =>
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        exerciseBufferedRealCoordinates chi.primitiveCharacter H

/-- All signed buffered imaginary zero coordinates for the same family. -/
def familyExerciseLocalImagCoordinates (Q : ℕ) (H : ℝ) : Finset ℝ :=
  (Finset.Icc 1 Q).biUnion fun q =>
    if hq0 : q = 0 then ∅ else
      letI : NeZero q := ⟨hq0⟩
      (Finset.univ : Finset (DirichletCharacter ℂ q)).biUnion fun chi =>
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        exerciseLocalImagCoordinates chi.primitiveCharacter H

/-- Family-wide real-coordinate clearance for the left vertical side. -/
def familyExerciseRealClearance (Q : ℕ) (H : ℝ) : ℝ :=
  (1 / 2 : ℝ) /
    (4 * ((familyExerciseBufferedRealCoordinates Q H).card + 1))

/-- Family-wide source-local ordinate clearance for both horizontal sides. -/
def familyExerciseHorizontalClearance (Q : ℕ) (H : ℝ) : ℝ :=
  1 / (4 * ((familyExerciseLocalImagCoordinates Q H).card + 1))

/-- Corner clearance when a single scalar is convenient. -/
def familyExerciseContourClearance (Q : ℕ) (H : ℝ) : ℝ :=
  min (familyExerciseRealClearance Q H)
    (familyExerciseHorizontalClearance Q H)

/-- Real-edge clearance rescaled to an arbitrarily short interval `(0,b)`.
This is the form needed to make `x^(sigma-1)` power-saving: later one may
take `b` of order `1 / log X` without paying a family-wide real-coordinate
union. -/
def exerciseScaledRealClearance
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (H b : ℝ) : ℝ :=
  b / (4 * ((exerciseBufferedRealCoordinates chi H).card + 1))

/-- The open neighborhood of the family-wide local ordinate obstruction.
Only imaginary coordinates are united across characters; real coordinates
are handled separately for each primitive inducer. -/
def familyExerciseForbiddenHeightNeighborhood (Q : ℕ) (H : ℝ) : Set ℝ :=
  ⋃ a ∈ familyExerciseLocalImagCoordinates Q H,
    Metric.ball a (familyExerciseHorizontalClearance Q H)

/-- The positive-measure set of common heights with uniform local horizontal
clearance for the whole finite AP family. -/
def familyExerciseGoodHeights (Q : ℕ) (H : ℝ) : Set ℝ :=
  Set.Ioo H (H + 1) \
    familyExerciseForbiddenHeightNeighborhood Q H

theorem familyExerciseContourClearance_pos (Q : ℕ) (H : ℝ) :
    0 < familyExerciseContourClearance Q H := by
  unfold familyExerciseContourClearance
  apply lt_min
  · unfold familyExerciseRealClearance
    positivity
  · unfold familyExerciseHorizontalClearance
    positivity

theorem exerciseScaledRealClearance_pos
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (H : ℝ) {b : ℝ} (hb : 0 < b) :
    0 < exerciseScaledRealClearance chi H b := by
  unfold exerciseScaledRealClearance
  positivity

/-- One small left edge per primitive inducer, chosen before any common
height.  No union over the real coordinates of different characters is
formed, so the edge remains in the prescribed short interval `(0,b)` and the
clearance pays only the zero divisor of that primitive inducer. -/
theorem exists_familyExerciseSmallRealEdges
    (Q : ℕ) (H : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ,
      ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
        letI : NeZero q :=
          ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        sigma q chi ∈ Set.Ioo (0 : ℝ) b ∧
        exerciseScaledRealClearance chi.primitiveCharacter H b ≤
          sigma q chi ∧
        ∀ u : ℝ,
          ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
            exerciseScaledRealClearance chi.primitiveCharacter H b ≤
              ‖((sigma q chi : ℝ) : ℂ) +
                (u : ℂ) * Complex.I - rho‖ := by
  classical
  have hsigmaExists :
      ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
        letI : NeZero q :=
          ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        ∃ sigma ∈ Set.Ioo (0 : ℝ) b,
          exerciseScaledRealClearance chi.primitiveCharacter H b ≤ sigma ∧
          ∀ u : ℝ,
            ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
              exerciseScaledRealClearance chi.primitiveCharacter H b ≤
                ‖((sigma : ℂ) + (u : ℂ) * Complex.I) - rho‖ := by
    intro q hq chi
    let hq0 : q ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
    letI : NeZero q := ⟨hq0⟩
    letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    let R := exerciseBufferedRealCoordinates chi.primitiveCharacter H
    obtain ⟨sigma, hsigma, hsigmaClear⟩ :=
      exists_mem_Ioo_with_finset_clearance R
        (a := 0) (b := b) hb
    have hzeroR : (0 : ℝ) ∈ R := by
      simp [R, exerciseBufferedRealCoordinates]
    have hsigmaRaw := hsigmaClear 0 hzeroR
    have hdSigma :
        exerciseScaledRealClearance chi.primitiveCharacter H b ≤ sigma := by
      unfold exerciseScaledRealClearance
      dsimp only [R] at hsigmaRaw
      simpa only [sub_zero, abs_of_pos hsigma.1] using hsigmaRaw
    refine ⟨sigma, hsigma, hdSigma, ?_⟩
    intro u rho hrho
    have hrhoR : rho.re ∈ R := by
      simp only [R, exerciseBufferedRealCoordinates, Finset.mem_insert]
      right
      apply Finset.mem_image.mpr
      exact ⟨rho, by convert hrho using 1 <;> ring, rfl⟩
    have hcoord := hsigmaClear rho.re hrhoR
    have hcoord' :
        exerciseScaledRealClearance chi.primitiveCharacter H b ≤
          |sigma - rho.re| := by
      unfold exerciseScaledRealClearance
      simpa only [R, sub_zero] using hcoord
    exact hcoord'.trans (by
      simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
        Complex.ofReal_im, zero_mul, sub_zero, add_zero] using
          Complex.abs_re_le_norm
            (((sigma : ℂ) + (u : ℂ) * Complex.I) - rho))
  choose sigma hsigmaMem hdSigma hleft using hsigmaExists
  let sigmaTotal : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ :=
    fun q chi =>
      if hq : q ∈ Finset.Icc 1 Q then sigma q hq chi else b / 2
  refine ⟨sigmaTotal, ?_⟩
  intro q hq chi
  have hsigmaEq : sigmaTotal q chi = sigma q hq chi := by
    simp only [sigmaTotal, dif_pos hq]
  exact ⟨by simpa only [hsigmaEq] using hsigmaMem q hq chi,
    by simpa only [hsigmaEq] using hdSigma q hq chi,
    by
      intro u rho hrho
      simpa only [hsigmaEq] using hleft q hq chi u rho hrho⟩
theorem measurableSet_familyExerciseForbiddenHeightNeighborhood
    (Q : ℕ) (H : ℝ) :
    MeasurableSet (familyExerciseForbiddenHeightNeighborhood Q H) := by
  unfold familyExerciseForbiddenHeightNeighborhood
  exact MeasurableSet.biUnion
    (familyExerciseLocalImagCoordinates Q H).countable_toSet
    (fun _a _ha => measurableSet_ball)

theorem measurableSet_familyExerciseGoodHeights (Q : ℕ) (H : ℝ) :
    MeasurableSet (familyExerciseGoodHeights Q H) := by
  exact measurableSet_Ioo.diff
    (measurableSet_familyExerciseForbiddenHeightNeighborhood Q H)

/-- The removed local-ordinate neighborhood occupies at most half of the unit
height interval.  This is the quantitative reserve needed by the normalized
height average. -/
theorem volume_familyExerciseForbiddenHeightNeighborhood_le_half
    (Q : ℕ) (H : ℝ) :
    volume (familyExerciseForbiddenHeightNeighborhood Q H) ≤
      ENNReal.ofReal (1 / 2 : ℝ) := by
  let A := familyExerciseLocalImagCoordinates Q H
  let d := familyExerciseHorizontalClearance Q H
  have hd0 : 0 ≤ d := by
    dsimp only [d]
    exact (by
      unfold familyExerciseHorizontalClearance
      positivity)
  calc
    volume (familyExerciseForbiddenHeightNeighborhood Q H) ≤
        ∑ a ∈ A, volume (Metric.ball a d) := by
      exact measure_biUnion_finset_le A (fun a => Metric.ball a d)
    _ = ENNReal.ofReal (2 * d) * A.card := by
      simp_rw [Real.volume_ball]
      rw [Finset.sum_const]
      simp [nsmul_eq_mul, mul_comm]
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hd0)]
      apply ENNReal.ofReal_mono
      dsimp only [d, familyExerciseHorizontalClearance, A]
      have hcard : (0 : ℝ) ≤
          ((familyExerciseLocalImagCoordinates Q H).card : ℝ) := by
        positivity
      have hden : 0 < 4 *
          (((familyExerciseLocalImagCoordinates Q H).card : ℝ) + 1) := by
        positivity
      rw [show 2 *
          (1 / (4 *
            (((familyExerciseLocalImagCoordinates Q H).card : ℝ) + 1))) *
            ((familyExerciseLocalImagCoordinates Q H).card : ℝ) =
          (2 * ((familyExerciseLocalImagCoordinates Q H).card : ℝ)) /
            (4 *
              (((familyExerciseLocalImagCoordinates Q H).card : ℝ) + 1)) by
        ring]
      apply (div_le_iff₀ hden).2
      nlinarith

theorem half_le_volume_familyExerciseGoodHeights
    (Q : ℕ) (H : ℝ) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤
      volume (familyExerciseGoodHeights Q H) := by
  let U := familyExerciseForbiddenHeightNeighborhood Q H
  have hU := volume_familyExerciseForbiddenHeightNeighborhood_le_half Q H
  have hUTop : volume U ≠ ⊤ := by
    exact ne_of_lt (hU.trans_lt ENNReal.ofReal_lt_top)
  have hadd : ENNReal.ofReal (1 / 2 : ℝ) + volume U ≤
      volume (Set.Ioo H (H + 1)) := by
    rw [Real.volume_Ioo]
    have hinterval : H + 1 - H = (1 : ℝ) := by ring
    rw [hinterval]
    calc
      ENNReal.ofReal (1 / 2 : ℝ) + volume U ≤
          ENNReal.ofReal (1 / 2 : ℝ) +
            ENNReal.ofReal (1 / 2 : ℝ) := add_le_add_right hU _
      _ = ENNReal.ofReal 1 := by
        rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)] <;>
          norm_num
  have hsub : ENNReal.ofReal (1 / 2 : ℝ) ≤
      volume (Set.Ioo H (H + 1)) - volume U :=
    ENNReal.le_sub_of_add_le_right hUTop hadd
  exact hsub.trans (by
    simpa only [familyExerciseGoodHeights, U] using
      (MeasureTheory.le_measure_diff
        (μ := volume)
        (s₁ := Set.Ioo H (H + 1))
        (s₂ := familyExerciseForbiddenHeightNeighborhood Q H)))

theorem familyExerciseGoodHeights_subset_Ioo (Q : ℕ) (H : ℝ) :
    familyExerciseGoodHeights Q H ⊆ Set.Ioo H (H + 1) :=
  Set.diff_subset

/-- Every good common height has the uniform family-wide local ordinate
clearance. -/
theorem familyExerciseHorizontalClearance_le_abs_sub
    (Q : ℕ) (H : ℝ) {T a : ℝ}
    (hT : T ∈ familyExerciseGoodHeights Q H)
    (ha : a ∈ familyExerciseLocalImagCoordinates Q H) :
    familyExerciseHorizontalClearance Q H ≤ |T - a| := by
  have hnot : T ∉ Metric.ball a (familyExerciseHorizontalClearance Q H) := by
    intro hball
    exact hT.2 (by
      unfold familyExerciseForbiddenHeightNeighborhood
      simp only [Set.mem_iUnion]
      exact ⟨a, ⟨ha, hball⟩⟩)
  rw [Metric.mem_ball, Real.dist_eq] at hnot
  exact not_lt.mp hnot

/-- Every primitive-inducer real obstruction belongs to the family union. -/
theorem mem_familyRealCoordinates
    (Q : ℕ) (H : ℝ) (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
    (chi : DirichletCharacter ℂ q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
    letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    ∀ r ∈ exerciseBufferedRealCoordinates chi.primitiveCharacter H,
      r ∈ familyExerciseBufferedRealCoordinates Q H := by
  classical
  let hq0 : q ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
  letI : NeZero q := ⟨hq0⟩
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  intro r hr
  unfold familyExerciseBufferedRealCoordinates
  apply Finset.mem_biUnion.mpr
  refine ⟨q, hq, ?_⟩
  simp only [dif_neg hq0]
  apply Finset.mem_biUnion.mpr
  exact ⟨chi, Finset.mem_univ _, hr⟩

/-- Every primitive-inducer imaginary obstruction belongs to the family union. -/
theorem mem_familyImagCoordinates
    (Q : ℕ) (H : ℝ) (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
    (chi : DirichletCharacter ℂ q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
    letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    ∀ a ∈ exerciseLocalImagCoordinates chi.primitiveCharacter H,
      a ∈ familyExerciseLocalImagCoordinates Q H := by
  classical
  let hq0 : q ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
  letI : NeZero q := ⟨hq0⟩
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  intro a ha
  unfold familyExerciseLocalImagCoordinates
  apply Finset.mem_biUnion.mpr
  refine ⟨q, hq, ?_⟩
  simp only [dif_neg hq0]
  apply Finset.mem_biUnion.mpr
  exact ⟨chi, Finset.mem_univ _, ha⟩

/-- One common quantitative aperture for every primitive inducer in the
finite AP family.  The chosen `sigma` is even common across characters (the
live endpoint only requires a character-dependent family), and `T` is common
as required. -/
theorem exists_familyExerciseContourAperture
    (Q : ℕ) (hQ : 1 ≤ Q) (H c : ℝ) :
    ∃ sigma ∈ Set.Ioo (0 : ℝ) (1 / 2),
      ∃ T ∈ Set.Ioo H (H + 1),
        familyExerciseRealClearance Q H ≤ sigma ∧
        ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
          (chi : DirichletCharacter ℂ q),
          letI : NeZero q :=
            ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
          letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
          (∀ u ∈ Set.Icc (-T) T,
            ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
              familyExerciseRealClearance Q H ≤
                ‖((sigma : ℂ) + (u : ℂ) * Complex.I) - rho‖) ∧
          (∀ r ∈ Set.Icc sigma c,
            ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
              familyExerciseHorizontalClearance Q H ≤
                ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho‖) ∧
          (∀ r ∈ Set.Icc sigma c,
            ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
              familyExerciseHorizontalClearance Q H ≤
                ‖((r : ℂ) + (T : ℂ) * Complex.I) - rho‖) := by
  classical
  let R := familyExerciseBufferedRealCoordinates Q H
  let A := familyExerciseLocalImagCoordinates Q H
  let dR := familyExerciseRealClearance Q H
  let dH := familyExerciseHorizontalClearance Q H
  obtain ⟨sigma, hsigma, hsigmaClear⟩ :=
    exists_mem_Ioo_with_finset_clearance R
      (a := 0) (b := 1 / 2) (by norm_num)
  obtain ⟨T, hT, hTClear⟩ :=
    exists_mem_Ioo_with_finset_clearance A
      (a := H) (b := H + 1) (by linarith)
  have hqOne : 1 ∈ Finset.Icc 1 Q := Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩
  let chiOne : DirichletCharacter ℂ 1 := 1
  letI : NeZero (1 : ℕ) := ⟨by norm_num⟩
  letI : NeZero chiOne.conductor := ⟨chiOne.conductor_ne_zero⟩
  have hzeroR : (0 : ℝ) ∈ R := by
    dsimp only [R]
    apply mem_familyRealCoordinates Q H 1 hqOne chiOne
    simp [exerciseBufferedRealCoordinates]
  have hsigmaRaw := hsigmaClear 0 hzeroR
  have hsigmaBase :
      (1 / 2 : ℝ) / (4 * (R.card + 1)) ≤ sigma := by
    norm_num [abs_of_pos hsigma.1] at hsigmaRaw
    exact hsigmaRaw
  have hdSigma : dR ≤ sigma := by
    simpa only [dR, familyExerciseRealClearance, R] using hsigmaBase
  refine ⟨sigma, hsigma, T, hT, hdSigma, ?_⟩
  intro q hq chi
  let hq0 : q ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
  letI : NeZero q := ⟨hq0⟩
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hleft : ∀ u ∈ Set.Icc (-T) T,
      ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
        dR ≤ ‖((sigma : ℂ) + (u : ℂ) * Complex.I) - rho‖ := by
    intro u hu rho hrho
    have hrhoR : rho.re ∈ R := by
      apply mem_familyRealCoordinates Q H q hq chi
      simp only [exerciseBufferedRealCoordinates, Finset.mem_insert]
      right
      apply Finset.mem_image.mpr
      exact ⟨rho, by convert hrho using 1 <;> ring, rfl⟩
    have hcoord := hsigmaClear rho.re hrhoR
    have hcoord' : (1 / 2 : ℝ) / (4 * (R.card + 1)) ≤
        |sigma - rho.re| := by simpa only [sub_zero] using hcoord
    exact (show dR ≤ |sigma - rho.re| by
      simpa only [dR, familyExerciseRealClearance, R] using hcoord').trans (by
        simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
          Complex.ofReal_im, zero_mul, sub_zero, add_zero] using
            Complex.abs_re_le_norm
              (((sigma : ℂ) + (u : ℂ) * Complex.I) - rho))
  have hdHleOne : dH ≤ 1 := by
    have hcard : (0 : ℝ) ≤ (A.card : ℝ) := by positivity
    have hden : (4 : ℝ) ≤ 4 * ((A.card : ℝ) + 1) := by nlinarith
    dsimp only [dH, familyExerciseHorizontalClearance]
    have hfrac : 1 / (4 * ((A.card : ℝ) + 1)) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) hden
    exact hfrac.trans (by norm_num)
  have hbottom : ∀ r ∈ Set.Icc sigma c,
      ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
        dH ≤ ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho‖ := by
    intro r hr rho hrho
    by_cases hrange : -rho.im ∈ Set.Icc (H - 1) (H + 2)
    · have hrhoA : -rho.im ∈ A := by
        apply mem_familyImagCoordinates Q H q hq chi
        exact mem_exerciseLocalImagCoordinates_of_mem_global_bottom
          chi.primitiveCharacter hrho hrange
      have hcoord := hTClear (-rho.im) hrhoA
      have hdist : dH ≤ |(-T) - rho.im| := by
        calc
          dH ≤ |T - (-rho.im)| := by
            simpa only [dH, familyExerciseHorizontalClearance, A,
              add_sub_cancel_left] using hcoord
          _ = _ := by
            rw [show (-T) - rho.im = -(T - (-rho.im)) by ring, abs_neg]
      exact hdist.trans (by
        simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          mul_one, zero_mul, add_zero, zero_add] using
            Complex.abs_im_le_norm
              (((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho))
    · have hfar : 1 ≤ |T - (-rho.im)| := by
        rw [Set.mem_Icc, not_and_or] at hrange
        rcases hrange with hlo | hhi
        · rw [abs_of_nonneg (by linarith [hT.1])]
          linarith [hT.1]
        · rw [abs_of_nonpos (by linarith [hT.2])]
          linarith [hT.2]
      have hdist : dH ≤ |(-T) - rho.im| :=
        hdHleOne.trans (hfar.trans_eq (by
          rw [show (-T) - rho.im = -(T - (-rho.im)) by ring, abs_neg]))
      exact hdist.trans (by
        simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          mul_one, zero_mul, add_zero, zero_add] using
            Complex.abs_im_le_norm
              (((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho))
  have htop : ∀ r ∈ Set.Icc sigma c,
      ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
        dH ≤ ‖((r : ℂ) + (T : ℂ) * Complex.I) - rho‖ := by
    intro r hr rho hrho
    by_cases hrange : rho.im ∈ Set.Icc (H - 1) (H + 2)
    · have hrhoA : rho.im ∈ A := by
        apply mem_familyImagCoordinates Q H q hq chi
        exact mem_exerciseLocalImagCoordinates_of_mem_global_top
          chi.primitiveCharacter hrho hrange
      have hcoord := hTClear rho.im hrhoA
      exact (show dH ≤ |T - rho.im| by
        simpa only [dH, familyExerciseHorizontalClearance, A,
          add_sub_cancel_left] using hcoord).trans (by
            simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
              Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
              mul_one, zero_mul, add_zero, zero_add] using
                Complex.abs_im_le_norm
                  (((r : ℂ) + (T : ℂ) * Complex.I) - rho))
    · have hfar : 1 ≤ |T - rho.im| := by
        rw [Set.mem_Icc, not_and_or] at hrange
        rcases hrange with hlo | hhi
        · rw [abs_of_nonneg (by linarith [hT.1])]
          linarith [hT.1]
        · rw [abs_of_nonpos (by linarith [hT.2])]
          linarith [hT.2]
      exact hdHleOne.trans (hfar.trans (by
        simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          mul_one, zero_mul, add_zero, zero_add] using
            Complex.abs_im_le_norm
              (((r : ℂ) + (T : ℂ) * Complex.I) - rho)))
  exact ⟨hleft, hbottom, htop⟩

/-- A single primitive-inducer contour with positive clearance on all three
moved sides is legal for the paper-edge explicit formula. -/
theorem paperEdgeContourLegal_of_localClearance
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor]
    {H sigma T dLeft dHorizontal : ℝ}
    (hH : 0 < H) (hsigma : sigma ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hT : T ∈ Set.Ioo H (H + 1))
    (hdLeft : 0 < dLeft) (hdHorizontal : 0 < dHorizontal)
    (hleft : ∀ u ∈ Set.Icc (-T) T,
      ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
        dLeft ≤ ‖((sigma : ℂ) + (u : ℂ) * Complex.I) - rho‖)
    (hbottom : ∀ r ∈ Set.Icc sigma 1,
      ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
        dHorizontal ≤
          ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho‖)
    (htop : ∀ r ∈ Set.Icc sigma 1,
      ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
        dHorizontal ≤ ‖((r : ℂ) + (T : ℂ) * Complex.I) - rho‖) :
    MAPAPCorrectedCommonHeightContract.paperEdgeContourLegal chi sigma T := by
  have hTpos : 0 < T := hH.trans hT.1
  refine ⟨hTpos, hsigma, ?_, ?_, ?_⟩
  · intro u hu hzero
    let z : ℂ := (sigma : ℂ) + (u : ℂ) * Complex.I
    have hzrect : z ∈ zeroRectangle 0 (H + 4) := by
      constructor
      · constructor
        · simpa [z] using hsigma.1.le
        · have hsigmaOne : sigma ≤ 1 := by linarith [hsigma.2]
          simpa [z] using hsigmaOne
      · constructor
        · have huLower : -(H + 4) ≤ u := by linarith [hu.1, hT.2]
          simpa [z] using huLower
        · have huUpper : u ≤ H + 4 := by linarith [hu.2, hT.2]
          simpa [z] using huUpper
    have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 4) :=
      (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        chi.primitiveCharacter 0 (H + 4) hzrect).2 hzero
    have hdist := hleft u hu z hzS
    have : dLeft ≤ 0 := by simpa [z] using hdist
    linarith
  · intro r hr hzero
    let z : ℂ := (r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I
    have hzrect : z ∈ zeroRectangle 0 (H + 4) := by
      constructor
      · constructor
        · have hrzero : 0 ≤ r := hsigma.1.le.trans hr.1
          simpa [z] using hrzero
        · simpa [z] using hr.2
      · constructor
        · have hnegTLower : -(H + 4) ≤ -T := by linarith [hT.2]
          simpa [z] using hnegTLower
        · have hnegTUpper : -T ≤ H + 4 := by linarith [hH, hT.1]
          simpa [z] using hnegTUpper
    have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 4) :=
      (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        chi.primitiveCharacter 0 (H + 4) hzrect).2 hzero
    have hdist := hbottom r hr z hzS
    have : dHorizontal ≤ 0 := by simpa [z] using hdist
    linarith
  · intro r hr hzero
    let z : ℂ := (r : ℂ) + (T : ℂ) * Complex.I
    have hzrect : z ∈ zeroRectangle 0 (H + 4) := by
      constructor
      · constructor
        · have hrzero : 0 ≤ r := hsigma.1.le.trans hr.1
          simpa [z] using hrzero
        · simpa [z] using hr.2
      · constructor
        · have hTLower : -(H + 4) ≤ T := by linarith [hH, hT.1]
          simpa [z] using hTLower
        · have hTUpper : T ≤ H + 4 := by linarith [hT.2]
          simpa [z] using hTUpper
    have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 4) :=
      (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        chi.primitiveCharacter 0 (H + 4) hzrect).2 hzero
    have hdist := htop r hr z hzS
    have : dHorizontal ≤ 0 := by simpa [z] using hdist
    linarith

/-- Positive family-wide clearance implies the exact nonvanishing predicate
used by the signed AP contour family.  This is the bridge from the
quantitative finite-union construction to the consumer's legal-contour
surface; no contour is reselected and the common height is unchanged. -/
theorem familyPaperEdgeLegal_of_familyExerciseClearance
    (Q : ℕ) {H sigma T : ℝ} (hH : 0 < H)
    (hsigma : sigma ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hT : T ∈ Set.Ioo H (H + 1))
    (hleft :
      ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
        letI : NeZero q :=
          ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        ∀ u ∈ Set.Icc (-T) T,
          ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
            familyExerciseRealClearance Q H ≤
              ‖((sigma : ℂ) + (u : ℂ) * Complex.I) - rho‖)
    (hbottom :
      ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
        letI : NeZero q :=
          ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        ∀ r ∈ Set.Icc sigma 1,
          ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
            familyExerciseHorizontalClearance Q H ≤
              ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho‖)
    (htop :
      ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
        letI : NeZero q :=
          ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        ∀ r ∈ Set.Icc sigma 1,
          ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
            familyExerciseHorizontalClearance Q H ≤
              ‖((r : ℂ) + (T : ℂ) * Complex.I) - rho‖) :
    familyPaperEdgeLegal Q (fun _q _chi => sigma) T := by
  intro q hq chi
  let hq0 : q ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
  letI : NeZero q := ⟨hq0⟩
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hTpos : 0 < T := hH.trans hT.1
  refine ⟨hTpos, hsigma, ?_, ?_, ?_⟩
  · intro u hu hzero
    let z : ℂ := (sigma : ℂ) + (u : ℂ) * Complex.I
    have hzrect : z ∈ zeroRectangle 0 (H + 4) := by
      constructor
      · constructor
        · simpa [z] using hsigma.1.le
        · have hsigmaOne : sigma ≤ 1 := by linarith [hsigma.2]
          simpa [z] using hsigmaOne
      · constructor
        · have huLower : -(H + 4) ≤ u := by
            linarith [hu.1, hT.2]
          simpa [z] using huLower
        · have huUpper : u ≤ H + 4 := by
            linarith [hu.2, hT.2]
          simpa [z] using huUpper
    have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 4) :=
      (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        chi.primitiveCharacter 0 (H + 4) hzrect).2 hzero
    have hdist := hleft q hq chi u hu z hzS
    have hdpos : 0 < familyExerciseRealClearance Q H := by
      unfold familyExerciseRealClearance
      positivity
    have : familyExerciseRealClearance Q H ≤ 0 := by
      simpa [z] using hdist
    linarith
  · intro r hr hzero
    let z : ℂ := (r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I
    have hzrect : z ∈ zeroRectangle 0 (H + 4) := by
      constructor
      · constructor
        · have hrzero : 0 ≤ r := hsigma.1.le.trans hr.1
          simpa [z] using hrzero
        · simpa [z] using hr.2
      · constructor
        · have hnegTLower : -(H + 4) ≤ -T := by linarith [hT.2]
          simpa [z] using hnegTLower
        · have hnegTUpper : -T ≤ H + 4 := by linarith [hH, hT.1]
          simpa [z] using hnegTUpper
    have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 4) :=
      (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        chi.primitiveCharacter 0 (H + 4) hzrect).2 hzero
    have hdist := hbottom q hq chi r hr z hzS
    have hdpos : 0 < familyExerciseHorizontalClearance Q H := by
      unfold familyExerciseHorizontalClearance
      positivity
    have : familyExerciseHorizontalClearance Q H ≤ 0 := by
      simpa [z] using hdist
    linarith
  · intro r hr hzero
    let z : ℂ := (r : ℂ) + (T : ℂ) * Complex.I
    have hzrect : z ∈ zeroRectangle 0 (H + 4) := by
      constructor
      · constructor
        · have hrzero : 0 ≤ r := hsigma.1.le.trans hr.1
          simpa [z] using hrzero
        · simpa [z] using hr.2
      · constructor
        · have hTLower : -(H + 4) ≤ T := by linarith [hH, hT.1]
          simpa [z] using hTLower
        · have hTUpper : T ≤ H + 4 := by linarith [hT.2]
          simpa [z] using hTUpper
    have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 4) :=
      (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        chi.primitiveCharacter 0 (H + 4) hzrect).2 hzero
    have hdist := htop q hq chi r hr z hzS
    have hdpos : 0 < familyExerciseHorizontalClearance Q H := by
      unfold familyExerciseHorizontalClearance
      positivity
    have : familyExerciseHorizontalClearance Q H ≤ 0 := by
      simpa [z] using hdist
    linarith

/-- One common quantitatively separated contour for the entire finite MAP AP
family, already packaged with the exact legality predicate consumed by
`AlignedLeftHorizontalFamilySquare`.  The left edge is allowed to be a family
in the consumer, but the finite-union construction supplies the stronger
constant family. -/
theorem exists_familyExerciseContourAperture_legal
    (Q : ℕ) (hQ : 1 ≤ Q) {H : ℝ} (hH : 0 < H) :
    ∃ sigma ∈ Set.Ioo (0 : ℝ) (1 / 2),
      ∃ T ∈ Set.Ioo H (H + 1),
        familyExerciseRealClearance Q H ≤ sigma ∧
        familyPaperEdgeLegal Q (fun _q _chi => sigma) T ∧
        ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
          (chi : DirichletCharacter ℂ q),
          letI : NeZero q :=
            ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
          letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
          (∀ u ∈ Set.Icc (-T) T,
            ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
              familyExerciseRealClearance Q H ≤
                ‖((sigma : ℂ) + (u : ℂ) * Complex.I) - rho‖) ∧
          (∀ r ∈ Set.Icc sigma 1,
            ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
              familyExerciseHorizontalClearance Q H ≤
                ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho‖) ∧
          (∀ r ∈ Set.Icc sigma 1,
            ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
              familyExerciseHorizontalClearance Q H ≤
                ‖((r : ℂ) + (T : ℂ) * Complex.I) - rho‖) := by
  obtain ⟨sigma, hsigma, T, hT, hdSigma, hclear⟩ :=
    exists_familyExerciseContourAperture Q hQ H 1
  have hleft :
      ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
        letI : NeZero q :=
          ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        ∀ u ∈ Set.Icc (-T) T,
          ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
            familyExerciseRealClearance Q H ≤
              ‖((sigma : ℂ) + (u : ℂ) * Complex.I) - rho‖ := by
    intro q hq chi
    exact (hclear q hq chi).1
  have hbottom :
      ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
        letI : NeZero q :=
          ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        ∀ r ∈ Set.Icc sigma 1,
          ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
            familyExerciseHorizontalClearance Q H ≤
              ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho‖ := by
    intro q hq chi
    exact (hclear q hq chi).2.1
  have htop :
      ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
        letI : NeZero q :=
          ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        ∀ r ∈ Set.Icc sigma 1,
          ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
            familyExerciseHorizontalClearance Q H ≤
              ‖((r : ℂ) + (T : ℂ) * Complex.I) - rho‖ := by
    intro q hq chi
    exact (hclear q hq chi).2.2
  have hlegal : familyPaperEdgeLegal Q (fun _q _chi => sigma) T :=
    familyPaperEdgeLegal_of_familyExerciseClearance Q hH hsigma hT
      hleft hbottom htop
  exact ⟨sigma, hsigma, T, hT, hdSigma, hlegal, hclear⟩

/-- Optimized family aperture for height averaging.  Each primitive inducer
gets its own quantitatively separated left edge, while only the source-local
imaginary coordinates are united to form one common positive-measure set of
heights.  Thus the vertical clearance pays no family-wide zero count, and the
horizontal clearance is uniform for every height in the same measurable set.
-/
theorem exists_familyExerciseGoodHeightAperture
    (Q : ℕ) {H : ℝ} (hH : 0 < H) :
    ∃ G : Set ℝ,
      ∃ sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ,
        MeasurableSet G ∧
        ENNReal.ofReal (1 / 2 : ℝ) ≤ volume G ∧
        G ⊆ Set.Ioo H (H + 1) ∧
        ∀ T ∈ G,
          familyPaperEdgeLegal Q sigma T ∧
          ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
            (chi : DirichletCharacter ℂ q),
            letI : NeZero q :=
              ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
            letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
            exerciseRealClearance chi.primitiveCharacter H ≤ sigma q chi ∧
            (∀ u ∈ Set.Icc (-T) T,
              ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
                exerciseRealClearance chi.primitiveCharacter H ≤
                  ‖((sigma q chi : ℝ) : ℂ) +
                    (u : ℂ) * Complex.I - rho‖) ∧
            (∀ r ∈ Set.Icc (sigma q chi) 1,
              ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
                familyExerciseHorizontalClearance Q H ≤
                  ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho‖) ∧
            (∀ r ∈ Set.Icc (sigma q chi) 1,
              ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
                familyExerciseHorizontalClearance Q H ≤
                  ‖((r : ℂ) + (T : ℂ) * Complex.I) - rho‖) := by
  classical
  have hsigmaExists :
      ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
        letI : NeZero q :=
          ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        ∃ sigma ∈ Set.Ioo (0 : ℝ) (1 / 2),
          exerciseRealClearance chi.primitiveCharacter H ≤ sigma ∧
          ∀ u : ℝ,
            ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
              exerciseRealClearance chi.primitiveCharacter H ≤
                ‖((sigma : ℂ) + (u : ℂ) * Complex.I) - rho‖ := by
    intro q hq chi
    let hq0 : q ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
    letI : NeZero q := ⟨hq0⟩
    letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    let R := exerciseBufferedRealCoordinates chi.primitiveCharacter H
    obtain ⟨sigma, hsigma, hsigmaClear⟩ :=
      exists_mem_Ioo_with_finset_clearance R
        (a := 0) (b := 1 / 2) (by norm_num)
    have hzeroR : (0 : ℝ) ∈ R := by
      simp [R, exerciseBufferedRealCoordinates]
    have hsigmaRaw := hsigmaClear 0 hzeroR
    have hdSigma : exerciseRealClearance chi.primitiveCharacter H ≤ sigma := by
      unfold exerciseRealClearance
      dsimp only [R] at hsigmaRaw
      norm_num [abs_of_pos hsigma.1] at hsigmaRaw
      exact hsigmaRaw
    refine ⟨sigma, hsigma, hdSigma, ?_⟩
    intro u rho hrho
    have hrhoR : rho.re ∈ R := by
      unfold R exerciseBufferedRealCoordinates
      apply Finset.mem_insert.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨rho, ?_, rfl⟩
      convert hrho using 1 <;> ring
    have hcoord := hsigmaClear rho.re hrhoR
    have hcoord' :
        exerciseRealClearance chi.primitiveCharacter H ≤
          |sigma - rho.re| := by
      unfold exerciseRealClearance
      dsimp only [R] at hcoord
      norm_num at hcoord ⊢
      exact hcoord
    exact hcoord'.trans (by
      simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
        Complex.ofReal_im, zero_mul, sub_zero, add_zero] using
          Complex.abs_re_le_norm
            (((sigma : ℂ) + (u : ℂ) * Complex.I) - rho))
  choose sigma hsigmaMem hdSigma hleft using hsigmaExists
  let sigmaTotal : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ :=
    fun q chi =>
      if hq : q ∈ Finset.Icc 1 Q then sigma q hq chi else 1 / 4
  let G := familyExerciseGoodHeights Q H
  refine ⟨G, sigmaTotal,
    measurableSet_familyExerciseGoodHeights Q H,
    half_le_volume_familyExerciseGoodHeights Q H,
    familyExerciseGoodHeights_subset_Ioo Q H, ?_⟩
  intro T hTG
  have hTIoo : T ∈ Set.Ioo H (H + 1) :=
    familyExerciseGoodHeights_subset_Ioo Q H hTG
  have hdHorizontal : 0 < familyExerciseHorizontalClearance Q H := by
    unfold familyExerciseHorizontalClearance
    positivity
  have hdHorizontalLeOne : familyExerciseHorizontalClearance Q H ≤ 1 := by
    have hcard : (0 : ℝ) ≤
        ((familyExerciseLocalImagCoordinates Q H).card : ℝ) := by
      positivity
    have hden : (4 : ℝ) ≤ 4 *
        (((familyExerciseLocalImagCoordinates Q H).card : ℝ) + 1) := by
      nlinarith
    unfold familyExerciseHorizontalClearance
    have hfrac :
        1 / (4 *
          (((familyExerciseLocalImagCoordinates Q H).card : ℝ) + 1)) ≤
          1 / 4 := one_div_le_one_div_of_le (by norm_num) hden
    exact hfrac.trans (by norm_num)
  have hdata :
      ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
        letI : NeZero q :=
          ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        exerciseRealClearance chi.primitiveCharacter H ≤
            sigmaTotal q chi ∧
        (∀ u ∈ Set.Icc (-T) T,
          ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
            exerciseRealClearance chi.primitiveCharacter H ≤
              ‖((sigmaTotal q chi : ℝ) : ℂ) +
                (u : ℂ) * Complex.I - rho‖) ∧
        (∀ r ∈ Set.Icc (sigmaTotal q chi) 1,
          ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
            familyExerciseHorizontalClearance Q H ≤
              ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho‖) ∧
        (∀ r ∈ Set.Icc (sigmaTotal q chi) 1,
          ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
            familyExerciseHorizontalClearance Q H ≤
              ‖((r : ℂ) + (T : ℂ) * Complex.I) - rho‖) := by
    intro q hq chi
    let hq0 : q ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
    letI : NeZero q := ⟨hq0⟩
    letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    have hsigmaEq : sigmaTotal q chi = sigma q hq chi := by
      simp only [sigmaTotal, dif_pos hq]
    have hbottom :
        ∀ r ∈ Set.Icc (sigmaTotal q chi) 1,
          ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
            familyExerciseHorizontalClearance Q H ≤
              ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho‖ := by
      intro r hr rho hrho
      by_cases hrange : -rho.im ∈ Set.Icc (H - 1) (H + 2)
      · have hrhoFamily : -rho.im ∈ familyExerciseLocalImagCoordinates Q H := by
          apply mem_familyImagCoordinates Q H q hq chi
          exact mem_exerciseLocalImagCoordinates_of_mem_global_bottom
            chi.primitiveCharacter hrho hrange
        have hcoord := familyExerciseHorizontalClearance_le_abs_sub
          Q H hTG hrhoFamily
        have hdist : familyExerciseHorizontalClearance Q H ≤
            |(-T) - rho.im| := by
          calc
            familyExerciseHorizontalClearance Q H ≤ |T - (-rho.im)| := hcoord
            _ = |(-T) - rho.im| := by
              rw [show (-T) - rho.im = -(T - (-rho.im)) by ring, abs_neg]
        exact hdist.trans (by
          simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
            Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
            mul_one, zero_mul, add_zero, zero_add] using
              Complex.abs_im_le_norm
                (((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho))
      · have hfar : 1 ≤ |T - (-rho.im)| := by
          rw [Set.mem_Icc, not_and_or] at hrange
          rcases hrange with hlo | hhi
          · rw [abs_of_nonneg (by linarith [hTIoo.1])]
            linarith [hTIoo.1]
          · rw [abs_of_nonpos (by linarith [hTIoo.2])]
            linarith [hTIoo.2]
        have hdist : familyExerciseHorizontalClearance Q H ≤
            |(-T) - rho.im| :=
          hdHorizontalLeOne.trans (hfar.trans_eq (by
            rw [show (-T) - rho.im = -(T - (-rho.im)) by ring, abs_neg]))
        exact hdist.trans (by
          simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
            Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
            mul_one, zero_mul, add_zero, zero_add] using
              Complex.abs_im_le_norm
                (((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho))
    have htop :
        ∀ r ∈ Set.Icc (sigmaTotal q chi) 1,
          ∀ rho ∈ zeroSupport chi.primitiveCharacter 0 (H + 4),
            familyExerciseHorizontalClearance Q H ≤
              ‖((r : ℂ) + (T : ℂ) * Complex.I) - rho‖ := by
      intro r hr rho hrho
      by_cases hrange : rho.im ∈ Set.Icc (H - 1) (H + 2)
      · have hrhoFamily : rho.im ∈ familyExerciseLocalImagCoordinates Q H := by
          apply mem_familyImagCoordinates Q H q hq chi
          exact mem_exerciseLocalImagCoordinates_of_mem_global_top
            chi.primitiveCharacter hrho hrange
        have hcoord := familyExerciseHorizontalClearance_le_abs_sub
          Q H hTG hrhoFamily
        exact hcoord.trans (by
          simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
            Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
            mul_one, zero_mul, add_zero, zero_add] using
              Complex.abs_im_le_norm
                (((r : ℂ) + (T : ℂ) * Complex.I) - rho))
      · have hfar : 1 ≤ |T - rho.im| := by
          rw [Set.mem_Icc, not_and_or] at hrange
          rcases hrange with hlo | hhi
          · rw [abs_of_nonneg (by linarith [hTIoo.1])]
            linarith [hTIoo.1]
          · rw [abs_of_nonpos (by linarith [hTIoo.2])]
            linarith [hTIoo.2]
        exact hdHorizontalLeOne.trans (hfar.trans (by
          simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
            Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
            mul_one, zero_mul, add_zero, zero_add] using
              Complex.abs_im_le_norm
                (((r : ℂ) + (T : ℂ) * Complex.I) - rho)))
    refine ⟨?_, ?_, hbottom, htop⟩
    · simpa only [hsigmaEq] using hdSigma q hq chi
    · intro u hu rho hrho
      simpa only [hsigmaEq] using
        hleft q hq chi u rho hrho
  have hlegal : familyPaperEdgeLegal Q sigmaTotal T := by
    intro q hq chi
    let hq0 : q ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
    letI : NeZero q := ⟨hq0⟩
    letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    have hqdata := hdata q hq chi
    have hsigmaIoo : sigmaTotal q chi ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
      simp only [sigmaTotal, dif_pos hq]
      exact hsigmaMem q hq chi
    exact paperEdgeContourLegal_of_localClearance chi hH hsigmaIoo hTIoo
      (exerciseRealClearance_pos chi.primitiveCharacter H)
      hdHorizontal hqdata.2.1 hqdata.2.2.1 hqdata.2.2.2
  exact ⟨hlegal, hdata⟩

/-- Consumer-shaped small-edge aperture.  The left edges lie in an arbitrary
prescribed interval `(0,b)` while a single positive-measure set of heights is
legal for the entire finite AP family.  This is the deterministic quantifier
order needed by the averaged signed contour estimate: `sigma` is fixed before
the height variable is integrated. -/
theorem exists_familyExerciseGoodHeightSmallEdgesLegal
    (Q : ℕ) {H b : ℝ} (hH : 0 < H) (hb : 0 < b)
    (hbHalf : b ≤ 1 / 2) :
    ∃ G : Set ℝ,
      ∃ sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ,
        MeasurableSet G ∧
        ENNReal.ofReal (1 / 2 : ℝ) ≤ volume G ∧
        G ⊆ Set.Ioo H (H + 1) ∧
        (∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
            (chi : DirichletCharacter ℂ q),
          sigma q chi ∈ Set.Ioo (0 : ℝ) b) ∧
        ∀ T ∈ G, familyPaperEdgeLegal Q sigma T := by
  classical
  obtain ⟨sigma, hsigma⟩ :=
    exists_familyExerciseSmallRealEdges Q H hb
  let G := familyExerciseGoodHeights Q H
  refine ⟨G, sigma,
    measurableSet_familyExerciseGoodHeights Q H,
    half_le_volume_familyExerciseGoodHeights Q H,
    familyExerciseGoodHeights_subset_Ioo Q H, ?_, ?_⟩
  · intro q hq chi
    exact (hsigma q hq chi).1
  · intro T hTG
    have hTIoo : T ∈ Set.Ioo H (H + 1) :=
      familyExerciseGoodHeights_subset_Ioo Q H hTG
    unfold familyPaperEdgeLegal
    intro q hq chi
    let hq0 : q ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
    letI : NeZero q := ⟨hq0⟩
    letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    have hsig := hsigma q hq chi
    have hsigmaHalf : sigma q chi ∈ Set.Ioo (0 : ℝ) (1 / 2) :=
      ⟨hsig.1.1, hsig.1.2.trans_le hbHalf⟩
    have hTpos : 0 < T := hH.trans hTIoo.1
    refine ⟨hTpos, hsigmaHalf, ?_, ?_, ?_⟩
    · intro u hu hzero
      let z : ℂ := ((sigma q chi : ℝ) : ℂ) + (u : ℂ) * Complex.I
      have hzrect : z ∈ zeroRectangle 0 (H + 4) := by
        constructor
        · constructor
          · simpa [z] using hsigmaHalf.1.le
          · simpa [z] using hsigmaHalf.2.le.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
        · constructor
          · have : -(H + 4) ≤ u := by linarith [hu.1, hTIoo.2]
            simpa [z] using this
          · have : u ≤ H + 4 := by linarith [hu.2, hTIoo.2]
            simpa [z] using this
      have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 4) :=
        (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
          chi.primitiveCharacter 0 (H + 4) hzrect).2 hzero
      have hdist := hsig.2.2 u z hzS
      have hdpos := exerciseScaledRealClearance_pos
        chi.primitiveCharacter H hb
      have : exerciseScaledRealClearance chi.primitiveCharacter H b ≤ 0 := by
        simpa [z] using hdist
      linarith
    · intro r hr hzero
      let z : ℂ := (r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I
      have hzrect : z ∈ zeroRectangle 0 (H + 4) := by
        constructor
        · constructor
          · have : 0 ≤ r := hsigmaHalf.1.le.trans hr.1
            simpa [z] using this
          · simpa [z] using hr.2
        · constructor
          · have : -(H + 4) ≤ -T := by linarith [hTIoo.2]
            simpa [z] using this
          · have : -T ≤ H + 4 := by linarith [hH, hTIoo.1]
            simpa [z] using this
      have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 4) :=
        (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
          chi.primitiveCharacter 0 (H + 4) hzrect).2 hzero
      have hrange : -z.im ∈ Set.Icc (H - 1) (H + 2) := by
        have him : -z.im = T := by simp [z]
        rw [him]
        constructor <;> linarith [hTIoo.1, hTIoo.2]
      have hzFamily : -z.im ∈ familyExerciseLocalImagCoordinates Q H := by
        apply mem_familyImagCoordinates Q H q hq chi
        exact mem_exerciseLocalImagCoordinates_of_mem_global_bottom
          chi.primitiveCharacter hzS hrange
      have hclear := familyExerciseHorizontalClearance_le_abs_sub
        Q H hTG hzFamily
      have hdpos : 0 < familyExerciseHorizontalClearance Q H := by
        unfold familyExerciseHorizontalClearance
        positivity
      have him : -z.im = T := by simp [z]
      rw [him, sub_self, abs_zero] at hclear
      linarith
    · intro r hr hzero
      let z : ℂ := (r : ℂ) + (T : ℂ) * Complex.I
      have hzrect : z ∈ zeroRectangle 0 (H + 4) := by
        constructor
        · constructor
          · have : 0 ≤ r := hsigmaHalf.1.le.trans hr.1
            simpa [z] using this
          · simpa [z] using hr.2
        · constructor
          · have : -(H + 4) ≤ T := by linarith [hH, hTIoo.1]
            simpa [z] using this
          · have : T ≤ H + 4 := by linarith [hTIoo.2]
            simpa [z] using this
      have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 4) :=
        (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
          chi.primitiveCharacter 0 (H + 4) hzrect).2 hzero
      have hrange : z.im ∈ Set.Icc (H - 1) (H + 2) := by
        have him : z.im = T := by simp [z]
        rw [him]
        constructor <;> linarith [hTIoo.1, hTIoo.2]
      have hzFamily : z.im ∈ familyExerciseLocalImagCoordinates Q H := by
        apply mem_familyImagCoordinates Q H q hq chi
        exact mem_exerciseLocalImagCoordinates_of_mem_global_top
          chi.primitiveCharacter hzS hrange
      have hclear := familyExerciseHorizontalClearance_le_abs_sub
        Q H hTG hzFamily
      have hdpos : 0 < familyExerciseHorizontalClearance Q H := by
        unfold familyExerciseHorizontalClearance
        positivity
      have him : z.im = T := by simp [z]
      rw [him, sub_self, abs_zero] at hclear
      linarith

end
end MAPAPSignedAlignedFamilyContourAperture

#print axioms MAPAPSignedAlignedFamilyContourAperture.exists_familyExerciseContourAperture
#print axioms MAPAPSignedAlignedFamilyContourAperture.exists_familyExerciseSmallRealEdges
#print axioms MAPAPSignedAlignedFamilyContourAperture.familyPaperEdgeLegal_of_familyExerciseClearance
#print axioms MAPAPSignedAlignedFamilyContourAperture.exists_familyExerciseContourAperture_legal
#print axioms MAPAPSignedAlignedFamilyContourAperture.exists_familyExerciseGoodHeightAperture
#print axioms MAPAPSignedAlignedFamilyContourAperture.exists_familyExerciseGoodHeightSmallEdgesLegal
