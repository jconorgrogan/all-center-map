import APDirectAlignedTailClosure
import Mathlib.MeasureTheory.Integral.Average

/-!
# Common-contour selection for the signed aligned AP family

The preferred analytic source in this file is below
`AlignedLeftHorizontalFamilySquare`: it averages the exact signed family
energy over a positive-measure set of legal common heights.  A first-moment
argument selects one common height.  The finite `q,chi` edge family can be
chosen once for the entire interval away from an explicit finite set of zero
ordinates, so no measurable selection in the height variable is needed.

The left and horizontal contour windows are never separated.  Their signs and
the legal real-`Y` supremum remain exactly those of
`familyAlignedLeftHorizontalMajorant`.
-/

namespace MAPAPSignedAlignedContourSelection

open MeasureTheory Set
open scoped ENNReal
open MAPFixedScaleAPZeroRoute
open MAPAPCorrectedCommonHeightContract
open MAPAPDirectAlignedTailClosure
open DirichletZeros PrimitiveTruncatedExplicitFormulaBridge

noncomputable section

/-- Family-wide legality for one common height and one character-dependent
left-edge family.  The edge may depend on `(q,chi)` but not on the height
variable being averaged. -/
def familyPaperEdgeLegal
    (Q : ℕ) (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (T : ℝ) : Prop :=
  ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
      (chi : DirichletCharacter ℂ q),
    @paperEdgeContourLegal q
      ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      chi (sigma q chi) T

/-- The exact joint signed family energy at one common height.  In particular,
the left and horizontal contour terms are still added before the norm square,
and the supremum over legal real window lengths remains inside
`familyAlignedLeftHorizontalMajorant`. -/
def signedAlignedFamilyHeightCost
    (Q : ℕ) (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (epsilon X T : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Set.Icc (X / 2) (4 * X),
    familyAlignedLeftHorizontalMajorant Q sigma T epsilon X x

/-- The finite union of primitive-inducer zero ordinates that a positive
common height must avoid.  Since the selected heights are positive, absolute
ordinates encode both horizontal sides. -/
def commonHeightForbiddenOrdinates (Q : ℕ) (H : ℝ) : Finset ℝ :=
  (Finset.Icc 1 Q).biUnion fun q =>
    if hq0 : q = 0 then ∅ else
      letI : NeZero q := ⟨hq0⟩
      (Finset.univ : Finset (DirichletCharacter ℂ q)).biUnion fun chi =>
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        (zeroSupport chi.primitiveCharacter 0 (H + 1)).image
          (fun rho => |rho.im|)

/-- The left edges can be selected once for the whole height interval.  Away
from the explicit finite ordinate obstruction, that one finite edge family is
legal at every common height.  This is the deterministic finite-choice weld;
it requires no measurable selection in the height variable. -/
theorem exists_fixedFamilySigma_legal_off_forbidden
    (Q : ℕ) {H : ℝ} (hH : 0 < H) :
    ∃ sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ,
      ∀ T ∈ Set.Ioo H (H + 1),
        T ∉ commonHeightForbiddenOrdinates Q H →
          familyPaperEdgeLegal Q sigma T := by
  classical
  have hsigmaExists : ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
      (chi : DirichletCharacter ℂ q),
      letI : NeZero q :=
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      ∃ sigma : ℝ, sigma ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧
        (∀ u ∈ Set.Icc (-(H + 1)) (H + 1),
          letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
          regularizedLFunction chi.primitiveCharacter
            ((sigma : ℂ) + (u : ℂ) * Complex.I) ≠ 0) := by
    intro q hq chi
    letI : NeZero q :=
      ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
    letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    let R : Finset ℝ :=
      (zeroSupport chi.primitiveCharacter 0 (H + 1)).image Complex.re
    have hsigInf : (Set.Ioo (0 : ℝ) (1 / 2)).Infinite :=
      Set.Ioo_infinite (by norm_num)
    obtain ⟨s, hsIoo, hsR⟩ :=
      (hsigInf.diff R.finite_toSet).nonempty
    refine ⟨s, hsIoo, ?_⟩
    intro u hu hzero
    let z : ℂ := (s : ℂ) + (u : ℂ) * Complex.I
    have hzrect : z ∈ zeroRectangle 0 (H + 1) := by
      constructor
      · constructor
        · simpa [z] using hsIoo.1.le
        · have hsone : s ≤ 1 := by linarith [hsIoo.2]
          simpa [z] using hsone
      · simpa [z] using hu
    have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 1) :=
      (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        chi.primitiveCharacter 0 (H + 1) hzrect).2 hzero
    apply hsR
    change s ∈ R
    exact Finset.mem_image.mpr ⟨z, hzS, by simp [z]⟩
  choose sigma hsigmaMem hsigmaLeft using hsigmaExists
  let sigmaTotal : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ :=
    fun q chi =>
      if hq : q ∈ Finset.Icc 1 Q then sigma q hq chi else 1 / 4
  refine ⟨sigmaTotal, ?_⟩
  intro T hTIoo hTavoid
  unfold familyPaperEdgeLegal
  intro q hq chi
  have hqpos := (Finset.mem_Icc.mp hq).1
  have hq0 : q ≠ 0 := Nat.ne_of_gt hqpos
  letI : NeZero q := ⟨hq0⟩
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hTpos : 0 < T := hH.trans hTIoo.1
  have hsigmaMemTotal : sigmaTotal q chi ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
    simpa only [sigmaTotal, dif_pos hq] using hsigmaMem q hq chi
  refine ⟨hTpos, hsigmaMemTotal, ?_, ?_, ?_⟩
  · intro u hu
    have huWide : u ∈ Set.Icc (-(H + 1)) (H + 1) := by
      constructor <;> linarith [hu.1, hu.2, hTIoo.2]
    simpa only [sigmaTotal, dif_pos hq] using
      hsigmaLeft q hq chi u huWide
  · intro r hr hzero
    let z : ℂ := (r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I
    have hzrect : z ∈ zeroRectangle 0 (H + 1) := by
      constructor
      · constructor
        · have hrzero : 0 ≤ r := hsigmaMemTotal.1.le.trans hr.1
          simpa [z] using hrzero
        · simpa [z] using hr.2
      · constructor
        · have : -(H + 1) ≤ -T := by linarith [hTIoo.2]
          simpa [z] using this
        · have : -T ≤ H + 1 := by linarith [hH, hTIoo.1]
          simpa [z] using this
    have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 1) :=
      (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        chi.primitiveCharacter 0 (H + 1) hzrect).2 hzero
    apply hTavoid
    unfold commonHeightForbiddenOrdinates
    apply Finset.mem_biUnion.mpr
    refine ⟨q, hq, ?_⟩
    simp only [dif_neg hq0]
    apply Finset.mem_biUnion.mpr
    refine ⟨chi, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨z, hzS, by simp [z, abs_of_pos hTpos]⟩

  · intro r hr hzero
    let z : ℂ := (r : ℂ) + (T : ℂ) * Complex.I
    have hzrect : z ∈ zeroRectangle 0 (H + 1) := by
      constructor
      · constructor
        · have hrzero : 0 ≤ r := hsigmaMemTotal.1.le.trans hr.1
          simpa [z] using hrzero
        · simpa [z] using hr.2
      · constructor
        · have : -(H + 1) ≤ T := by linarith [hH, hTIoo.1]
          simpa [z] using this
        · simpa [z] using hTIoo.2.le
    have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 1) :=
      (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        chi.primitiveCharacter 0 (H + 1) hzrect).2 hzero
    apply hTavoid
    unfold commonHeightForbiddenOrdinates
    apply Finset.mem_biUnion.mpr
    refine ⟨q, hq, ?_⟩
    simp only [dif_neg hq0]
    apply Finset.mem_biUnion.mpr
    refine ⟨chi, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨z, hzS, by simp [z, abs_of_pos hTpos]⟩

/-- Deterministic shell of the averaged contract: the explicit cofinite set of
legal common heights is measurable and has the full positive measure of the
unit interval.  An analytic source may shrink this set further to impose
quantitative zero clearance. -/
theorem exists_positiveMeasureSet_fixedFamilySigma_legal
    (Q : ℕ) {H : ℝ} (hH : 0 < H) :
    ∃ G : Set ℝ,
      ∃ sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ,
        MeasurableSet G ∧
        volume G ≠ 0 ∧
        G ⊆ Set.Ioo H (H + 1) ∧
        ∀ T ∈ G, familyPaperEdgeLegal Q sigma T := by
  classical
  obtain ⟨sigma, hlegal⟩ :=
    exists_fixedFamilySigma_legal_off_forbidden Q hH
  let F : Finset ℝ := commonHeightForbiddenOrdinates Q H
  let G : Set ℝ := Set.Ioo H (H + 1) \ (F : Set ℝ)
  refine ⟨G, sigma, ?_, ?_, Set.diff_subset, ?_⟩
  · exact measurableSet_Ioo.diff F.measurableSet
  · have hFzero : volume (F : Set ℝ) = 0 := F.measure_zero volume
    have hGvolume : volume G = volume (Set.Ioo H (H + 1)) := by
      simpa only [G] using
        (measure_diff_null (s := Set.Ioo H (H + 1)) hFzero)
    rw [hGvolume, Real.volume_Ioo]
    norm_num
  · intro T hTG
    exact hlegal T hTG.1 hTG.2

/-- Source-faithful height-average form of the remaining signed contour
estimate.  The analytic source may choose a measurable positive-measure set
of good common heights and one finite character-edge family legal throughout
that set.  This permits a quantitative-clearance subset when the analytic
log-derivative estimate needs one; it does not demand a bound at every merely
nonvanishing contour. -/
def AveragedGoodHeightAlignedLeftHorizontalMeanSquare : Prop :=
  ∀ K A epsilon : ℝ,
    0 < K → 0 < A → 0 < epsilon → epsilon ≤ 13 / 30 →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
        let reserve := min epsilon (1 / 10)
        let H0 := apZeroHeight reserve X
        let Q := ⌊Real.rpow (Real.log X) K⌋₊
        ∃ G : Set ℝ,
          ∃ sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ,
            MeasurableSet G ∧
            volume G ≠ 0 ∧
            G ⊆ Set.Ioo H0 (H0 + 1) ∧
            (∀ T ∈ G, familyPaperEdgeLegal Q sigma T) ∧
            AEMeasurable
              (signedAlignedFamilyHeightCost Q sigma epsilon X)
              (volume.restrict G) ∧
            (⨍⁻ T in G,
                signedAlignedFamilyHeightCost Q sigma epsilon X T ∂volume) ≤
              ENNReal.ofReal (C * X * Real.rpow (Real.log X) (-A))

/-- First-moment selection of one common contour height from the source's
positive-measure good-height set.  The normalized `laverage` gives the target
constant with no Markov loss. -/
theorem alignedLeftHorizontalFamilySquare_of_averagedGoodHeight
    (hAverage : AveragedGoodHeightAlignedLeftHorizontalMeanSquare) :
    AlignedLeftHorizontalFamilySquare := by
  intro K A epsilon hK hA hepsilon hepsilonCap
  rcases hAverage K A epsilon hK hA hepsilon hepsilonCap with
    ⟨C, X0, hC, hX0, hAverageX⟩
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X hXX0
  have hAtX := hAverageX X hXX0
  dsimp only at hAtX ⊢
  rcases hAtX with
    ⟨G, sigma, hGmeas, hGnonzero, hGIoo, hlegal, hcostMeas, haverage⟩
  have hGfinite : volume G ≠ ∞ := by
    apply ne_of_lt
    exact (measure_mono hGIoo).trans_lt measure_Ioo_lt_top
  obtain ⟨T, hTG, hTcost⟩ :=
    exists_le_setLAverage hGnonzero hGfinite hcostMeas
  refine ⟨T, hGIoo hTG, sigma, ?_, ?_⟩
  · exact hlegal T hTG
  · exact hTcost.trans haverage

/-- A stronger exploratory contour estimate, retained for comparison.  This
uniform form is not the preferred live source because it demands the bound at
every merely legal contour, including contours arbitrarily close to zeros. -/
def UniformLegalAlignedLeftHorizontalMeanSquare : Prop :=
  ∀ K A epsilon : ℝ,
    0 < K → 0 < A → 0 < epsilon → epsilon ≤ 13 / 30 →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
        let reserve := min epsilon (1 / 10)
        let H0 := apZeroHeight reserve X
        let Q := ⌊Real.rpow (Real.log X) K⌋₊
        ∀ T ∈ Set.Ioo H0 (H0 + 1),
          ∀ sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ,
            (∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
                (chi : DirichletCharacter ℂ q),
              @paperEdgeContourLegal q
                ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
                chi (sigma q chi) T) →
            (∫⁻ x in Set.Icc (X / 2) (4 * X),
                familyAlignedLeftHorizontalMajorant Q sigma T epsilon X x) ≤
              ENNReal.ofReal (C * X * Real.rpow (Real.log X) (-A))

/-- The finite zero divisor supplies a common zero-avoiding height and one
legal left edge per ambient character.  Applying the fixed-data mean estimate
to that selected family produces the exact signed contour-family square. -/
theorem alignedLeftHorizontalFamilySquare_of_uniformLegalMeanSquare
    (hMean : UniformLegalAlignedLeftHorizontalMeanSquare) :
    AlignedLeftHorizontalFamilySquare := by
  intro K A epsilon hK hA hepsilon hepsilonCap
  rcases hMean K A epsilon hK hA hepsilon hepsilonCap with
    ⟨C, X0, hC, hX0, hMeanX⟩
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X hXX0
  have hXtwo : 2 ≤ X := hX0.trans hXX0
  have hXpos : 0 < X := zero_lt_two.trans_le hXtwo
  let reserve : ℝ := min epsilon (1 / 10)
  let H0 : ℝ := apZeroHeight reserve X
  let Q : ℕ := ⌊Real.rpow (Real.log X) K⌋₊
  have hH0 : 0 < H0 := by
    dsimp only [H0, apZeroHeight]
    exact Real.rpow_pos_of_pos hXpos _
  obtain ⟨T, hT, sigma, hlegal⟩ :=
    exists_commonHeight_familyPaperEdgeContours_total Q hH0
  dsimp only
  refine ⟨T, hT, sigma, hlegal, ?_⟩
  have hAtX := hMeanX X hXX0
  dsimp only at hAtX
  exact hAtX T hT sigma hlegal

end
end MAPAPSignedAlignedContourSelection

#print axioms MAPAPSignedAlignedContourSelection.alignedLeftHorizontalFamilySquare_of_uniformLegalMeanSquare
#print axioms MAPAPSignedAlignedContourSelection.exists_fixedFamilySigma_legal_off_forbidden
#print axioms MAPAPSignedAlignedContourSelection.exists_positiveMeasureSet_fixedFamilySigma_legal
#print axioms MAPAPSignedAlignedContourSelection.alignedLeftHorizontalFamilySquare_of_averagedGoodHeight
