import APTailToRemainderTransfer
import PaperEdgePrimitiveComponents

/-!
# Corrected common-height AP contour contract

The rejected exact-height contract cannot demand horizontal nonvanishing for
every real `X`: the prescribed height can equal a zero ordinate.  This module
selects one common height in `(H,H+1)` after taking the finite union over all
ambient characters up to `Q`.  The right edge is the paper edge; it is enough
to certify horizontal nonvanishing through real part one because the
regularized L-function is already nonzero in `re s ≥ 1`.
-/

namespace MAPAPCorrectedCommonHeightContract

open Set
open scoped BigOperators ENNReal
open APFoundation MAPAPLiteralTailContract
open DirichletZeros PrimitiveTruncatedExplicitFormulaBridge

noncomputable section

/-- Legal common-height contour data sufficient for every paper right edge. -/
def paperEdgeContourLegal {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma T : ℝ) : Prop := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact 0 < T ∧ sigma ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧
    (∀ u ∈ Set.Icc (-T) T,
      regularizedLFunction chi.primitiveCharacter
        ((sigma : ℂ) + (u : ℂ) * Complex.I) ≠ 0) ∧
    (∀ r ∈ Set.Icc sigma 1,
      regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0) ∧
    (∀ r ∈ Set.Icc sigma 1,
      regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0)

/-- Exact failure certificate for the rejected fixed-height contour
interface: a zero on its top edge contradicts legality immediately. -/
theorem not_primitiveContourLegal_of_top_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor]
    {sigma T r : ℝ} (hr : r ∈ Set.Icc sigma 3)
    (hzero : regularizedLFunction chi.primitiveCharacter
      ((r : ℂ) + (T : ℂ) * Complex.I) = 0) :
    ¬ primitiveContourLegal chi sigma T := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  intro hlegal
  exact (hlegal.2.2.2.2.2 r hr) hzero

/-- Horizontal paper-edge nonvanishing follows from legality through `re=1`
and the certified zero-free half-plane beyond it. -/
theorem paperEdgeContourLegal.horizontal_nonzero
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    [NeZero chi.conductor]
    {sigma T c : ℝ} (hlegal : paperEdgeContourLegal chi sigma T)
    (hc : 1 ≤ c) :
    (∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0) ∧
    (∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  constructor
  · intro r hr
    by_cases hr1 : r ≤ 1
    · exact hlegal.2.2.2.1 r ⟨hr.1, hr1⟩
    · apply MAPMellinDetectorLeaf.regularizedLFunction_ne_zero_of_one_le_re
      change 1 ≤ (((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)).re
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        neg_zero, zero_mul, sub_zero, add_zero]
      exact (not_le.mp hr1).le
  · intro r hr
    by_cases hr1 : r ≤ 1
    · exact hlegal.2.2.2.2 r ⟨hr.1, hr1⟩
    · apply MAPMellinDetectorLeaf.regularizedLFunction_ne_zero_of_one_le_re
      change 1 ≤ (((r : ℂ) + (T : ℂ) * Complex.I)).re
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        zero_mul, sub_zero, add_zero]
      exact (not_le.mp hr1).le

/-- One common height avoids the finite union of every primitive-inducer
zero divisor in the floor-capped ambient family.  Left edges remain
character-dependent, as they may without affecting equation (2.8). -/
theorem exists_commonHeight_familyPaperEdgeContours
    (Q : ℕ) {H : ℝ} (hH : 0 < H) :
    ∃ T ∈ Set.Ioo H (H + 1),
      ∃ sigma : ∀ (q : ℕ), q ∈ Finset.Icc 1 Q →
          DirichletCharacter ℂ q → ℝ,
        ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
          (chi : DirichletCharacter ℂ q),
          @paperEdgeContourLegal q
            ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
            chi (sigma q hq chi) T := by
  classical
  let A : Finset ℝ :=
    (Finset.Icc 1 Q).biUnion fun q =>
      if hq0 : q = 0 then ∅ else
        letI : NeZero q := ⟨hq0⟩
        (Finset.univ : Finset (DirichletCharacter ℂ q)).biUnion fun chi =>
          letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
          (zeroSupport chi.primitiveCharacter 0 (H + 1)).image
            (fun rho => |rho.im|)
  have hTinf : (Set.Ioo H (H + 1)).Infinite :=
    Set.Ioo_infinite (by linarith)
  obtain ⟨T, hTIoo, hTA⟩ :=
    (hTinf.diff A.finite_toSet).nonempty
  have hsigmaExists : ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
      (chi : DirichletCharacter ℂ q),
      letI : NeZero q :=
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      ∃ sigma : ℝ, sigma ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧
        (∀ u ∈ Set.Icc (-T) T,
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
        · have : s ≤ 1 := by linarith [hsIoo.2]
          simpa [z] using this
      · constructor
        · have : -(H + 1) ≤ u := by linarith [hu.1, hTIoo.2]
          simpa [z] using this
        · have : u ≤ H + 1 := by linarith [hu.2, hTIoo.2]
          simpa [z] using this
    have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 1) :=
      (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        chi.primitiveCharacter 0 (H + 1) hzrect).2 hzero
    apply hsR
    change s ∈ R
    exact Finset.mem_image.mpr ⟨z, hzS, by simp [z]⟩
  choose sigma hsigmaMem hsigmaLeft using hsigmaExists
  refine ⟨T, hTIoo, sigma, ?_⟩
  intro q hq chi
  have hqpos := (Finset.mem_Icc.mp hq).1
  have hq0 : q ≠ 0 := Nat.ne_of_gt hqpos
  letI : NeZero q := ⟨hq0⟩
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  refine ⟨hH.trans hTIoo.1, hsigmaMem q hq chi,
    hsigmaLeft q hq chi, ?_, ?_⟩
  · intro r hr hzero
    let z : ℂ := (r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I
    have hzrect : z ∈ zeroRectangle 0 (H + 1) := by
      constructor
      · constructor
        · have : 0 ≤ r := (hsigmaMem q hq chi).1.le.trans hr.1
          simpa [z] using this
        · simpa [z] using hr.2
      · constructor
        · have : -(H + 1) ≤ -T := by linarith [hTIoo.2]
          simpa [z] using this
        · have : -T ≤ H + 1 := by linarith [hH, hTIoo.1]
          simpa [z] using this
    have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 1) :=
      (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        chi.primitiveCharacter 0 (H + 1) hzrect).2 hzero
    apply hTA
    change T ∈ A
    apply Finset.mem_biUnion.mpr
    refine ⟨q, hq, ?_⟩
    simp only [dif_neg hq0]
    apply Finset.mem_biUnion.mpr
    refine ⟨chi, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨z, hzS, ?_⟩
    have hTpos : 0 < T := hH.trans hTIoo.1
    simp [z, abs_of_pos hTpos]

  · intro r hr hzero
    let z : ℂ := (r : ℂ) + (T : ℂ) * Complex.I
    have hzrect : z ∈ zeroRectangle 0 (H + 1) := by
      constructor
      · constructor
        · have : 0 ≤ r := (hsigmaMem q hq chi).1.le.trans hr.1
          simpa [z] using this
        · simpa [z] using hr.2
      · constructor
        · have : -(H + 1) ≤ T := by linarith [hH, hTIoo.1]
          simpa [z] using this
        · simpa [z] using hTIoo.2.le
    have hzS : z ∈ zeroSupport chi.primitiveCharacter 0 (H + 1) :=
      (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        chi.primitiveCharacter 0 (H + 1) hzrect).2 hzero
    apply hTA
    change T ∈ A
    apply Finset.mem_biUnion.mpr
    refine ⟨q, hq, ?_⟩
    simp only [dif_neg hq0]
    apply Finset.mem_biUnion.mpr
    refine ⟨chi, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨z, hzS, ?_⟩
    have hTpos : 0 < T := hH.trans hTIoo.1
    simp [z, abs_of_pos hTpos]

/-- Total-function wrapper matching the shape consumed by AP family sums. -/
theorem exists_commonHeight_familyPaperEdgeContours_total
    (Q : ℕ) {H : ℝ} (hH : 0 < H) :
    ∃ T ∈ Set.Ioo H (H + 1),
      ∃ sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ,
        ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
          (chi : DirichletCharacter ℂ q),
          @paperEdgeContourLegal q
            ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
            chi (sigma q chi) T := by
  classical
  obtain ⟨T, hT, sigma, hlegal⟩ :=
    exists_commonHeight_familyPaperEdgeContours Q hH
  let sigmaTotal : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ := fun q chi =>
    if hq : q ∈ Finset.Icc 1 Q then sigma q hq chi else 1 / 4
  refine ⟨T, hT, sigmaTotal, ?_⟩
  intro q hq chi
  simpa only [sigmaTotal, dif_pos hq] using hlegal q hq chi

end
end MAPAPCorrectedCommonHeightContract

#print axioms MAPAPCorrectedCommonHeightContract.not_primitiveContourLegal_of_top_zero
#print axioms MAPAPCorrectedCommonHeightContract.paperEdgeContourLegal.horizontal_nonzero
#print axioms MAPAPCorrectedCommonHeightContract.exists_commonHeight_familyPaperEdgeContours
#print axioms MAPAPCorrectedCommonHeightContract.exists_commonHeight_familyPaperEdgeContours_total
