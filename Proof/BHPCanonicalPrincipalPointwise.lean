import BHPCanonicalNonprincipalPointwise
import BHPPrincipalResidueBound

/-!
# Source-faithful principal BHP pointwise contour bound

The principal character differs from the nonprincipal argument in exactly two
places: the translated pole contributes its true residue, and the horizontal
edge requires a zeta bound rather than the nonprincipal ambient interpolation.
This file certifies every other step while retaining the Perron `/w` kernel.
-/

namespace MAPBHPCanonicalPrincipalPointwise

open MAPBHPCorrectedContourShift
open MAPBHPCorrectedPerronKernel
open MAPBHPCanonicalNonprincipalPointwise
open MAPBHPPrincipalResidueBound
open MAPMRTLemma211AllCharacterSource
open MAPMRTCorollary25Minkowski
open RamachandraTheorem6ShiftedStripSource

noncomputable section

/-- The literal remaining principal analytic input.  It asks only for the two
horizontal edges of the already fixed source-faithful rectangle.  The factor
`(1+log x0)^2` is deliberately generous; it is harmless in the MAP polylog-q
range and avoids hiding an epsilon-dependent constant. -/
def CanonicalPrincipalHorizontalSource : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (q X : ℕ) [NeZero q] (t T x0 : ℝ),
      2 ≤ X → 1 ≤ T → 8 ≤ x0 →
      (q : ℝ) ≤ x0 → (X : ℝ) ≤ x0 →
      T ≤ x0 → 2 * T ≤ x0 → |t| ≤ T →
      ‖bhpHorizontalBoundaryIntegral (1 : DirichletCharacter ℂ q) (X : ℝ) t
          (canonicalRamachandraOffset x0)
          ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ ≤
        C * (1 + Real.log x0) ^ 2 *
          (Real.sqrt (q : ℝ) / Real.sqrt T + Real.sqrt (X : ℝ) / T)

/-- Exact principal pointwise inequality before any logarithmic absorption.
The radius of the pole excision is the Ramachandra offset itself; all four
strict containment inequalities are proved from `x0 >= 8`, `T >= 1`, and
`|t| <= T`. -/
theorem norm_criticalPrefixPolynomial_principal_le_canonicalContour
    {q X : ℕ} [NeZero q] {t T x0 : ℝ}
    (hX : 2 ≤ X) (hT : 1 ≤ T) (hx0 : 8 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hXx : (X : ℝ) ≤ x0)
    (hTwoTx : 2 * T ≤ x0) (ht : |t| ≤ T) :
    ‖criticalPrefixPolynomial q X (1 : DirichletCharacter ℂ q) t‖ ≤
      canonicalTitchmarshConstant *
          (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
            1 / Real.sqrt (X : ℝ)) +
        (Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
            (2 * Real.pi)) *
          perronConvolution
            (shiftedCriticalLineLNorm (1 : DirichletCharacter ℂ q)
              (canonicalRamachandraOffset x0)) (2 * T) t +
        ‖bhpHorizontalBoundaryIntegral (1 : DirichletCharacter ℂ q) (X : ℝ) t
          (canonicalRamachandraOffset x0)
          ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ +
        3 * Real.sqrt (X : ℝ) / (1 + |t|) := by
  have hXreal : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : 0 < (X : ℝ) := by positivity
  have hTwoT : 2 ≤ 2 * T := by linarith
  have hTwoT0 : 0 ≤ 2 * T := by linarith
  have hx0one : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hx0one
  let delta : ℝ := canonicalRamachandraOffset x0
  let c : ℝ := (1 / 2 : ℝ) + (Real.log x0)⁻¹
  let r : ℝ := delta
  have hdelta : 0 < delta := by
    dsimp [delta, canonicalRamachandraOffset]
    positivity
  have hdeltaOne : delta < 1 := by
    dsimp [delta, canonicalRamachandraOffset]
    have hlog2le : Real.log 2 ≤ Real.log x0 :=
      Real.strictMonoOn_log.monotoneOn (by norm_num : (0 : ℝ) < 2)
        (by linarith : 0 < x0) (by linarith)
    have hden : (1 : ℝ) < 400 * Real.log x0 := by
      nlinarith [Real.log_two_gt_d9]
    exact (inv_lt_one₀ (by positivity : 0 < 400 * Real.log x0)).2 hden
  have hdc : delta ≤ c := by
    have hdle : delta ≤ (Real.log x0)⁻¹ := by
      dsimp [delta, canonicalRamachandraOffset]
      have hden : Real.log x0 ≤ 400 * Real.log x0 := by nlinarith
      have hi := one_div_le_one_div_of_le hlog hden
      simpa [one_div] using hi
    dsimp [c]
    linarith
  have hleft : delta < (bhpPrincipalPole t).re - r := by
    have hlog2le : Real.log 2 ≤ Real.log x0 :=
      Real.strictMonoOn_log.monotoneOn (by norm_num : (0 : ℝ) < 2)
        (by linarith : 0 < x0) (by linarith)
    have hden4 : (4 : ℝ) < 400 * Real.log x0 := by
      nlinarith [Real.log_two_gt_d9]
    have hsmall : delta < 1 / 4 := by
      dsimp [delta, canonicalRamachandraOffset]
      simpa [one_div] using
        (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4) hden4)
    simp [bhpPrincipalPole, r]
    linarith
  have hright : (bhpPrincipalPole t).re + r < c := by
    have hstrict : delta < (Real.log x0)⁻¹ := by
      dsimp [delta, canonicalRamachandraOffset]
      have hden : Real.log x0 < 400 * Real.log x0 := by nlinarith
      have hi := one_div_lt_one_div_of_lt hlog hden
      simpa [one_div] using hi
    simp [bhpPrincipalPole, r, c]
    linarith
  have hdeltaT : delta < T := hdeltaOne.trans_le hT
  have htLower : -T ≤ t := (abs_le.mp ht).1
  have htUpper : t ≤ T := (abs_le.mp ht).2
  have hbottom : -(2 * T) < (bhpPrincipalPole t).im - r := by
    simp [bhpPrincipalPole, r]
    linarith
  have htop : (bhpPrincipalPole t).im + r < 2 * T := by
    simp [bhpPrincipalPole, r]
    linarith
  have hperron := canonicalTitchmarshBound q X
    (1 : DirichletCharacter ℂ q) t (2 * T) x0
      hX hTwoT hqx hXx hTwoTx
  have hcontour :=
    bhpPrincipalRightLine_eq_correctedLeft_sub_horizontal_add_residue
      (q := q) (X := (X : ℝ)) (t := t) (delta := delta) (c := c)
      (H := 2 * T) (r := r) hXpos hdelta hdc hdelta hleft hright
      hbottom htop
  have hrightNorm :
      ‖bhpVerticalLineIntegral (1 : DirichletCharacter ℂ q) (X : ℝ) t c
          (2 * T)‖ ≤
        ‖shiftedLeftLineIntegral (1 : DirichletCharacter ℂ q) (X : ℝ)
            delta (2 * T) t‖ +
          ‖bhpHorizontalBoundaryIntegral (1 : DirichletCharacter ℂ q)
            (X : ℝ) t delta c (2 * T)‖ +
          ‖bhpPrincipalResidue q (X : ℝ) t‖ := by
    rw [hcontour]
    calc
      ‖shiftedLeftLineIntegral (1 : DirichletCharacter ℂ q) (X : ℝ)
            delta (2 * T) t -
          bhpHorizontalBoundaryIntegral (1 : DirichletCharacter ℂ q)
            (X : ℝ) t delta c (2 * T) +
          bhpPrincipalResidue q (X : ℝ) t‖ ≤
        ‖shiftedLeftLineIntegral (1 : DirichletCharacter ℂ q) (X : ℝ)
            delta (2 * T) t -
          bhpHorizontalBoundaryIntegral (1 : DirichletCharacter ℂ q)
            (X : ℝ) t delta c (2 * T)‖ +
          ‖bhpPrincipalResidue q (X : ℝ) t‖ := norm_add_le _ _
      _ ≤ (‖shiftedLeftLineIntegral (1 : DirichletCharacter ℂ q) (X : ℝ)
              delta (2 * T) t‖ +
            ‖bhpHorizontalBoundaryIntegral (1 : DirichletCharacter ℂ q)
              (X : ℝ) t delta c (2 * T)‖) +
          ‖bhpPrincipalResidue q (X : ℝ) t‖ :=
        add_le_add (norm_sub_le _ _) (le_refl _)
      _ = _ := by ring
  have hleftBound :=
    norm_scaledAmbientOffsetLeftLineIntegral_le
      (1 : DirichletCharacter ℂ q) (A := (400 : ℝ))
      (X := (X : ℝ)) (T := 2 * T) (t := t) (x0 := x0)
      (by norm_num) hXreal hXx hTwoT0
  have hresidue := norm_bhpPrincipalResidue_le q hXpos (t := t)
  have hprefixSplit :
      criticalPrefixPolynomial q X (1 : DirichletCharacter ℂ q) t =
        (criticalPrefixPolynomial q X (1 : DirichletCharacter ℂ q) t -
          bhpVerticalLineIntegral (1 : DirichletCharacter ℂ q) (X : ℝ) t c
            (2 * T)) +
        bhpVerticalLineIntegral (1 : DirichletCharacter ℂ q) (X : ℝ) t c
          (2 * T) := by ring
  rw [hprefixSplit]
  calc
    ‖(criticalPrefixPolynomial q X (1 : DirichletCharacter ℂ q) t -
          bhpVerticalLineIntegral (1 : DirichletCharacter ℂ q) (X : ℝ) t c
            (2 * T)) +
        bhpVerticalLineIntegral (1 : DirichletCharacter ℂ q) (X : ℝ) t c
          (2 * T)‖ ≤
      ‖criticalPrefixPolynomial q X (1 : DirichletCharacter ℂ q) t -
          bhpVerticalLineIntegral (1 : DirichletCharacter ℂ q) (X : ℝ) t c
            (2 * T)‖ +
        ‖bhpVerticalLineIntegral (1 : DirichletCharacter ℂ q) (X : ℝ) t c
          (2 * T)‖ := norm_add_le _ _
    _ ≤ canonicalTitchmarshConstant *
          (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
            1 / Real.sqrt (X : ℝ)) +
        (‖shiftedLeftLineIntegral (1 : DirichletCharacter ℂ q) (X : ℝ)
            delta (2 * T) t‖ +
          ‖bhpHorizontalBoundaryIntegral (1 : DirichletCharacter ℂ q)
            (X : ℝ) t delta c (2 * T)‖ +
          ‖bhpPrincipalResidue q (X : ℝ) t‖) :=
      add_le_add (by simpa [c] using hperron) hrightNorm
    _ ≤ canonicalTitchmarshConstant *
          (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
            1 / Real.sqrt (X : ℝ)) +
        ((Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
            (2 * Real.pi)) *
          perronConvolution
            (shiftedCriticalLineLNorm (1 : DirichletCharacter ℂ q)
              (canonicalRamachandraOffset x0)) (2 * T) t +
          ‖bhpHorizontalBoundaryIntegral (1 : DirichletCharacter ℂ q)
            (X : ℝ) t (canonicalRamachandraOffset x0)
              ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ +
          3 * Real.sqrt (X : ℝ) / (1 + |t|)) := by
      apply add_le_add (le_refl _)
      apply add_le_add
      · apply add_le_add
        · simpa [delta, canonicalRamachandraOffset] using hleftBound
        · rfl
      · exact hresidue
    _ = _ := by ring

end
end MAPBHPCanonicalPrincipalPointwise

#print axioms MAPBHPCanonicalPrincipalPointwise.norm_criticalPrefixPolynomial_principal_le_canonicalContour
