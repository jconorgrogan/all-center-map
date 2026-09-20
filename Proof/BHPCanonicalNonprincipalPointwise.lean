import BHPTitchmarshTheorem319Proof
import BHPCanonicalHorizontalScalar

/-!
# Source-faithful nonprincipal BHP pointwise contour bound

This joins the premise-free Titchmarsh right edge to the corrected positive
Ramachandra offset.  The two offsets are kept distinct, and every occurrence
of the Perron kernel retains `/w`.
-/

namespace MAPBHPCanonicalNonprincipalPointwise

open MAPBHPCorrectedContourShift
open MAPBHPCorrectedPerronKernel
open MAPBHPCanonicalHorizontalScalar
open MAPBHPHorizontalEndpointInterpolation
open MAPMRTLemma211AllCharacterSource
open MAPMRTCorollary25Minkowski
open RamachandraTheorem6ShiftedStripSource

noncomputable section

/-- The single universal Titchmarsh constant selected from the premise-free
proof.  Keeping this choice outside every pointwise quantifier is essential
for the later finite-family fourth-moment summation. -/
def canonicalTitchmarshConstant : ℝ :=
  MAPBHPTitchmarshTheorem319Proof.bhpTheorem319TruncatedPerronSource_proved.choose

theorem canonicalTitchmarshConstant_pos :
    0 < canonicalTitchmarshConstant :=
  MAPBHPTitchmarshTheorem319Proof.bhpTheorem319TruncatedPerronSource_proved.choose_spec.1

theorem canonicalTitchmarshBound
    (q X : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
    (t T x0 : ℝ)
    (hX : 2 ≤ X) (hT : 2 ≤ T)
    (hqx : (q : ℝ) ≤ x0) (hXx : (X : ℝ) ≤ x0) (hTx : T ≤ x0) :
    ‖criticalPrefixPolynomial q X chi t -
        bhpVerticalLineIntegral chi (X : ℝ) t
          ((1 / 2 : ℝ) + (Real.log x0)⁻¹) T‖ ≤
      canonicalTitchmarshConstant *
        (Real.log x0 * Real.sqrt (X : ℝ) / T +
          1 / Real.sqrt (X : ℝ)) :=
  MAPBHPTitchmarshTheorem319Proof.bhpTheorem319TruncatedPerronSource_proved.choose_spec.2
    q X chi t T x0 hX hT hqx hXx hTx

/-- Exact nonprincipal pointwise inequality before the final harmless
polylogarithmic collapse of the two horizontal endpoint numerators. -/
theorem norm_criticalPrefixPolynomial_le_canonicalContour
    {q X : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) {t T x0 : ℝ}
    (hX : 2 ≤ X) (hT : 1 ≤ T) (hx0 : 8 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hXx : (X : ℝ) ≤ x0)
    (hTwoTx : 2 * T ≤ x0) :
    ‖criticalPrefixPolynomial q X chi t‖ ≤
      canonicalTitchmarshConstant *
          (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
            1 / Real.sqrt (X : ℝ)) +
        (Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
            (2 * Real.pi)) *
          perronConvolution
            (shiftedCriticalLineLNorm chi
              (canonicalRamachandraOffset x0)) (2 * T) t +
        ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
          (((ambientHorizontalGeneralEndpointNumerator q
                (canonicalRamachandraOffset x0) (Real.log x0)⁻¹
                (canonicalRamachandraOffset x0) (X : ℝ) (t + 2 * T) /
                  (2 * T)) +
            (ambientHorizontalGeneralEndpointNumerator q
                (canonicalRamachandraOffset x0) (Real.log x0)⁻¹
                (canonicalRamachandraOffset x0) (X : ℝ) (t - 2 * T) /
                  (2 * T))) *
              (1 / 2 + (Real.log x0)⁻¹ -
                canonicalRamachandraOffset x0)) := by
  have hXreal : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : 0 < (X : ℝ) := by positivity
  have hTwoT : 2 ≤ 2 * T := by linarith
  have hTwoT0 : 0 ≤ 2 * T := by linarith
  let C319 : ℝ := canonicalTitchmarshConstant
  have hperron := canonicalTitchmarshBound q X chi t (2 * T) x0
    hX hTwoT hqx hXx hTwoTx
  have hperronC :
      ‖criticalPrefixPolynomial q X chi t -
          bhpVerticalLineIntegral chi (X : ℝ) t
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ ≤
        C319 * (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
          1 / Real.sqrt (X : ℝ)) := by
    simpa using hperron
  have hx0one : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hx0one
  have hdelta : 0 < canonicalRamachandraOffset x0 := by
    unfold canonicalRamachandraOffset
    positivity
  have hdc : canonicalRamachandraOffset x0 ≤
      (1 / 2 : ℝ) + (Real.log x0)⁻¹ := by
    have : canonicalRamachandraOffset x0 ≤ (Real.log x0)⁻¹ := by
      unfold canonicalRamachandraOffset
      have hden : Real.log x0 ≤ 400 * Real.log x0 := by nlinarith
      have hi := one_div_le_one_div_of_le hlog hden
      simpa [one_div] using hi
    exact this.trans (le_add_of_nonneg_left (by norm_num))
  have hcontour := bhpRightLine_eq_correctedLeft_sub_horizontal
    chi hchi hXpos hdelta hdc hTwoT0
      (X := (X : ℝ)) (t := t)
      (c := (1 / 2 : ℝ) + (Real.log x0)⁻¹)
      (H := 2 * T)
  have hrightNorm :
      ‖bhpVerticalLineIntegral chi (X : ℝ) t
          ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ ≤
        ‖shiftedLeftLineIntegral chi (X : ℝ)
            (canonicalRamachandraOffset x0) (2 * T) t‖ +
          ‖bhpHorizontalBoundaryIntegral chi (X : ℝ) t
            (canonicalRamachandraOffset x0)
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ := by
    rw [hcontour]
    exact norm_sub_le _ _
  have hleft := MAPBHPCorrectedPerronKernel.norm_scaledAmbientOffsetLeftLineIntegral_le
    chi (A := (400 : ℝ)) (X := (X : ℝ)) (T := 2 * T)
      (t := t) (x0 := x0) (by norm_num) hXreal hXx hTwoT0
  have hleft' :
      ‖shiftedLeftLineIntegral chi (X : ℝ)
          (canonicalRamachandraOffset x0) (2 * T) t‖ ≤
        (Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
            (2 * Real.pi)) *
          perronConvolution
            (shiftedCriticalLineLNorm chi
              (canonicalRamachandraOffset x0)) (2 * T) t := by
    simpa [canonicalRamachandraOffset] using hleft
  have hhorizontal :=
    norm_bhpHorizontalBoundaryIntegral_titchmarshCanonical_le
      chi hchi hx0 hXpos hT
        (X := (X : ℝ)) (x0 := x0) (t := t) (T := T)
  have hprefixSplit :
      criticalPrefixPolynomial q X chi t =
        (criticalPrefixPolynomial q X chi t -
          bhpVerticalLineIntegral chi (X : ℝ) t
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)) +
        bhpVerticalLineIntegral chi (X : ℝ) t
          ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T) := by ring
  rw [hprefixSplit]
  calc
    ‖(criticalPrefixPolynomial q X chi t -
          bhpVerticalLineIntegral chi (X : ℝ) t
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)) +
        bhpVerticalLineIntegral chi (X : ℝ) t
          ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ ≤
      ‖criticalPrefixPolynomial q X chi t -
          bhpVerticalLineIntegral chi (X : ℝ) t
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ +
        ‖bhpVerticalLineIntegral chi (X : ℝ) t
          ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ := norm_add_le _ _
    _ ≤ C319 *
          (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
            1 / Real.sqrt (X : ℝ)) +
        (‖shiftedLeftLineIntegral chi (X : ℝ)
            (canonicalRamachandraOffset x0) (2 * T) t‖ +
          ‖bhpHorizontalBoundaryIntegral chi (X : ℝ) t
            (canonicalRamachandraOffset x0)
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖) :=
      add_le_add hperronC hrightNorm
    _ ≤ C319 *
          (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
            1 / Real.sqrt (X : ℝ)) +
        ((Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
            (2 * Real.pi)) *
          perronConvolution
            (shiftedCriticalLineLNorm chi
              (canonicalRamachandraOffset x0)) (2 * T) t +
          (‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
          (((ambientHorizontalGeneralEndpointNumerator q
                (canonicalRamachandraOffset x0) (Real.log x0)⁻¹
                (canonicalRamachandraOffset x0) (X : ℝ) (t + 2 * T) /
                  (2 * T)) +
            (ambientHorizontalGeneralEndpointNumerator q
                (canonicalRamachandraOffset x0) (Real.log x0)⁻¹
                (canonicalRamachandraOffset x0) (X : ℝ) (t - 2 * T) /
                  (2 * T))) *
              (1 / 2 + (Real.log x0)⁻¹ -
                canonicalRamachandraOffset x0)))) := by
      exact add_le_add (le_refl _) (add_le_add hleft' hhorizontal)
    _ = _ := by ring

/-- Clean source-facing nonprincipal bound after the exact horizontal
endpoint numerators are collapsed.  All logarithmic losses and absolute
constants remain visible. -/
theorem norm_criticalPrefixPolynomial_le_canonicalPolylog
    {q X : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) {t T x0 : ℝ}
    (hX : 2 ≤ X) (hT : 1 ≤ T) (hx0 : 8 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hXx : (X : ℝ) ≤ x0)
    (hTx : T ≤ x0) (hTwoTx : 2 * T ≤ x0) (ht : |t| ≤ T) :
    ‖criticalPrefixPolynomial q X chi t‖ ≤
      canonicalTitchmarshConstant *
          (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
            1 / Real.sqrt (X : ℝ)) +
        (Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
            (2 * Real.pi)) *
          perronConvolution
            (shiftedCriticalLineLNorm chi
              (canonicalRamachandraOffset x0)) (2 * T) t +
        ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
          (20000 * (1 + Real.log x0) ^ 2 * Real.exp 9 *
            (4 * Real.sqrt (q : ℝ) / Real.sqrt T +
              Real.sqrt (X : ℝ) / T)) := by
  have hXreal : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : 0 < (X : ℝ) := by positivity
  have hTwoT : 2 ≤ 2 * T := by linarith
  have hTwoT0 : 0 ≤ 2 * T := by linarith
  let C319 : ℝ := canonicalTitchmarshConstant
  have hperron := canonicalTitchmarshBound q X chi t (2 * T) x0
    hX hTwoT hqx hXx hTwoTx
  have hx0one : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hx0one
  have hdelta : 0 < canonicalRamachandraOffset x0 := by
    unfold canonicalRamachandraOffset
    positivity
  have hdc : canonicalRamachandraOffset x0 ≤
      (1 / 2 : ℝ) + (Real.log x0)⁻¹ := by
    have hdle : canonicalRamachandraOffset x0 ≤ (Real.log x0)⁻¹ := by
      unfold canonicalRamachandraOffset
      have hden : Real.log x0 ≤ 400 * Real.log x0 := by nlinarith
      have hi := one_div_le_one_div_of_le hlog hden
      simpa [one_div] using hi
    exact hdle.trans (le_add_of_nonneg_left (by norm_num))
  have hcontour := bhpRightLine_eq_correctedLeft_sub_horizontal
    chi hchi hXpos hdelta hdc hTwoT0
      (X := (X : ℝ)) (t := t)
      (c := (1 / 2 : ℝ) + (Real.log x0)⁻¹) (H := 2 * T)
  have hrightNorm :
      ‖bhpVerticalLineIntegral chi (X : ℝ) t
          ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ ≤
        ‖shiftedLeftLineIntegral chi (X : ℝ)
            (canonicalRamachandraOffset x0) (2 * T) t‖ +
          ‖bhpHorizontalBoundaryIntegral chi (X : ℝ) t
            (canonicalRamachandraOffset x0)
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ := by
    rw [hcontour]
    exact norm_sub_le _ _
  have hleftRaw :=
    MAPBHPCorrectedPerronKernel.norm_scaledAmbientOffsetLeftLineIntegral_le
      chi (A := (400 : ℝ)) (X := (X : ℝ)) (T := 2 * T)
        (t := t) (x0 := x0) (by norm_num) hXreal hXx hTwoT0
  have hleft :
      ‖shiftedLeftLineIntegral chi (X : ℝ)
          (canonicalRamachandraOffset x0) (2 * T) t‖ ≤
        (Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
            (2 * Real.pi)) *
          perronConvolution
            (shiftedCriticalLineLNorm chi
              (canonicalRamachandraOffset x0)) (2 * T) t := by
    simpa [canonicalRamachandraOffset] using hleftRaw
  have hhorizontal :=
    norm_bhpHorizontalBoundaryIntegral_titchmarshCanonical_polylog_le
      chi hchi hx0 hXpos hXx hqx hT hTx ht
        (X := (X : ℝ)) (x0 := x0) (t := t) (T := T)
  have hprefixSplit :
      criticalPrefixPolynomial q X chi t =
        (criticalPrefixPolynomial q X chi t -
          bhpVerticalLineIntegral chi (X : ℝ) t
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)) +
        bhpVerticalLineIntegral chi (X : ℝ) t
          ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T) := by ring
  rw [hprefixSplit]
  calc
    ‖(criticalPrefixPolynomial q X chi t -
          bhpVerticalLineIntegral chi (X : ℝ) t
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)) +
        bhpVerticalLineIntegral chi (X : ℝ) t
          ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ ≤
      ‖criticalPrefixPolynomial q X chi t -
          bhpVerticalLineIntegral chi (X : ℝ) t
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ +
        ‖bhpVerticalLineIntegral chi (X : ℝ) t
          ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖ := norm_add_le _ _
    _ ≤ C319 *
          (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
            1 / Real.sqrt (X : ℝ)) +
        (‖shiftedLeftLineIntegral chi (X : ℝ)
            (canonicalRamachandraOffset x0) (2 * T) t‖ +
          ‖bhpHorizontalBoundaryIntegral chi (X : ℝ) t
            (canonicalRamachandraOffset x0)
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) (2 * T)‖) :=
      add_le_add hperron hrightNorm
    _ ≤ C319 *
          (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
            1 / Real.sqrt (X : ℝ)) +
        ((Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
            (2 * Real.pi)) *
          perronConvolution
            (shiftedCriticalLineLNorm chi
              (canonicalRamachandraOffset x0)) (2 * T) t +
          (‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
            (20000 * (1 + Real.log x0) ^ 2 * Real.exp 9 *
              (4 * Real.sqrt (q : ℝ) / Real.sqrt T +
                Real.sqrt (X : ℝ) / T)))) := by
      exact add_le_add (le_refl _) (add_le_add hleft hhorizontal)
    _ = _ := by ring

/-- Universal constant in the compact nonprincipal pointwise source. -/
def canonicalNonprincipalPointwiseConstant : ℝ :=
  2 * canonicalTitchmarshConstant +
    401 * Real.exp (1 / 400 : ℝ) / (2 * Real.pi) +
    ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
      (80000 * Real.exp 9)

theorem canonicalNonprincipalPointwiseConstant_pos :
    0 < canonicalNonprincipalPointwiseConstant := by
  unfold canonicalNonprincipalPointwiseConstant
  have := canonicalTitchmarshConstant_pos
  positivity

/-- Compact nonprincipal source in the form needed by the fourth-moment
reduction.  The fixed power `2` absorbs every contour and Titchmarsh loss,
and the same universal constant works for every modulus, prefix and point. -/
theorem norm_criticalPrefixPolynomial_le_globalPolylog
    {q X : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) {t T x0 : ℝ}
    (hX : 2 ≤ X) (hT : 1 ≤ T) (hx0 : 8 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hXx : (X : ℝ) ≤ x0)
    (hTx0 : T ≤ x0) (hTwoTx : 2 * T ≤ x0)
    (hTX : T ≤ (X : ℝ)) (ht : |t| ≤ T) :
    ‖criticalPrefixPolynomial q X chi t‖ ≤
      canonicalNonprincipalPointwiseConstant *
        (1 + Real.log x0) ^ 2 *
        (perronConvolution
            (shiftedCriticalLineLNorm chi
              (canonicalRamachandraOffset x0)) (2 * T) t +
          Real.sqrt (q : ℝ) / Real.sqrt T +
          Real.sqrt (X : ℝ) / T) := by
  let C319 : ℝ := canonicalTitchmarshConstant
  have hC319 : 0 < C319 := canonicalTitchmarshConstant_pos
  have hpoint := norm_criticalPrefixPolynomial_le_canonicalPolylog
    chi hchi hX hT hx0 hqx hXx hTx0 hTwoTx ht
  let P0 : ℝ := ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖
  let Kleft : ℝ := 401 * Real.exp (1 / 400 : ℝ) / (2 * Real.pi)
  let Khoriz : ℝ := P0 * (80000 * Real.exp 9)
  let C : ℝ := 2 * C319 + Kleft + Khoriz
  have hP0 : 0 ≤ P0 := by dsimp [P0]; positivity
  have hKleft : 0 < Kleft := by dsimp [Kleft]; positivity
  have hKhoriz : 0 ≤ Khoriz := by dsimp [Khoriz]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  change ‖criticalPrefixPolynomial q X chi t‖ ≤
    C * (1 + Real.log x0) ^ 2 *
      (perronConvolution
          (shiftedCriticalLineLNorm chi
            (canonicalRamachandraOffset x0)) (2 * T) t +
        Real.sqrt (q : ℝ) / Real.sqrt T +
        Real.sqrt (X : ℝ) / T)
  refine hpoint.trans ?_
  let L1 : ℝ := 1 + Real.log x0
  let V : ℝ := perronConvolution
      (shiftedCriticalLineLNorm chi (canonicalRamachandraOffset x0))
        (2 * T) t
  let a : ℝ := Real.sqrt (q : ℝ) / Real.sqrt T
  let b : ℝ := Real.sqrt (X : ℝ) / T
  have hx0one : 1 < x0 := by linarith
  have hlog0 : 0 ≤ Real.log x0 := Real.log_nonneg (by linarith)
  have hL1 : 1 ≤ L1 := by dsimp [L1]; linarith
  have hL10 : 0 ≤ L1 := zero_le_one.trans hL1
  have hV : 0 ≤ V := by
    dsimp [V]
    exact perronConvolution_nonneg (fun _ => norm_nonneg _) (by linarith)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hTpos : 0 < T := by linarith
  have hXpos : 0 < (X : ℝ) := by positivity
  have hsqrtX : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.2 hXpos
  have hinvX : 1 / Real.sqrt (X : ℝ) ≤ b := by
    dsimp [b]
    rw [div_le_div_iff₀ hsqrtX hTpos]
    have hsqrtSq : Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) = (X : ℝ) := by
      simpa [pow_two] using Real.sq_sqrt hXpos.le
    simpa [hsqrtSq] using hTX
  have hlogTerm : Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) ≤
      L1 ^ 2 * b := by
    dsimp [L1, b]
    have hhalf : Real.sqrt (X : ℝ) / (2 * T) ≤
        Real.sqrt (X : ℝ) / T := by
      gcongr
      linarith
    calc
      Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) =
          Real.log x0 * (Real.sqrt (X : ℝ) / (2 * T)) := by ring
      _ ≤ Real.log x0 * (Real.sqrt (X : ℝ) / T) :=
        mul_le_mul_of_nonneg_left hhalf hlog0
      _ ≤ (1 + Real.log x0) ^ 2 *
          (Real.sqrt (X : ℝ) / T) := by
        have hc : Real.log x0 ≤ (1 + Real.log x0) ^ 2 := by
          nlinarith [sq_nonneg (Real.log x0)]
        exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hperronError :
      C319 * (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
        1 / Real.sqrt (X : ℝ)) ≤
      (2 * C319) * L1 ^ 2 * b := by
    have hinvXL : 1 / Real.sqrt (X : ℝ) ≤ L1 ^ 2 * b :=
      hinvX.trans (by
        have : 1 ≤ L1 ^ 2 := by nlinarith [sq_nonneg L1]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right this hb)
    have hsum := add_le_add hlogTerm hinvXL
    have hC0 : 0 ≤ C319 := hC319.le
    calc
      C319 * (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
          1 / Real.sqrt (X : ℝ)) ≤
        C319 * (L1 ^ 2 * b + L1 ^ 2 * b) :=
          mul_le_mul_of_nonneg_left hsum hC0
      _ = (2 * C319) * L1 ^ 2 * b := by ring
  have hleftCoeff :
      Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
          (2 * Real.pi) ≤ Kleft * L1 := by
    have hpoly : 1 + 400 * Real.log x0 ≤ 401 * L1 := by
      dsimp [L1]
      nlinarith
    dsimp [Kleft]
    have hden : 0 ≤ 2 * Real.pi := by positivity
    calc
      Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
          (2 * Real.pi) ≤
        Real.exp (1 / 400 : ℝ) * (401 * L1) / (2 * Real.pi) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le) hden
      _ = 401 * Real.exp (1 / 400 : ℝ) / (2 * Real.pi) * L1 := by ring
  have hleftTerm :
      (Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
          (2 * Real.pi)) * V ≤ Kleft * L1 ^ 2 * V := by
    calc
      _ ≤ (Kleft * L1) * V :=
        mul_le_mul_of_nonneg_right hleftCoeff hV
      _ ≤ (Kleft * L1 ^ 2) * V := by
        have hLL : L1 ≤ L1 ^ 2 := by nlinarith [sq_nonneg (L1 - 1)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLL hKleft.le) hV
      _ = Kleft * L1 ^ 2 * V := by ring
  have hhorizontalTerm :
      P0 * (20000 * L1 ^ 2 * Real.exp 9 * (4 * a + b)) ≤
        Khoriz * L1 ^ 2 * (a + b) := by
    have hab : 4 * a + b ≤ 4 * (a + b) := by linarith
    dsimp [Khoriz]
    calc
      P0 * (20000 * L1 ^ 2 * Real.exp 9 * (4 * a + b)) ≤
        P0 * (20000 * L1 ^ 2 * Real.exp 9 * (4 * (a + b))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hab (by positivity)) hP0
      _ = (P0 * (80000 * Real.exp 9)) * L1 ^ 2 * (a + b) := by ring
  have hcomponents :
      (2 * C319) * L1 ^ 2 * b +
          (Kleft * L1 ^ 2 * V + Khoriz * L1 ^ 2 * (a + b)) ≤
        C * L1 ^ 2 * (V + a + b) := by
    have h2C : 0 ≤ 2 * C319 := by positivity
    have hscale : 0 ≤ L1 ^ 2 := sq_nonneg _
    dsimp [C]
    nlinarith [mul_nonneg hscale hV, mul_nonneg hscale ha,
      mul_nonneg hscale hb, mul_nonneg hKleft.le hscale,
      mul_nonneg hKhoriz hscale]
  have hhorizontalTerm' :
      ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
          (20000 * (1 + Real.log x0) ^ 2 * Real.exp 9 *
            (4 * Real.sqrt (q : ℝ) / Real.sqrt T +
              Real.sqrt (X : ℝ) / T)) ≤
        Khoriz * (1 + Real.log x0) ^ 2 *
          (Real.sqrt (q : ℝ) / Real.sqrt T +
            Real.sqrt (X : ℝ) / T) := by
    convert hhorizontalTerm using 1 <;> dsimp only [P0, L1, a, b] <;> ring
  calc
    (C319 *
          (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
            1 / Real.sqrt (X : ℝ)) +
        Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
          (2 * Real.pi) *
          perronConvolution
            (shiftedCriticalLineLNorm chi
              (canonicalRamachandraOffset x0)) (2 * T) t) +
      ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
        (20000 * (1 + Real.log x0) ^ 2 * Real.exp 9 *
          (4 * Real.sqrt (q : ℝ) / Real.sqrt T +
            Real.sqrt (X : ℝ) / T)) ≤
      ((2 * C319) * (1 + Real.log x0) ^ 2 *
          (Real.sqrt (X : ℝ) / T) +
        Kleft * (1 + Real.log x0) ^ 2 *
          perronConvolution
            (shiftedCriticalLineLNorm chi
              (canonicalRamachandraOffset x0)) (2 * T) t) +
        Khoriz * (1 + Real.log x0) ^ 2 *
          (Real.sqrt (q : ℝ) / Real.sqrt T + Real.sqrt (X : ℝ) / T) :=
      add_le_add (add_le_add hperronError hleftTerm) hhorizontalTerm'
    _ = (2 * C319) * (1 + Real.log x0) ^ 2 *
          (Real.sqrt (X : ℝ) / T) +
        (Kleft * (1 + Real.log x0) ^ 2 *
            perronConvolution
              (shiftedCriticalLineLNorm chi
                (canonicalRamachandraOffset x0)) (2 * T) t +
          Khoriz * (1 + Real.log x0) ^ 2 *
            (Real.sqrt (q : ℝ) / Real.sqrt T +
              Real.sqrt (X : ℝ) / T)) := by ring
    _ ≤ _ := by
      simpa only [V, a, b, L1, P0] using hcomponents

/-- Source-faithful compact bound with the literal Titchmarsh
`1/sqrt X` error retained.  Unlike the convenience theorem above, this form
does not assume `T <= X` and therefore matches the actual MRT prefix range. -/
theorem norm_criticalPrefixPolynomial_le_globalPolylog_literal
    {q X : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) {t T x0 : ℝ}
    (hX : 2 ≤ X) (hT : 1 ≤ T) (hx0 : 8 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hXx : (X : ℝ) ≤ x0)
    (hTx0 : T ≤ x0) (hTwoTx : 2 * T ≤ x0)
    (ht : |t| ≤ T) :
    ‖criticalPrefixPolynomial q X chi t‖ ≤
      canonicalNonprincipalPointwiseConstant *
        (1 + Real.log x0) ^ 2 *
        (perronConvolution
            (shiftedCriticalLineLNorm chi
              (canonicalRamachandraOffset x0)) (2 * T) t +
          Real.sqrt (q : ℝ) / Real.sqrt T +
          Real.sqrt (X : ℝ) / T + 1 / Real.sqrt (X : ℝ)) := by
  let C319 : ℝ := canonicalTitchmarshConstant
  let P0 : ℝ := ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖
  let Kleft : ℝ := 401 * Real.exp (1 / 400 : ℝ) / (2 * Real.pi)
  let Khoriz : ℝ := P0 * (80000 * Real.exp 9)
  let C : ℝ := 2 * C319 + Kleft + Khoriz
  let L1 : ℝ := 1 + Real.log x0
  let V : ℝ := perronConvolution
      (shiftedCriticalLineLNorm chi (canonicalRamachandraOffset x0))
        (2 * T) t
  let a : ℝ := Real.sqrt (q : ℝ) / Real.sqrt T
  let b : ℝ := Real.sqrt (X : ℝ) / T
  let d : ℝ := 1 / Real.sqrt (X : ℝ)
  have hpoint := norm_criticalPrefixPolynomial_le_canonicalPolylog
    chi hchi hX hT hx0 hqx hXx hTx0 hTwoTx ht
  have hpoint' :
      ‖criticalPrefixPolynomial q X chi t‖ ≤
        (C319 *
            (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
              1 / Real.sqrt (X : ℝ)) +
          Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
            (2 * Real.pi) * V) +
        P0 * (20000 * L1 ^ 2 * Real.exp 9 * (4 * a + b)) := by
    convert hpoint using 1 <;>
      dsimp only [C319, P0, L1, V, a, b] <;> ring
  have hC319 : 0 < C319 := canonicalTitchmarshConstant_pos
  have hP0 : 0 ≤ P0 := by dsimp [P0]; positivity
  have hKleft : 0 < Kleft := by dsimp [Kleft]; positivity
  have hKhoriz : 0 ≤ Khoriz := by dsimp [Khoriz]; positivity
  have hx0one : 1 < x0 := by linarith
  have hlog0 : 0 ≤ Real.log x0 := Real.log_nonneg (by linarith)
  have hL1 : 1 ≤ L1 := by dsimp [L1]; linarith
  have hL10 : 0 ≤ L1 := zero_le_one.trans hL1
  have hV : 0 ≤ V := by
    dsimp [V]
    exact perronConvolution_nonneg (fun _ => norm_nonneg _) (by linarith)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hlogTerm : Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) ≤
      L1 ^ 2 * b := by
    dsimp [L1, b]
    have hhalf : Real.sqrt (X : ℝ) / (2 * T) ≤
        Real.sqrt (X : ℝ) / T := by
      gcongr
      linarith
    calc
      Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) =
          Real.log x0 * (Real.sqrt (X : ℝ) / (2 * T)) := by ring
      _ ≤ Real.log x0 * (Real.sqrt (X : ℝ) / T) :=
        mul_le_mul_of_nonneg_left hhalf hlog0
      _ ≤ (1 + Real.log x0) ^ 2 *
          (Real.sqrt (X : ℝ) / T) := by
        have hc : Real.log x0 ≤ (1 + Real.log x0) ^ 2 := by
          nlinarith [sq_nonneg (Real.log x0)]
        exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hdL : d ≤ L1 ^ 2 * d := by
    have hsq : 1 ≤ L1 ^ 2 := by nlinarith [sq_nonneg L1]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq hd
  have hperronError :
      C319 * (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
        1 / Real.sqrt (X : ℝ)) ≤
      (2 * C319) * L1 ^ 2 * (b + d) := by
    have hsum := add_le_add hlogTerm hdL
    calc
      C319 * (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
          1 / Real.sqrt (X : ℝ)) ≤
        C319 * (L1 ^ 2 * b + L1 ^ 2 * d) :=
          mul_le_mul_of_nonneg_left hsum hC319.le
      _ ≤ (2 * C319) * L1 ^ 2 * (b + d) := by
        have hnon : 0 ≤ C319 * L1 ^ 2 * (b + d) := by positivity
        calc
          C319 * (L1 ^ 2 * b + L1 ^ 2 * d) =
              C319 * L1 ^ 2 * (b + d) := by ring
          _ ≤ 2 * (C319 * L1 ^ 2 * (b + d)) := by linarith
          _ = _ := by ring
  have hleftCoeff :
      Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
          (2 * Real.pi) ≤ Kleft * L1 := by
    have hpoly : 1 + 400 * Real.log x0 ≤ 401 * L1 := by
      dsimp [L1]
      nlinarith
    dsimp [Kleft]
    calc
      Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
          (2 * Real.pi) ≤
        Real.exp (1 / 400 : ℝ) * (401 * L1) / (2 * Real.pi) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le)
            (by positivity)
      _ = 401 * Real.exp (1 / 400 : ℝ) / (2 * Real.pi) * L1 := by ring
  have hleftTerm :
      (Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
          (2 * Real.pi)) * V ≤ Kleft * L1 ^ 2 * V := by
    calc
      _ ≤ (Kleft * L1) * V :=
        mul_le_mul_of_nonneg_right hleftCoeff hV
      _ ≤ (Kleft * L1 ^ 2) * V := by
        have hLL : L1 ≤ L1 ^ 2 := by nlinarith [sq_nonneg (L1 - 1)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLL hKleft.le) hV
      _ = Kleft * L1 ^ 2 * V := by ring
  have hhorizontalTerm :
      P0 * (20000 * L1 ^ 2 * Real.exp 9 * (4 * a + b)) ≤
        Khoriz * L1 ^ 2 * (a + b) := by
    have hab : 4 * a + b ≤ 4 * (a + b) := by linarith
    dsimp [Khoriz]
    calc
      P0 * (20000 * L1 ^ 2 * Real.exp 9 * (4 * a + b)) ≤
        P0 * (20000 * L1 ^ 2 * Real.exp 9 * (4 * (a + b))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hab (by positivity)) hP0
      _ = (P0 * (80000 * Real.exp 9)) * L1 ^ 2 * (a + b) := by ring
  have hcomponents :
      (2 * C319) * L1 ^ 2 * (b + d) +
          (Kleft * L1 ^ 2 * V + Khoriz * L1 ^ 2 * (a + b)) ≤
        C * L1 ^ 2 * (V + a + b + d) := by
    have hscale : 0 ≤ L1 ^ 2 := sq_nonneg _
    dsimp [C]
    nlinarith [mul_nonneg hscale hV, mul_nonneg hscale ha,
      mul_nonneg hscale hb, mul_nonneg hscale hd,
      mul_nonneg hKleft.le hscale, mul_nonneg hKhoriz hscale,
      hC319.le]
  change ‖criticalPrefixPolynomial q X chi t‖ ≤
    C * L1 ^ 2 * (V + a + b + d)
  refine hpoint'.trans ?_
  calc
    (C319 *
          (Real.log x0 * Real.sqrt (X : ℝ) / (2 * T) +
            1 / Real.sqrt (X : ℝ)) +
        Real.exp (1 / 400 : ℝ) * (1 + 400 * Real.log x0) /
          (2 * Real.pi) * V) +
      P0 * (20000 * L1 ^ 2 * Real.exp 9 * (4 * a + b)) ≤
      ((2 * C319) * L1 ^ 2 * (b + d) +
        Kleft * L1 ^ 2 * V) + Khoriz * L1 ^ 2 * (a + b) :=
      add_le_add (add_le_add hperronError hleftTerm) hhorizontalTerm
    _ = (2 * C319) * L1 ^ 2 * (b + d) +
        (Kleft * L1 ^ 2 * V + Khoriz * L1 ^ 2 * (a + b)) := by ring
    _ ≤ C * L1 ^ 2 * (V + a + b + d) := hcomponents

/-- Existential compatibility wrapper for callers using the earlier API. -/
theorem exists_norm_criticalPrefixPolynomial_le_globalPolylog
    {q X : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) {t T x0 : ℝ}
    (hX : 2 ≤ X) (hT : 1 ≤ T) (hx0 : 8 ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hXx : (X : ℝ) ≤ x0)
    (hTx0 : T ≤ x0) (hTwoTx : 2 * T ≤ x0)
    (hTX : T ≤ (X : ℝ)) (ht : |t| ≤ T) :
    ∃ C : ℝ, 0 < C ∧
      ‖criticalPrefixPolynomial q X chi t‖ ≤
        C * (1 + Real.log x0) ^ 2 *
          (perronConvolution
              (shiftedCriticalLineLNorm chi
                (canonicalRamachandraOffset x0)) (2 * T) t +
            Real.sqrt (q : ℝ) / Real.sqrt T +
            Real.sqrt (X : ℝ) / T) := by
  exact ⟨canonicalNonprincipalPointwiseConstant,
    canonicalNonprincipalPointwiseConstant_pos,
    norm_criticalPrefixPolynomial_le_globalPolylog chi hchi hX hT hx0
      hqx hXx hTx0 hTwoTx hTX ht⟩

end
end MAPBHPCanonicalNonprincipalPointwise

#print axioms MAPBHPCanonicalNonprincipalPointwise.norm_criticalPrefixPolynomial_le_canonicalContour
#print axioms MAPBHPCanonicalNonprincipalPointwise.norm_criticalPrefixPolynomial_le_canonicalPolylog
#print axioms MAPBHPCanonicalNonprincipalPointwise.norm_criticalPrefixPolynomial_le_globalPolylog
#print axioms MAPBHPCanonicalNonprincipalPointwise.norm_criticalPrefixPolynomial_le_globalPolylog_literal
#print axioms MAPBHPCanonicalNonprincipalPointwise.exists_norm_criticalPrefixPolynomial_le_globalPolylog
