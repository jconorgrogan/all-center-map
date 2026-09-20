import GuthMaynardLemma92UnequalScaleWeld
import GuthMaynardJIterationEllRestrictionWeld

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-!
# Unequal-scale large-ell Lemma 9.2 weld

The first-Poisson affine scale `M₃` remains independent of the second-Poisson
scale `M₂=M`.  The discarded-frequency denominator is therefore kept in its
literal form `M₂(RT/M₂-B/M₃)`; it is not simplified using a false equality of
scales.
-/
/-- Variable-radius version used for the source's subpower ell cutoff. -/
theorem sigmaIIEllRetainedFinite_const_one_le_sourceBump_radius_unequalScale
    (ellRange m2Range : Finset ℤ) (fhat : ℝ → ℂ)
    {M : ℕ} (hM : 0 < M) {T Ctau R M3 : ℝ}
    (hT : 0 < T) (hCtau : 0 ≤ Ctau) (hR : 0 < R) :
    sigmaIIEllRetainedFinite ellRange m2Range
        (R * T / (M : ℝ)) (fun _ => 1) fhat
        (M : ℝ) T M3 Ctau ≤
      sigmaIIFinite (sourceBumpEllRange M T R) m2Range
        (fun x => sourceBump R hR x) fhat
        (M : ℝ) T M3 Ctau := by
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  let retained := ellRange.filter fun ell : ℤ =>
    |(ell : ℝ)| < R * T / (M : ℝ)
  have hsubset : retained ⊆ sourceBumpEllRange M T R := by
    intro ell hell
    have hell' := (Finset.mem_filter.mp hell).2
    apply mem_sourceIntegerWindow_zero_of_abs_le
    have hratio : 0 < R * T / (M : ℝ) := by positivity
    have : |(ell : ℝ)| ≤ 2 * R * T / (M : ℝ) := by
      calc
        |(ell : ℝ)| ≤ R * T / (M : ℝ) := hell'.le
        _ ≤ 2 * R * T / (M : ℝ) := by
          rw [show 2 * R * T / (M : ℝ) =
            2 * (R * T / (M : ℝ)) by ring]
          linarith
    simpa only [sourceBumpEllRange] using this
  have hplateau : ∀ ell ∈ retained,
      sourceBump R hR ((M : ℝ) * (ell : ℝ) / T) = 1 := by
    intro ell hell
    have hell' := (Finset.mem_filter.mp hell).2
    apply sourceBump_eq_one_of_abs_le
    have hscaled :
        |(M : ℝ) * (ell : ℝ) / T| =
          (M : ℝ) * |(ell : ℝ)| / T := by
      rw [abs_div, abs_mul, abs_of_pos hMreal, abs_of_pos hT]
    rw [hscaled]
    have hmul : (M : ℝ) * |(ell : ℝ)| < R * T := by
      have := (lt_div_iff₀ hMreal).mp hell'
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    exact ((div_lt_iff₀ hT).2 hmul).le
  unfold sigmaIIEllRetainedFinite sigmaIIFinite
  change (∑ ell ∈ retained,
      (1 : ℝ) * ∫ tau in -Ctau..Ctau,
        ‖∑ m2 ∈ m2Range,
          sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2) ≤ _
  calc
    (∑ ell ∈ retained,
        (1 : ℝ) * ∫ tau in -Ctau..Ctau,
          ‖∑ m2 ∈ m2Range,
            sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2) =
      ∑ ell ∈ retained,
        sourceBump R hR ((M : ℝ) * (ell : ℝ) / T) *
          ∫ tau in -Ctau..Ctau,
            ‖∑ m2 ∈ m2Range,
              sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro ell hell
        rw [hplateau ell hell]
    _ ≤ ∑ ell ∈ sourceBumpEllRange M T R,
        sourceBump R hR ((M : ℝ) * (ell : ℝ) / T) *
          ∫ tau in -Ctau..Ctau,
            ‖∑ m2 ∈ m2Range,
              sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro ell hellSmall hellNotRetained
        exact mul_nonneg (sourceBump_nonneg R hR _)
          (intervalIntegral.integral_nonneg (by linarith) fun tau htau =>
            sq_nonneg _)


/-- Exact discarded-ell cost with independent `M₂` and `M₃`. -/
def sourceLemma92EllTailCostRadiusUnequal
    (ellRange : Finset ℤ) (M : ℕ) (M3 : ℝ)
    (T S eta C delta R : ℝ) (j : ℕ) : ℝ :=
  (ellRange.card : ℝ) * (2 * T ^ delta) *
    (((4 * (M : ℝ) + 3) * (2 * (M : ℝ)) *
      (C * T ^ eta *
        (T / ((M : ℝ) *
          (R * T / (M : ℝ) - T ^ delta / M3))) ^ j * S)) ^ 2)

/-- Variable-radius ell restriction with the literal independent affine scale. -/
theorem sigmaIIFinite_const_one_le_sourceBump_radius_add_ellTail_unequalScale
    (ellRange mRange : Finset ℤ) (fhat : ℝ → ℂ)
    {M : ℕ} (hM : 0 < M) (hmRange : mRange ⊆ sourcePositiveDyadicRange M)
    {T S eta C B R M3 : ℝ} (j : ℕ)
    (hT : 0 < T) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hB0 : 0 ≤ B) (hR : 0 < R) (hM3 : 0 < M3)
    (hgap : B / M3 < R * T / (M : ℝ))
    (hbound : ∀ z : ℝ, z ≠ 0 →
      ‖fhat z‖ ≤ C * T ^ eta * (T / |z|) ^ j * S) :
    sigmaIIFinite ellRange mRange (fun _ => 1) fhat
        (M : ℝ) T M3 B ≤
      sigmaIIFinite (sourceBumpEllRange M T R) mRange
          (fun x => sourceBump R hR x) fhat
          (M : ℝ) T M3 B +
        (ellRange.card : ℝ) * (2 * B) *
          (((4 * (M : ℝ) + 3) * (2 * (M : ℝ)) *
            (C * T ^ eta *
              (T / ((M : ℝ) *
                (R * T / (M : ℝ) - B / M3))) ^ j * S)) ^ 2) := by
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hN2 : (mRange.card : ℝ) ≤ 4 * (M : ℝ) + 3 := by
    calc
      (mRange.card : ℝ) ≤ ((sourcePositiveDyadicRange M).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hmRange
      _ ≤ 4 * (M : ℝ) + 3 := card_sourcePositiveDyadicRange_cast_le M
  have hNell :
      ((ellRange.filter fun ell : ℤ =>
        ¬ |(ell : ℝ)| < R * T / (M : ℝ)).card : ℝ) ≤
        (ellRange.card : ℝ) := by
    have hcard := Finset.card_filter_le ellRange
      (fun ell : ℤ => ¬ |(ell : ℝ)| < R * T / (M : ℝ))
    exact_mod_cast hcard
  have hfreq : 0 < (M : ℝ) *
      (R * T / (M : ℝ) - B / M3) := by positivity
  have hmlo : ∀ m ∈ mRange, (M : ℝ) ≤ |(m : ℝ)| := by
    intro m hm
    exact (sourcePositiveDyadicRange_abs_bounds hM (hmRange hm)).1
  have hmhi : ∀ m ∈ mRange, |(m : ℝ)| ≤ 2 * (M : ℝ) := by
    intro m hm
    simpa using (sourcePositiveDyadicRange_abs_bounds hM (hmRange hm)).2
  have htail := sigmaIIEllTailFinite_le
    ellRange mRange (fun _ => 1) fhat
    (T := T) (S := S) (eta := eta) (C := C)
    (M2 := (M : ℝ)) (M3 := M3) (M2lo := (M : ℝ))
    (M2hi := 2 * (M : ℝ)) (N2 := 4 * (M : ℝ) + 3)
    (L := R * T / (M : ℝ)) (Ctau := B) (P2 := 1)
    (Nell := (ellRange.card : ℝ)) j hT.le hS hC hM3
    hMreal.le (by positivity : (0 : ℝ) ≤ 2 * (M : ℝ)) hN2 hB0
    (by norm_num : (0 : ℝ) ≤ 1) hNell hfreq hmlo hmhi
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) hbound
  have hretained := sigmaIIEllRetainedFinite_const_one_le_sourceBump_radius_unequalScale
    ellRange mRange fhat hM hT hB0 hR (M3 := M3)
  rw [sigmaIIFinite_eq_ellRetained_add_tail ellRange mRange
    (R * T / (M : ℝ)) (fun _ => 1) fhat (M : ℝ) T M3 B]
  simpa [mul_assoc] using add_le_add hretained htail

/-- Full large-ell selected endpoint with the three source scales kept distinct. -/
theorem sigmaIIFinite_largeEll_selectedPositiveDyadic_variableRadius_unequalScale_le
    {T S F delta : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    {M : ℕ} (hM : 0 < M) (mRange ellRange : Finset ℤ)
    (hmRange : mRange ⊆ sourcePositiveDyadicRange M)
    (q j : ℕ) {M3 R Csecond etaTail Ctail : ℝ}
    (hR : 0 < R) (hRone : 1 ≤ R) (hM3 : 0 < M3)
    (hT : 1 ≤ T) (hF0 : 0 ≤ F) (hF : F ≤ T)
    (hMhi : (M : ℝ) ≤ T ^ 4)
    (hgap : T ^ delta / M3 < R * T / (M : ℝ))
    (hCsecond : 0 ≤ Csecond) (hCtail : 0 ≤ Ctail)
    (hFourierTail : ∀ z : ℝ, z ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
        Ctail * T ^ etaTail * (T / |z|) ^ j * S)
    (hsecondBudget :
      ((T / (M : ℝ)) *
          (R * sourceBumpFourierConstant 1 zero_lt_one (q + 2)) *
          ((1 + (4 * (M : ℝ) * F) / ((M : ℝ) / T)) ^ 2 *
            max 1 (((M : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
        Csecond * (T ^ delta) ^ q)) :
    sigmaIIFinite ellRange mRange (fun _ => 1)
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        (M : ℝ) T M3 (T ^ delta) ≤
      ((2 * T ^ delta *
          (R * sourceBumpFourierConstant 1 zero_lt_one 0)) *
          (2 : ℝ) ^ 2 * (M : ℝ)) *
          Real.sqrt ((∫ u : ℝ, f u ^ 2) *
            sourceAffineJ
              (sourceAffineConfigs (sourcePositiveDyadicRange M)
                (sourceLemma92JRange M T F (2 * T ^ delta)))
              (affineSmoothing T
                (fun z => sourceBump (T ^ delta) (by positivity) z) f)) +
        ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
          |(m2 : ℝ) * (m2' : ℝ)| *
            (((∫ u : ℝ, |f u|) ^ 2 * (2 * T ^ delta)) *
              (Csecond / T ^ 100)) +
        sourceLemma92EllTailCostRadiusUnequal ellRange M M3 T S etaTail Ctail
          delta R j := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hB0 : 0 ≤ T ^ delta := (Real.rpow_pos_of_pos hTpos delta).le
  have hell := sigmaIIFinite_const_one_le_sourceBump_radius_add_ellTail_unequalScale
    ellRange mRange
    (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) hM hmRange
    j hTpos hf.bound_nonneg hCtail hB0 hR hM3 hgap hFourierTail
  have hsmall := sigmaIIFinite_selectedPositiveDyadic_variableEllRadius_unequalScale_le
    hf hM mRange hmRange q hR hRone hM3 hT hF0 hF hMhi hB0
    hCsecond hsecondBudget
  calc
    sigmaIIFinite ellRange mRange (fun _ => 1)
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        (M : ℝ) T M3 (T ^ delta) ≤
      sigmaIIFinite (sourceBumpEllRange M T R) mRange
          (fun x => sourceBump R hR x)
          (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
          (M : ℝ) T M3 (T ^ delta) +
        sourceLemma92EllTailCostRadiusUnequal ellRange M M3 T S etaTail Ctail
          delta R j := by
            simpa [sourceLemma92EllTailCostRadiusUnequal, mul_assoc] using hell
    _ ≤ (((2 * T ^ delta *
            (R * sourceBumpFourierConstant 1 zero_lt_one 0)) *
            (2 : ℝ) ^ 2 * (M : ℝ)) *
            Real.sqrt ((∫ u : ℝ, f u ^ 2) *
              sourceAffineJ
                (sourceAffineConfigs (sourcePositiveDyadicRange M)
                  (sourceLemma92JRange M T F (2 * T ^ delta)))
                (affineSmoothing T
                  (fun z => sourceBump (T ^ delta) (by positivity) z) f)) +
          ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
            |(m2 : ℝ) * (m2' : ℝ)| *
              (((∫ u : ℝ, |f u|) ^ 2 * (2 * T ^ delta)) *
                (Csecond / T ^ 100))) +
        sourceLemma92EllTailCostRadiusUnequal ellRange M M3 T S etaTail Ctail
          delta R j := add_le_add hsmall le_rfl

#print axioms GuthMaynardJIteration.sigmaIIEllRetainedFinite_const_one_le_sourceBump_radius_unequalScale
#print axioms GuthMaynardJIteration.sigmaIIFinite_const_one_le_sourceBump_radius_add_ellTail_unequalScale
#print axioms GuthMaynardJIteration.sigmaIIFinite_largeEll_selectedPositiveDyadic_variableRadius_unequalScale_le

end GuthMaynardJIteration
