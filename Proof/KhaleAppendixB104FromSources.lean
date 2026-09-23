import KhaleAppendixBHeightCoefficientBound
import KhaleMcCurleyFinitePatch
import DirichletLFunctionConjugationGeneral
import KhaleAppendixB1HighZeroReduction
import KhaleAppendixB1PenultimateReduction
import KhaleAppendixB1LazyKeyReduction
import KhaleAppendixB1FirstPartReduction
import KhaleAppendixBFirstPartSourceReduction
import KhaleAppendixBCotangentCertified
import KhaleAppendixBZetaPointwiseCertified
import KhaleAppendixBFirstPartAnalyticReduction
import KhaleAppendixBLemma51ExpansionReduction
import KhaleAppendixBZetaPrimePowerCertified
import KhaleAppendixBLemma51EulerFourierCertified

/-!
# Khale Appendix B, Corollary B.2 from its actual source theorems

This file removes `AppendixBCorollary104` as a black-box input.  It proves the
literal closed, sign-symmetric corollary from:

* Ford's exact Hurwitz-zeta estimate with `(A,B) = (76.2,4.45)`;
* Khale's preceding Theorem B.1;
* the real-exception conclusion of McCurley Theorem 1.1.

All threshold, supremum, rounding, and negative-ordinate work is discharged
here.
-/

namespace MAPKhaleAppendixB104FromSources

open MAPKhaleAppendixBSource MAPKhaleWeakVKApplication
open MAPKhaleAppendixBHeightCoefficientBound
open MAPMcCurleyHighImaginaryBridge MAPKhaleMcCurleyFinitePatch

noncomputable section

/-- The complete high-ordinate B.1 reciprocal estimate from the sole
remaining Khale Lemma-4.1 raw input.  Lemma 5.1, cotangent, zeta, and every
subsequent numerical weld are discharged internally. -/
theorem appendixBHighZeroReciprocalEstimate_of_raw
    (hRaw :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate) :
    MAPKhaleAppendixB1HighZeroReduction.AppendixBHighZeroReciprocalEstimate :=
  MAPKhaleAppendixB1PenultimateReduction.highZeroReciprocalEstimate_of_penultimate
    (MAPKhaleAppendixB1LazyKeyReduction.penultimateEstimate_of_lazyKeyAfterZeta
      (MAPKhaleAppendixB1ZetaReduction.lazyKeyAfterZeta_of_beforeZeta_and_zetaBound
        (MAPKhaleAppendixB1FirstPartReduction.lazyKeyBeforeZeta_of_firstPart_and_cotangent
          (MAPKhaleAppendixBFirstPartSourceReduction.firstPartEstimate_of_upper
            (MAPKhaleAppendixBFirstPartAnalyticReduction.firstPartUpper_of_raw_and_lemma51
              hRaw
              (MAPKhaleAppendixBLemma51ExpansionReduction.lemma51Specialized_of_expansions_and_ford
                MAPKhaleAppendixBLemma51EulerFourierCertified.appendixBLemma51EulerFourierExpansion
                MAPKhaleAppendixBLemma51KernelCertified.fordCoshSqFourierIdentity
                MAPKhaleAppendixBZetaPrimePowerCertified.appendixBZetaPrimePowerIdentity)))
          MAPKhaleAppendixBCotangentCertified.appendixBCotangent0012)
        (MAPKhaleAppendixB1ZetaReduction.lazyZetaBound_of_pointwise06
          MAPKhaleAppendixBZetaPointwiseCertified.appendixBZetaPointwise06)))

private theorem theoremB1_startup_ratio :
    (5110.6 : ℝ) / 4.45 ≤
      Real.log (Real.exp 11450) /
        Real.log (Real.log (Real.exp 11450)) := by
  rw [Real.log_exp]
  have hlogpos : 0 < Real.log (11450 : ℝ) :=
    (by norm_num : (0 : ℝ) < 9.345).trans log_11450_gt
  apply (le_div_iff₀ hlogpos).2
  nlinarith [log_11450_lt]

private theorem theoremB1_startup_loglog :
    (183 : ℝ) / (4.45 : ℝ) ^ 2 ≤
      Real.log (Real.log (Real.exp 11450)) := by
  rw [Real.log_exp]
  have h := log_11450_gt
  norm_num at h ⊢
  linarith

private theorem high_positive_ordinate_nonvanishing
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hB1 : AppendixBTheoremB1)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {u sigma : ℝ} (hq : 3 ≤ q) (hu : Real.exp 11450 ≤ u)
    (hsigma : 1 - 1 / khaleWeakDenominatorAbs q u ≤ sigma) :
    DirichletCharacter.LFunction chi
      ((sigma : ℂ) + (u : ℂ) * Complex.I) ≠ 0 := by
  have hsource := hB1 76.2 4.45 (Real.exp 11450)
    (by norm_num) (by norm_num) (by norm_num) hFord
    (Real.exp_le_exp.mpr (by norm_num : (10650 : ℝ) ≤ 11450))
    theoremB1_startup_ratio theoremB1_startup_loglog
    q chi u sigma hq hu
  let F : ℝ := Real.rpow (Real.log u) (2 / 3 : ℝ) *
    Real.rpow (Real.log (Real.log u)) (1 / 3 : ℝ)
  let D₁ : ℝ := 18 * Real.log q +
    appendixBHeightCoefficient 76.2 (Real.exp 11450) *
      Real.rpow 4.45 (2 / 3 : ℝ) * F
  let D₂ : ℝ := 18 * Real.log q + 104 * F
  have huPos : 0 < u := (Real.exp_pos 11450).trans_le hu
  have hlogu : (11450 : ℝ) ≤ Real.log u := by
    rw [← Real.log_exp 11450]
    exact Real.log_le_log (Real.exp_pos 11450) hu
  have hloguPos : 0 < Real.log u := by linarith
  have hlogloguPos : 0 < Real.log (Real.log u) := by
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 11450) hlogu
    exact (by norm_num : (0 : ℝ) < 9.345).trans
      (log_11450_gt.trans_le hmono)
  have hFpos : 0 < F := by
    dsimp [F]
    exact mul_pos (Real.rpow_pos_of_pos hloguPos _)
      (Real.rpow_pos_of_pos hlogloguPos _)
  have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogqPos : 0 < Real.log q :=
    Real.log_pos ((by norm_num : (1 : ℝ) < 3).trans_le hqReal)
  have hcoeffNonneg :
      0 ≤ appendixBHeightCoefficient 76.2 (Real.exp 11450) := by
    unfold appendixBHeightCoefficient
    positivity
  have hD₁pos : 0 < D₁ := by
    dsimp [D₁]
    have hterm : 0 ≤
        appendixBHeightCoefficient 76.2 (Real.exp 11450) *
          Real.rpow 4.45 (2 / 3 : ℝ) * F :=
      mul_nonneg
        (mul_nonneg hcoeffNonneg (Real.rpow_nonneg (by norm_num) _)) hFpos.le
    exact add_pos_of_pos_of_nonneg (mul_pos (by norm_num) hlogqPos) hterm
  have hDlt : D₁ < D₂ := by
    dsimp [D₁, D₂]
    have hc := appendixBHeightCoefficient_mul_rpow_lt_104
    simpa only [add_comm] using!
      add_lt_add_left (mul_lt_mul_of_pos_right hc hFpos) (18 * Real.log q)
  have hboundary : 1 - 1 / D₁ < 1 - 1 / D₂ := by
    have hinv := one_div_lt_one_div_of_lt hD₁pos hDlt
    linarith
  apply hsource
  have habsu : |u| = u := abs_of_pos huPos
  have hsigmaD₂ : 1 - 1 / D₂ ≤ sigma := by
    simpa only [D₂, F, khaleWeakDenominatorAbs, khaleWeakDenominator, habsu,
      mul_assoc]
      using hsigma
  dsimp [D₁, F] at hboundary ⊢
  simp only [mul_assoc] at hboundary ⊢
  exact hboundary.trans_le hsigmaD₂

private theorem high_absolute_ordinate_nonvanishing
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hB1 : AppendixBTheoremB1)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {t sigma : ℝ} (hq : 3 ≤ q) (ht : Real.exp 11450 ≤ |t|)
    (hsigma : 1 - 1 / khaleWeakDenominatorAbs q t ≤ sigma) :
    DirichletCharacter.LFunction chi
      ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  let u := |t|
  have hu : Real.exp 11450 ≤ u := ht
  have hpositive (psi : DirichletCharacter ℂ q) :
      DirichletCharacter.LFunction psi
        ((sigma : ℂ) + (u : ℂ) * Complex.I) ≠ 0 := by
    apply high_positive_ordinate_nonvanishing hFord hB1 psi hq hu
    simpa only [u, khaleWeakDenominatorAbs, abs_abs] using hsigma
  by_cases ht0 : 0 ≤ t
  · have habs : |t| = t := abs_of_nonneg ht0
    simpa only [u, habs] using hpositive chi
  · have htneg : t < 0 := lt_of_not_ge ht0
    have habs : u = -t := by simp [u, abs_of_neg htneg]
    let s : ℂ := (sigma : ℂ) + (t : ℂ) * Complex.I
    have htne : t ≠ 0 := ne_of_lt htneg
    have hsone : s ≠ 1 := by
      intro hs
      have him : t = 0 := by
        simpa [s] using congrArg Complex.im hs
      exact htne him
    have hconj :=
      MAPDirichletLFunctionConjugationGeneral.LFunction_inv_conj_of_ne_one
        chi s hsone
    intro hzero
    apply hpositive chi⁻¹
    have hzeroConj : DirichletCharacter.LFunction chi⁻¹ (starRingEnd ℂ s) = 0 := by
      rw [hconj, hzero]
      simp
    have hsConj : starRingEnd ℂ s =
        (sigma : ℂ) + (u : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [s]
      · simp [s, habs]
    rwa [hsConj] at hzeroConj

theorem appendixBCorollary104_of_sources
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hB1 : AppendixBTheoremB1)
    (hMcCurley : McCurleyTheorem11RealException) :
    AppendixBCorollary104 := by
  intro q _inst chi t sigma hq ht hsigma
  by_cases hhigh : Real.exp 11450 ≤ |t|
  · exact high_absolute_ordinate_nonvanishing hFord hB1 chi hq hhigh hsigma
  · have htop : |t| ≤ Real.exp 11450 := le_of_not_ge hhigh
    have hden := mccurley_denominator_le_khaleWeakDenominatorAbs hq ht htop
    have hsafeDenPos : 0 < safeClosedR * Real.log (mccurleyScale q t) :=
      mul_pos (by norm_num [safeClosedR]) (log_mccurleyScale_pos q t)
    have hinv : 1 / khaleWeakDenominatorAbs q t ≤
        1 / (safeClosedR * Real.log (mccurleyScale q t)) :=
      one_div_le_one_div_of_le hsafeDenPos hden
    have hsafe : mccurleyBoundary safeClosedR q t ≤ sigma := by
      dsimp [mccurleyBoundary]
      linarith [hinv, hsigma]
    have htne : t ≠ 0 := by
      intro htzero
      subst t
      norm_num at ht
    have hresult := ne_zero_of_published_real_exception chi
      (fun psi s hregion hzero => hMcCurley q psi s hregion hzero)
      htne hsafe
    convert hresult using 1 <;> ring

/-- Appendix B.104 with Theorem B.1 opened to the precise high-zero
reciprocal estimate used by its proof.  McCurley's theorem is shared by the
B.1 height reduction and the finite-height part of Corollary B.2. -/
theorem appendixBCorollary104_of_ford_highZero_mccurley
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hHigh :
      MAPKhaleAppendixB1HighZeroReduction.AppendixBHighZeroReciprocalEstimate)
    (hMcCurley : McCurleyTheorem11RealException) :
    AppendixBCorollary104 :=
  appendixBCorollary104_of_sources hFord
    (MAPKhaleAppendixB1HighZeroReduction.appendixBTheoremB1_of_highZero_and_mccurley
      hMcCurley hHigh)
    hMcCurley

/-- Same constructor with the high-zero estimate opened through the literal
penultimate display of the B.1 proof. -/
theorem appendixBCorollary104_of_ford_penultimate_mccurley
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hPenultimate :
      MAPKhaleAppendixB1PenultimateReduction.AppendixBPenultimateZeroEstimate)
    (hMcCurley : McCurleyTheorem11RealException) :
    AppendixBCorollary104 :=
  appendixBCorollary104_of_ford_highZero_mccurley hFord
    (MAPKhaleAppendixB1PenultimateReduction.highZeroReciprocalEstimate_of_penultimate
      hPenultimate)
    hMcCurley

/-- Same constructor with the penultimate display discharged from the exact
post-zeta form of equation `(lazykey)`. -/
theorem appendixBCorollary104_of_ford_lazyKey_mccurley
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hLazy :
      MAPKhaleAppendixB1LazyKeyReduction.AppendixBLazyKeyAfterZetaEstimate)
    (hMcCurley : McCurleyTheorem11RealException) :
    AppendixBCorollary104 :=
  appendixBCorollary104_of_ford_penultimate_mccurley hFord
    (MAPKhaleAppendixB1LazyKeyReduction.penultimateEstimate_of_lazyKeyAfterZeta
      hLazy)
    hMcCurley

/-- Corollary B.2 with B.1 reduced to its exact `firstpart` inequality and
the pointwise zeta bound; the cotangent estimate is premise-free. -/
theorem appendixBCorollary104_of_ford_firstPart_zeta_mccurley
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hFirst : MAPKhaleAppendixB1FirstPartReduction.AppendixBFirstPartEstimate)
    (hZeta : MAPKhaleAppendixB1ZetaReduction.AppendixBZetaPointwise06)
    (hMcCurley : McCurleyTheorem11RealException) :
    AppendixBCorollary104 :=
  appendixBCorollary104_of_ford_lazyKey_mccurley hFord
    (MAPKhaleAppendixB1ZetaReduction.lazyKeyAfterZeta_of_beforeZeta_and_zetaBound
      (MAPKhaleAppendixB1FirstPartReduction.lazyKeyBeforeZeta_of_firstPart_and_cotangent
        hFirst MAPKhaleAppendixBCotangentCertified.appendixBCotangent0012)
      (MAPKhaleAppendixB1ZetaReduction.lazyZetaBound_of_pointwise06 hZeta))
    hMcCurley

/-- The same source descent with the already-certified fact `beta < 1`
removed from the analytic leaf. -/
theorem appendixBCorollary104_of_ford_firstPartUpper_zeta_mccurley
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hFirstUpper :
      MAPKhaleAppendixBFirstPartSourceReduction.AppendixBFirstPartUpperEstimate)
    (hZeta : MAPKhaleAppendixB1ZetaReduction.AppendixBZetaPointwise06)
    (hMcCurley : McCurleyTheorem11RealException) :
    AppendixBCorollary104 :=
  appendixBCorollary104_of_ford_firstPart_zeta_mccurley hFord
    (MAPKhaleAppendixBFirstPartSourceReduction.firstPartEstimate_of_upper hFirstUpper)
    hZeta hMcCurley

/-- Deepest current B.104 constructor.  The cotangent and sharp pointwise zeta
bounds are both premise-free; the remaining Khale B.1 input is only the
`firstpart` upper inequality. -/
theorem appendixBCorollary104_of_ford_firstPartUpper_mccurley
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hFirstUpper :
      MAPKhaleAppendixBFirstPartSourceReduction.AppendixBFirstPartUpperEstimate)
    (hMcCurley : McCurleyTheorem11RealException) :
    AppendixBCorollary104 :=
  appendixBCorollary104_of_ford_firstPartUpper_zeta_mccurley
    hFord hFirstUpper
    MAPKhaleAppendixBZetaPointwiseCertified.appendixBZetaPointwise06 hMcCurley

/-- Corollary B.2 with `(firstpart)` opened into the signed Lemma-4.1 raw
estimate and the specialized Lemma-5.1 logarithmic-integral inequality. -/
theorem appendixBCorollary104_of_ford_raw_lemma51_mccurley
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hRaw :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate)
    (h51 :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBLemma51Specialized)
    (hMcCurley : McCurleyTheorem11RealException) :
    AppendixBCorollary104 :=
  appendixBCorollary104_of_ford_firstPartUpper_mccurley hFord
    (MAPKhaleAppendixBFirstPartAnalyticReduction.firstPartUpper_of_raw_and_lemma51
      hRaw h51)
    hMcCurley

/-- The Lemma-5.1 premise opened through its literal Euler/Fourier and zeta
prime-power identities.  Ford's `cosh^{-2}` transform is retained as the
first genuine Fourier-analysis leaf. -/
theorem appendixBCorollary104_of_ford_raw_expansions_mccurley
    (hFordHurwitz : FordHurwitzEquation12 76.2 4.45)
    (hRaw :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate)
    (hEuler :
      MAPKhaleAppendixBLemma51ExpansionReduction.AppendixBLemma51EulerFourierExpansion)
    (hFourier :
      MAPKhaleAppendixBLemma51KernelCertified.FordCoshSqFourierIdentity)
    (hZetaEuler :
      MAPKhaleAppendixBLemma51ExpansionReduction.AppendixBZetaPrimePowerIdentity)
    (hMcCurley : McCurleyTheorem11RealException) :
    AppendixBCorollary104 :=
  appendixBCorollary104_of_ford_raw_lemma51_mccurley hFordHurwitz hRaw
    (MAPKhaleAppendixBLemma51ExpansionReduction.lemma51Specialized_of_expansions_and_ford
      hEuler hFourier hZetaEuler)
    hMcCurley

/-- Same descent with the zeta prime-power identity discharged internally from
Mathlib's Euler product and `-log(1-z)` Taylor series. -/
theorem appendixBCorollary104_of_ford_raw_eulerFourier_mccurley
    (hFordHurwitz : FordHurwitzEquation12 76.2 4.45)
    (hRaw :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate)
    (hEuler :
      MAPKhaleAppendixBLemma51ExpansionReduction.AppendixBLemma51EulerFourierExpansion)
    (hFourier :
      MAPKhaleAppendixBLemma51KernelCertified.FordCoshSqFourierIdentity)
    (hMcCurley : McCurleyTheorem11RealException) :
    AppendixBCorollary104 :=
  appendixBCorollary104_of_ford_raw_expansions_mccurley hFordHurwitz hRaw
    hEuler hFourier
    MAPKhaleAppendixBZetaPrimePowerCertified.appendixBZetaPrimePowerIdentity
    hMcCurley

/-- Lemma 5.1 is now fully discharged: its character Euler product, absolute
Fubini interchange, phase projection, odd-sine cancellation, zeta expansion,
and Ford `cosh^{-2}` transform are all certified internally.  The only
remaining inputs on this branch are the preceding Lemma-4.1 raw estimate,
Ford's Hurwitz-zeta bound, and McCurley's real-exception theorem. -/
theorem appendixBCorollary104_of_ford_raw_mccurley
    (hFordHurwitz : FordHurwitzEquation12 76.2 4.45)
    (hRaw :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate)
    (hMcCurley : McCurleyTheorem11RealException) :
    AppendixBCorollary104 :=
  appendixBCorollary104_of_ford_raw_expansions_mccurley hFordHurwitz hRaw
    MAPKhaleAppendixBLemma51EulerFourierCertified.appendixBLemma51EulerFourierExpansion
    MAPKhaleAppendixBLemma51KernelCertified.fordCoshSqFourierIdentity
    MAPKhaleAppendixBZetaPrimePowerCertified.appendixBZetaPrimePowerIdentity
    hMcCurley

end
end MAPKhaleAppendixB104FromSources

#print axioms MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_sources
#print axioms MAPKhaleAppendixB104FromSources.appendixBHighZeroReciprocalEstimate_of_raw
#print axioms MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_highZero_mccurley
#print axioms MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_penultimate_mccurley
#print axioms MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_lazyKey_mccurley
#print axioms MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_firstPart_zeta_mccurley
#print axioms MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_firstPartUpper_zeta_mccurley
#print axioms MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_firstPartUpper_mccurley
#print axioms MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_raw_lemma51_mccurley
#print axioms MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_raw_expansions_mccurley
#print axioms MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_raw_eulerFourier_mccurley
#print axioms MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_raw_mccurley
