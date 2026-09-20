import APRegularNearAppendixBAdapter
import PrincipalWeakVKZeroGapFromKhaleHigh
import KhaleHighZeroNonvanishingFromRaw
import KoukLowKhaleRangeWeakGap
import KhaleAppendixBFirstPartExactHeightRepair
import KhaleAppendixBLemma62NaturalScaleWeld

/-!
# Primitive regular high gap from the literal pre-McCurley Khale source

The only range in which Khale's high-zero calculation is used is
`exp(11450) <= |gamma|` and `q^(1/100000) <= |gamma|`.  On its complement,
polylogarithmic conductor makes Koukoulopoulos' reciprocal-log collar already
stronger than the weak-VK `log(X)^(-3/4)` mesh.  Thus McCurley's bounded-height
alternative and the packaged Appendix-B corollary are unnecessary for MAP.
-/

namespace MAPAPPrimitiveRegularHighGapFromFordRaw

open Filter Set DirichletZeros
open MAPKhaleAppendixBSource MAPKhaleWeakVKApplication
open MAPKhaleAppendixB1HighZeroReduction
open MAPAPRegularNearAppendixBAdapter
open MAPKoukTheorem12ThreeGlobal MAPLocalZeroWindow

noncomputable section

/-- The exact regular-high interface consumed by the all-center MAP endpoint,
from Ford's Hurwitz estimate and the repaired high-zero estimate. -/
theorem primitiveRegularHighGap_of_high_estimate
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hHighEstimate : AppendixBHighZeroReciprocalEstimate) :
    PrimitiveRegularHighGap := by
  intro K hK
  obtain ⟨cPrincipal, hcPrincipal, hPrincipal⟩ :=
    MAPPrincipalWeakVKZeroGapFromKhaleHigh.exists_eventually_principal_weakVK_gap_of_high_estimate
      hFord hHighEstimate
  let cKhale : ℝ := 1 / (18 * K + 104)
  let cKouk : ℝ :=
    1 / (100000000000 *
      (Real.log (Real.exp 11450 + 3) + 2 * K))
  let c : ℝ := min cPrincipal (min cKhale cKouk)
  have hcKhale : 0 < cKhale := by
    dsimp [cKhale]
    positivity
  have hlogConst : 0 < Real.log (Real.exp 11450 + 3) := by
    apply Real.log_pos
    nlinarith [Real.exp_pos 11450]
  have hcKouk : 0 < cKouk := by
    dsimp [cKouk]
    positivity
  have hc : 0 < c := lt_min hcPrincipal (lt_min hcKhale hcKouk)
  have hKhaleScalar :=
    weakGap_le_of_one_div_khaleWeakDenominatorAbs_le K hK.le
  have hKoukScalar :=
    MAPKoukLowKhaleRangeWeakGap.eventually_weakGap_le_koukGap_of_not_khale_high_range
      K hK
  have hlarge : ∀ᶠ X : ℝ in atTop, Real.exp 1 < X :=
    eventually_gt_atTop (Real.exp 1)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hPrincipal, hKhaleScalar, hKoukScalar, hlarge] with
      X hPrincipalX hKhaleX hKoukX hX
  intro q _inst chi hprim hqX T rho hrho hbeta hheight himX
  have hXpos : 0 < X := (Real.exp_pos 1).trans hX
  have hlogOne : 1 < Real.log X := by
    rw [Real.lt_log_iff_exp_lt hXpos]
    exact hX
  have hpowNonneg :
      0 ≤ Real.rpow (Real.log X) (-(3 / 4 : ℝ)) :=
    Real.rpow_nonneg (zero_lt_one.trans hlogOne).le _
  by_cases hchi : chi = 1
  · have hqOne : q = 1 := by
      have hcond : chi.conductor = q := hprim
      rw [hchi, DirichletCharacter.conductor_one] at hcond
      exact hcond.symm
    subst q
    subst chi
    have hglobalRect :=
      PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
        (1 : DirichletCharacter ℂ 1) 0 T hrho
    have htargetRect : rho ∈ zeroRectangle 0 X := by
      rw [zeroRectangle, Complex.mem_reProdIm]
      exact ⟨⟨by linarith, hglobalRect.1.2⟩, abs_le.mp himX⟩
    have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport
      (1 : DirichletCharacter ℂ 1) 0 T hrho
    have hrhoX : rho ∈ zeroSupport (1 : DirichletCharacter ℂ 1) 0 X :=
      (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        (1 : DirichletCharacter ℂ 1) 0 X htargetRect).mpr hzero
    have hgap := hPrincipalX X le_rfl rho hrhoX
    have hcoef : c ≤ cPrincipal := min_le_left _ _
    exact (mul_le_mul_of_nonneg_right hcoef hpowNonneg).trans hgap
  · have hqThree : 3 ≤ q :=
      three_le_level_of_isPrimitive_of_ne_one chi hprim hchi
    by_cases hKhaleRange :
        Real.exp 11450 ≤ |rho.im| ∧
          Real.rpow (q : ℝ) (1 / 100000 : ℝ) ≤ |rho.im|
    · have hzero : DirichletCharacter.LFunction chi rho = 0 :=
        MAPAPPrimitiveRegularLowGap.LFunction_eq_zero_of_mem_zeroSupport chi hrho
      have hnonzero :
          1 - 1 / khaleWeakDenominatorAbs q rho.im ≤ rho.re →
            DirichletCharacter.LFunction chi
              ((rho.re : ℂ) + (rho.im : ℂ) * Complex.I) ≠ 0 := by
        intro hboundary
        exact MAPKhaleHighZeroNonvanishingFromRaw.high_absolute_nonvanishing_of_high_estimate
          hFord hHighEstimate chi hqThree hKhaleRange.1 hKhaleRange.2 hboundary
      have hzero' : DirichletCharacter.LFunction chi
          ((rho.re : ℂ) + (rho.im : ℂ) * Complex.I) = 0 := by
        simpa [Complex.re_add_im] using hzero
      have hrecip :=
        one_div_khaleWeakDenominatorAbs_le_one_sub_sigma_of_zero
          chi (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) hheight
          hnonzero hzero'
      have hweak := hKhaleX q rho.im rho.re
        (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) hqX hheight himX hrecip
      have hcoef : c ≤ cKhale :=
        (min_le_right cPrincipal (min cKhale cKouk)).trans
          (min_le_left cKhale cKouk)
      exact (mul_le_mul_of_nonneg_right hcoef hpowNonneg).trans hweak
    · have hregular : ¬ (chi ^ 2 = 1 ∧ rho.im = 0 ∧
          zeroMultiplicity chi 0 T rho = 1) := by
        intro hbad
        rw [hbad.2.1] at hheight
        norm_num at hheight
      have hKoukGap := primitive_global_regular_zero_gap chi hprim hchi hrho
        (by linarith) hregular
      have hscalar := hKoukX q rho.im hqX hKhaleRange
      have hcoef : c ≤ cKouk :=
        (min_le_right cPrincipal (min cKhale cKouk)).trans
          (min_le_right cKhale cKouk)
      exact (mul_le_mul_of_nonneg_right hcoef hpowNonneg).trans
        (hscalar.trans hKoukGap)

/-- Backwards-compatible constructor from the invalid-as-printed raw
interface.  It is retained only for auditing older modules. -/
theorem primitiveRegularHighGap_of_ford_raw
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hRaw :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate) :
    PrimitiveRegularHighGap :=
  primitiveRegularHighGap_of_high_estimate hFord
    (MAPKhaleAppendixBHighZeroFromRaw.appendixBHighZeroReciprocalEstimate_of_raw hRaw)

/-- Canonical source-facing constructor from the literal signed Lemma-6.2
applications at the four natural heights. -/
theorem primitiveRegularHighGap_of_ford_naturalScales
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hNatural :
      MAPKhaleAppendixBFirstPartScaleCorrected.AppendixBLemma41TrigNaturalScales) :
    PrimitiveRegularHighGap :=
  primitiveRegularHighGap_of_high_estimate hFord
    (MAPKhaleAppendixBFirstPartExactHeightRepair.appendixBHighZeroReciprocalEstimate_of_naturalScales
      hNatural)

/-- Source-faithful constructor below the combined natural-scale premise.
The only Khale inputs are the four literal Lemma-6.2 rows and the elementary
real-axis zeta estimate; the trigonometric/Euler-product combination is a
compiled theorem. -/
theorem primitiveRegularHighGap_of_ford_lemma62
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (h62 :
      MAPKhaleAppendixBLemma62NaturalScaleWeld.AppendixBLemma62FourNaturalScaleBounds)
    (hZeta :
      MAPKhaleAppendixBLemma62NaturalScaleWeld.AppendixBLemma41ZetaLogDerivativeBound) :
    PrimitiveRegularHighGap :=
  primitiveRegularHighGap_of_ford_naturalScales hFord
    (MAPKhaleAppendixBLemma62NaturalScaleWeld.lemma41TrigNaturalScales_of_lemma62Four_and_zeta
      h62 hZeta)

end

end MAPAPPrimitiveRegularHighGapFromFordRaw

#print axioms MAPAPPrimitiveRegularHighGapFromFordRaw.primitiveRegularHighGap_of_ford_raw
#print axioms MAPAPPrimitiveRegularHighGapFromFordRaw.primitiveRegularHighGap_of_ford_naturalScales
#print axioms MAPAPPrimitiveRegularHighGapFromFordRaw.primitiveRegularHighGap_of_ford_lemma62
