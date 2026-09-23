import RamachandraPrincipalHighSourceIdentity
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# Continuity of the conductor-one translated-pole remainder

This file removes the last regularity obligation in the principal branch of
the literal shifted Ramachandra contour identity.  The key point is that the
value of the first divided difference at the translated pole is an ordinary
derivative.  We reduce it to the derivative of the entire shifted Gamma core,
whose evaluation point satisfies `s + (1-s) = 1`.
-/

namespace RamachandraPrincipalResidueContinuity

open Complex Filter Topology Set
open RamachandraPrincipalHighContourIdentity
open RamachandraPrincipalHighSourceIdentity
open BHPRamachandraMeanValueFromDyadicAFE
open RamachandraPrimitiveShiftedContourReduction

noncomputable section

local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

set_option maxHeartbeats 800000

/-- At the translated pole, the first divided difference is the derivative
of the entire core divided by the translated displacement, with the expected
double-pole correction. -/
theorem principalTranslatedFirstDifference_self_eq
    {s : ℂ} {X : ℝ} (hX : 0 < X) (hs : s ≠ 1)
    (hpStrip : -1 < (principalTranslatedPole s).re) :
    principalTranslatedFirstDifference s X (principalTranslatedPole s) =
      deriv (principalShiftedGammaCore s X) (principalTranslatedPole s) /
          principalTranslatedPole s -
        principalShiftedGammaCore s X (principalTranslatedPole s) /
          principalTranslatedPole s ^ 2 := by
  let p : ℂ := principalTranslatedPole s
  let A : ℂ → ℂ := principalShiftedGammaCore s X
  let f : ℂ → ℂ := fun w =>
    A w / w - (w - p) ^ 2 * (A 0 / (w * p ^ 2))
  have hp : p ≠ 0 := by
    dsimp [p, principalTranslatedPole]
    exact sub_ne_zero.mpr (Ne.symm hs)
  have hAf : principalAfterGammaPole s X =ᶠ[nhds p] f := by
    filter_upwards [eventually_ne_nhds hp] with w hw
    have halg :
        w⁻¹ * ((p ^ 2 * A w - A 0 * (w - p) ^ 2) -
          (p ^ 2 * A 0 - A 0 * (0 - p) ^ 2)) / p ^ 2 =
          A w / w - (w - p) ^ 2 * (A 0 / (w * p ^ 2)) := by
      field_simp [hw, hp]
      ring
    simpa [principalAfterGammaPole, dslope_of_ne _ hw, slope,
      principalGammaZeroKernel,
      A, p, f, vsub_eq_sub] using halg
  have hderivAf : deriv (principalAfterGammaPole s X) p = deriv f p :=
    hAf.deriv_eq
  have hAderiv : HasDerivAt A (deriv A p) p :=
    (analyticAt_principalShiftedGammaCore s hX hpStrip).differentiableAt.hasDerivAt
  have hfderiv : HasDerivAt f
      (deriv A p / p - A p / p ^ 2) p := by
    dsimp [f]
    have hfirst := hAderiv.div (hasDerivAt_id p) hp
    have hquot : HasDerivAt (fun w : ℂ => A 0 / (w * p ^ 2))
        (-A 0 * p ^ 2 / (p * p ^ 2) ^ 2) p := by
      simpa only [id_eq, zero_mul, one_mul, zero_sub, neg_mul] using!
        (hasDerivAt_const p (A 0)).div
        ((hasDerivAt_id p).mul_const (p ^ 2))
        (mul_ne_zero hp (pow_ne_zero 2 hp))
    have hsecond := (((hasDerivAt_id p).sub_const p).pow 2).mul hquot
    have hsecond0 : HasDerivAt
        (fun w : ℂ => (w - p) ^ 2 * (A 0 / (w * p ^ 2))) 0 p := by
      simpa using! hsecond
    convert hfirst.sub hsecond0 using 1 <;>
      first | rfl | (simp only [id_eq]; field_simp [hp]; ring)
  unfold principalTranslatedFirstDifference
  rw [dslope_same, hderivAf, hfderiv.deriv]

/-- The derivative of the entire shifted Gamma core at `p = 1-s` has no
moving zeta argument: the regularized zeta factor and its derivative are both
evaluated at `1`. -/
theorem principalShiftedGammaCore_deriv_translatedPole_eq
    {s : ℂ} {X : ℝ} (hX : 0 < X)
    (hpStrip : -1 < (principalTranslatedPole s).re) :
    deriv (principalShiftedGammaCore s X) (principalTranslatedPole s) =
      (2 * principalF 1 * deriv principalF 1 *
          Complex.Gamma (principalTranslatedPole s + 1) *
          (X : ℂ) ^ principalTranslatedPole s) +
      (principalF 1 ^ 2 *
          deriv Complex.Gamma (principalTranslatedPole s + 1) *
          (X : ℂ) ^ principalTranslatedPole s) +
      (principalF 1 ^ 2 *
          Complex.Gamma (principalTranslatedPole s + 1) *
          ((X : ℂ) ^ principalTranslatedPole s *
            Complex.log (X : ℂ))) := by
  let p : ℂ := principalTranslatedPole s
  have hsp : s + p = 1 := by
    dsimp [p, principalTranslatedPole]
    ring
  have hFbase : HasDerivAt principalF (deriv principalF 1) 1 :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1 1).hasDerivAt
  have hF : HasDerivAt (fun w : ℂ => principalF (s + w))
      (deriv principalF 1) p := by
    have hFbase' : HasDerivAt principalF (deriv principalF 1) (s + p) := by
      simpa [hsp] using hFbase
    simpa using! hFbase'.comp p ((hasDerivAt_id p).const_add s)
  have hGammaDiff : DifferentiableAt ℂ Complex.Gamma (p + 1) := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    linarith
  have hGamma : HasDerivAt (fun w : ℂ => Complex.Gamma (w + 1))
      (deriv Complex.Gamma (p + 1)) p := by
    simpa using! hGammaDiff.hasDerivAt.comp p ((hasDerivAt_id p).add_const 1)
  have hpow : HasDerivAt (fun w : ℂ => (X : ℂ) ^ w)
      ((X : ℂ) ^ p * Complex.log (X : ℂ)) p :=
    (Complex.hasStrictDerivAt_const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).hasDerivAt
  have hcore := ((hF.pow 2).mul hGamma).mul hpow
  have hcoreDeriv := hcore.deriv
  have hcoreDeriv' :
      deriv (fun w : ℂ =>
        principalF (s + w) ^ 2 * Complex.Gamma (w + 1) * (X : ℂ) ^ w) p =
        ((2 * principalF (s + p) * deriv principalF 1 *
              Complex.Gamma (p + 1) +
            principalF (s + p) ^ 2 * deriv Complex.Gamma (p + 1)) *
              (X : ℂ) ^ p +
          principalF (s + p) ^ 2 * Complex.Gamma (p + 1) *
            ((X : ℂ) ^ p * Complex.log (X : ℂ))) := by
    simpa only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat,
      pow_one, Nat.reduceSubDiff] using! hcoreDeriv
  change deriv (fun w : ℂ =>
      principalF (s + w) ^ 2 * Complex.Gamma (w + 1) * (X : ℂ) ^ w) p = _
  rw [hcoreDeriv']
  dsimp [p] at hsp ⊢
  rw [hsp]
  ring

/-- Closed formula for the translated simple-pole coefficient, expressed only
through Gamma, its derivative, and the moving displacement `p = 1-s`.
The regularized zeta values occur only at the fixed point `1`. -/
def principalTranslatedResidueClosedForm (X : ℝ) (p : ℂ) : ℂ :=
  ((2 * principalF 1 * deriv principalF 1 * Complex.Gamma (p + 1) *
        (X : ℂ) ^ p) +
      (principalF 1 ^ 2 * deriv Complex.Gamma (p + 1) * (X : ℂ) ^ p) +
      (principalF 1 ^ 2 * Complex.Gamma (p + 1) *
        ((X : ℂ) ^ p * Complex.log (X : ℂ)))) / p -
    (principalF 1 ^ 2 * Complex.Gamma (p + 1) * (X : ℂ) ^ p) / p ^ 2

theorem principalShiftedSourceRemainder_eq_neg_closedForm
    {T sigma t : ℝ} (hT : 0 < T) (hsigma : sigma < 1) :
    principalShiftedSourceRemainder T sigma t =
      -principalTranslatedResidueClosedForm T
        (principalTranslatedPole (ramachandraShiftedPoint sigma t)) := by
  let s : ℂ := ramachandraShiftedPoint sigma t
  let p : ℂ := principalTranslatedPole s
  have hs : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s, ramachandraShiftedPoint] at hre
    linarith
  have hpStrip : -1 < p.re := by
    simp [p, s, principalTranslatedPole, ramachandraShiftedPoint]
    linarith
  have hsp : s + p = 1 := by
    dsimp [p, principalTranslatedPole]
    ring
  rw [principalShiftedSourceRemainder,
    principalTranslatedFirstDifference_self_eq hT hs hpStrip,
    principalShiftedGammaCore_deriv_translatedPole_eq hT hpStrip]
  unfold principalShiftedGammaCore principalTranslatedResidueClosedForm
  dsimp [s, p] at hsp ⊢
  rw [hsp]

/-- The Gamma derivative is continuous on the right half-plane.  This is a
direct complex-analytic consequence of Gamma's holomorphy there. -/
theorem continuousOn_deriv_Gamma_rightHalfPlane :
    ContinuousOn (deriv Complex.Gamma) (Complex.re ⁻¹' Ioi 0) := by
  have hopen : IsOpen (Complex.re ⁻¹' Ioi 0) :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hdiff : DifferentiableOn ℂ Complex.Gamma (Complex.re ⁻¹' Ioi 0) := by
    intro z hz
    apply (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hzpos : 0 < z.re := hz
    rw [hre] at hzpos
    linarith
  exact (hdiff.deriv hopen).continuousOn

/-- For a fixed shifted line strictly left of the zeta pole, the explicit
translated-pole coefficient varies continuously with the ordinate. -/
theorem continuous_principalTranslatedResidueClosedForm_comp
    {T sigma : ℝ} (hT : 0 < T) (hsigma : sigma < 1) :
    Continuous (fun t : ℝ =>
      principalTranslatedResidueClosedForm T
        (principalTranslatedPole (ramachandraShiftedPoint sigma t))) := by
  let p : ℝ → ℂ := fun t =>
    principalTranslatedPole (ramachandraShiftedPoint sigma t)
  have hpcont : Continuous p := by
    dsimp [p, principalTranslatedPole, ramachandraShiftedPoint]
    fun_prop
  have hpne : ∀ t, p t ≠ 0 := by
    intro t h
    have hre := congrArg Complex.re h
    simp [p, principalTranslatedPole, ramachandraShiftedPoint] at hre
    linarith
  have hGamma : Continuous (fun t : ℝ => Complex.Gamma (p t + 1)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have houter : ContinuousAt Complex.Gamma (p t + 1) := by
      apply Complex.continuousAt_Gamma
      intro m hm
      have hre := congrArg Complex.re hm
      simp [p, principalTranslatedPole, ramachandraShiftedPoint] at hre
      linarith
    simpa only [Function.comp_apply] using!
      (ContinuousAt.comp (f := fun u : ℝ => p u + 1) houter
        ((hpcont.continuousAt).add_const 1))
  have hGammaDeriv :
      Continuous (fun t : ℝ => deriv Complex.Gamma (p t + 1)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hmem : p t + 1 ∈ Complex.re ⁻¹' Ioi 0 := by
      simp [p, principalTranslatedPole, ramachandraShiftedPoint]
      linarith
    have hopen : IsOpen (Complex.re ⁻¹' Ioi 0) :=
      Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
    have hlocal : ContinuousAt (deriv Complex.Gamma) (p t + 1) :=
      continuousOn_deriv_Gamma_rightHalfPlane.continuousAt
        (hopen.mem_nhds hmem)
    simpa only [Function.comp_apply] using!
      (ContinuousAt.comp (f := fun u : ℝ => p u + 1) hlocal
        ((hpcont.continuousAt).add_const 1))
  have hpow : Continuous (fun t : ℝ => (T : ℂ) ^ p t) := by
    exact hpcont.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hT.ne'))
  unfold principalTranslatedResidueClosedForm
  exact (((((continuous_const.mul continuous_const).mul hGamma).mul hpow).add
    (((continuous_const.mul hGammaDeriv).mul hpow))).add
      (((continuous_const.mul hGamma).mul
        (hpow.mul continuous_const)))).div hpcont hpne |>.sub
          (((continuous_const.mul hGamma).mul hpow).div
            (hpcont.pow 2) (fun t => pow_ne_zero 2 (hpne t)))

/-- Exact continuity field needed by `PrimitiveShiftedContourIdentityData` in
the principal branch. -/
theorem continuous_principalShiftedSourceRemainder_sq
    {T sigma : ℝ} (hT : 0 < T) (hsigma : sigma < 1) :
    Continuous (fun t : ℝ =>
      ‖principalShiftedSourceRemainder T sigma t‖ ^ 2) := by
  have hrem : Continuous (fun t : ℝ =>
      principalShiftedSourceRemainder T sigma t) := by
    have hclosed :=
      (continuous_principalTranslatedResidueClosedForm_comp hT hsigma).neg
    exact hclosed.congr (fun t =>
      (principalShiftedSourceRemainder_eq_neg_closedForm hT hsigma).symm)
  exact hrem.norm.pow 2

/-- Uniform branch version used directly in the all-primitive identity data:
the remainder is the continuous principal residue at conductor one and zero at
all other primitive conductors. -/
theorem continuous_canonicalPrimitiveShiftedRemainder_sq
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {T sigma : ℝ} (hT : 0 < T) (hsigma : sigma < 1) :
    Continuous (fun t : ℝ =>
      ‖canonicalPrimitiveShiftedRemainder psi T sigma t‖ ^ 2) := by
  by_cases hd : d = 1
  · subst d
    simpa [canonicalPrimitiveShiftedRemainder] using
      (continuous_principalShiftedSourceRemainder_sq hT hsigma)
  · simpa [canonicalPrimitiveShiftedRemainder, hd] using
      (continuous_const : Continuous (fun _t : ℝ => (0 : ℝ)))

end
end RamachandraPrincipalResidueContinuity

#print axioms RamachandraPrincipalResidueContinuity.principalTranslatedFirstDifference_self_eq
#print axioms RamachandraPrincipalResidueContinuity.principalShiftedGammaCore_deriv_translatedPole_eq
#print axioms RamachandraPrincipalResidueContinuity.principalShiftedSourceRemainder_eq_neg_closedForm
#print axioms RamachandraPrincipalResidueContinuity.continuous_principalShiftedSourceRemainder_sq
#print axioms RamachandraPrincipalResidueContinuity.continuous_canonicalPrimitiveShiftedRemainder_sq
