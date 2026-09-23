import APRegularNearAppendixBAdapter
import WeakVKNearDecay

/-!
# Fixed-theta weak high-gap source boundary

The live near-one consumer only needs a gap which beats every fixed
polylogarithmic loss after the factor `X^(-omega/12)`.  This file records the
fixed-theta version of that boundary.  It is additive: the existing
`PrimitiveRegularHighGap` API remains unchanged.
-/

namespace MAPPrimitiveRegularHighSavingFixedTheta

open Filter Set
open DirichletZeros
open MAPAPRegularNearAppendixBAdapter

noncomputable section

/-- Primitive regular high-ordinate gap with an explicit fixed logarithmic
exponent.  The quantifiers and zero support are the same as the existing
`PrimitiveRegularHighGap` interface. -/
def PrimitiveRegularHighSavingAt (theta : ℝ) : Prop :=
  ∀ K : ℝ, 0 < K →
    ∃ c : ℝ, 0 < c ∧
      Filter.Eventually (fun X : ℝ =>
        ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
          chi.IsPrimitive →
          (q : ℝ) ≤ Real.rpow (Real.log X) K →
          ∀ (T : ℝ) (rho : ℂ),
            rho ∈ DirichletZeros.zeroSupport chi 0 T →
            4 / 5 < rho.re → 3 ≤ |rho.im| → |rho.im| ≤ X →
            c * Real.rpow (Real.log X) (-theta) ≤ 1 - rho.re)
        Filter.atTop

/-- A source exponent in `[1/4,1)` is exactly the range compatible with the
certified bounded-height principal gap and the weak-gap polylog absorption. -/
def FixedThetaWeakHighSaving : Prop :=
  ∃ theta : ℝ, 1 / 4 ≤ theta ∧ theta < 1 ∧
    PrimitiveRegularHighSavingAt theta

/-! A fixed exponent below `1/4` is stronger on the eventual range
`log X > 1`; this monotonicity bridge lets the consumer use the bounded-height
principal branch without imposing an analytic lower bound on the source
exponent. -/
theorem primitiveRegularHighSavingAt_mono
    {theta theta' : ℝ} (hTheta : theta ≤ theta') :
    PrimitiveRegularHighSavingAt theta →
      PrimitiveRegularHighSavingAt theta' := by
  intro hSaving K hK
  obtain ⟨c, hc, hgap⟩ := hSaving K hK
  refine ⟨c, hc, ?_⟩
  filter_upwards [hgap, eventually_gt_atTop (Real.exp 1)] with X hXgap hX
  have hXpos : 0 < X := (Real.exp_pos 1).trans hX
  have hlogOne : 1 < Real.log X := by
    rw [Real.lt_log_iff_exp_lt hXpos]
    exact hX
  intro q _inst chi hPrimitive hq T rho hrho hRe hIm hImX
  have hpow : Real.rpow (Real.log X) (-theta') ≤
      Real.rpow (Real.log X) (-theta) := by
    apply Real.rpow_le_rpow_of_exponent_le hlogOne.le
    linarith
  exact (mul_le_mul_of_nonneg_left hpow hc.le).trans
    (hXgap q chi hPrimitive hq T rho hrho hRe hIm hImX)

def FixedThetaWeakHighSavingAny : Prop :=
  ∃ theta : ℝ, theta < 1 ∧ PrimitiveRegularHighSavingAt theta

theorem fixedThetaWeakHighSaving_of_any
    (hSaving : FixedThetaWeakHighSavingAny) :
    FixedThetaWeakHighSaving := by
  obtain ⟨theta, hTheta, hSaving⟩ := hSaving
  let theta' : ℝ := max theta (1 / 4)
  have hThetaLow : 1 / 4 ≤ theta' := by
    dsimp [theta']
    exact le_max_right _ _
  have hThetaUpper : theta' < 1 := by
    dsimp [theta']
    exact max_lt hTheta (by norm_num)
  refine ⟨theta', hThetaLow, hThetaUpper, ?_⟩
  exact primitiveRegularHighSavingAt_mono (le_max_left _ _) hSaving

/-- The calculus factor used by every near-one consumer, with the exponent
kept explicit instead of hard-coding `3/4`. -/
theorem weakGapNearFactorBeatsPolylog_fixedTheta
    {theta c P A : ℝ} (htheta : theta < 1) (hc : 0 < c)
    (hP : 0 ≤ P) (hA : 0 ≤ A) :
    ∀ᶠ X : ℝ in atTop, ∀ omega : ℝ,
      c * Real.rpow (Real.log X) (-theta) ≤ omega →
      Real.rpow (Real.log X) P * Real.rpow X (-(omega / 12)) ≤
        Real.rpow (Real.log X) (-A) :=
  WeakVKNear.weakGap_nearFactor_beats_polylog theta c P A
    htheta hc hP hA

/-- The other fixed-`3/4` helper used by the gapped near-one consumer, with
`theta` explicit. -/
theorem logRpow_le_scaledWeakGapPower_fixedTheta
    {theta P a c : ℝ} (htheta : theta < 1)
    (hP : 0 ≤ P) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, ∀ omega : ℝ,
      c * Real.rpow (Real.log X) (-theta) ≤ omega →
      Real.rpow (Real.log X) P ≤ Real.rpow X (a * omega) := by
  have hdecay :=
    WeakVKNear.weakGap_nearFactor_beats_polylog theta (12 * a * c)
      P 0 htheta (by positivity) hP (by norm_num)
  have hlarge : ∀ᶠ X : ℝ in atTop, 1 < X :=
    eventually_gt_atTop 1
  filter_upwards [hdecay, hlarge] with X hdecayX hX omega homega
  let omega' : ℝ := 12 * a * omega
  have homega' :
      (12 * a * c) * Real.rpow (Real.log X) (-theta) ≤ omega' := by
    dsimp [omega']
    calc
      (12 * a * c) * Real.rpow (Real.log X) (-theta) =
          (12 * a) * (c * Real.rpow (Real.log X) (-theta)) := by ring
      _ ≤ (12 * a) * omega :=
        mul_le_mul_of_nonneg_left homega (by positivity)
      _ = omega' := by simp [omega']
  have hprod := hdecayX omega' homega'
  norm_num at hprod
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hpow0 : 0 ≤ Real.rpow X (a * omega) :=
    Real.rpow_nonneg hXpos.le _
  have hcancel :
      Real.rpow X (-(a * omega)) * Real.rpow X (a * omega) = 1 := by
    calc
      Real.rpow X (-(a * omega)) * Real.rpow X (a * omega) =
          Real.rpow X (-(a * omega) + a * omega) :=
        (Real.rpow_add hXpos (-(a * omega)) (a * omega)).symm
      _ = 1 := by norm_num
  calc
    Real.rpow (Real.log X) P =
        (Real.rpow (Real.log X) P * Real.rpow X (-(a * omega))) *
          Real.rpow X (a * omega) := by
      rw [mul_assoc, hcancel, mul_one]
    _ ≤ 1 * Real.rpow X (a * omega) :=
      mul_le_mul_of_nonneg_right (by
        simpa only [omega', show -(12 * a * omega / 12) =
          -(a * omega) by ring] using! hprod) hpow0
    _ = Real.rpow X (a * omega) := one_mul _

/-- The old `3/4` gap implies the new fixed-theta leaf, choosing
`theta = 3/4`.  This is a compatibility theorem only; it does not prove the
new leaf from no analytic input. -/
theorem fixedThetaWeakHighSaving_of_primitiveRegularHighGap
    (hgap : PrimitiveRegularHighGap) : FixedThetaWeakHighSaving := by
  refine ⟨3 / 4, by norm_num, by norm_num, ?_⟩
  simpa only [PrimitiveRegularHighSavingAt] using hgap

end
end MAPPrimitiveRegularHighSavingFixedTheta

#print axioms MAPPrimitiveRegularHighSavingFixedTheta.weakGapNearFactorBeatsPolylog_fixedTheta
#print axioms MAPPrimitiveRegularHighSavingFixedTheta.logRpow_le_scaledWeakGapPower_fixedTheta
#print axioms MAPPrimitiveRegularHighSavingFixedTheta.fixedThetaWeakHighSaving_of_primitiveRegularHighGap
#print axioms MAPPrimitiveRegularHighSavingFixedTheta.primitiveRegularHighSavingAt_mono
#print axioms MAPPrimitiveRegularHighSavingFixedTheta.fixedThetaWeakHighSaving_of_any
