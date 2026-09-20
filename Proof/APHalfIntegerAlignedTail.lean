import APCorrectedCommonHeightContract
import PaperEdgePrimitiveComponents

/-!
# Half-integer-aligned AP explicit formula

The arithmetic prefix is already indexed by floors, whereas Perron's formula
is naturally evaluated at `floor(t)+1/2`.  Keeping those endpoints aligned
removes the artificial real-endpoint/Perron-zero aperture mismatch.
-/

namespace MAPAPHalfIntegerAlignedTail

open MeasureTheory Set
open scoped BigOperators ENNReal ArithmeticFunction
open APFoundation APExplicitFormulaMajorantAdapter
open MAPFixedScaleAPZeroRoute
open PrimitiveTruncatedExplicitFormulaBridge
open TruncatedTwistedPerron
open MAPAPCorrectedCommonHeightContract
open PaperEdgePrimitiveComponents
open DirichletZeros

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Zero field on the literal Perron rectangle `sigma ≤ Re rho ≤ 1`. -/
def perronZeroField
    (chi : DirichletCharacter ℂ q) (sigma T t : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact finiteZeroField
    (zeroSupport chi.primitiveCharacter sigma T)
    (zeroMultiplicity chi.primitiveCharacter sigma T) t

/-- Endpoint remainder with the Perron zero sum left at its natural
half-integer.  There is no endpoint/Perron-zero mismatch term. -/
def alignedEndpointRemainder
    (chi : DirichletCharacter ℂ q) (sigma T t : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let N := ⌊t⌋₊
  let u := halfIntegerPoint N
  let c := standardEdge N
  exact
    residueMain chi.primitiveCharacter u - principalCoefficient chi * t +
      leftLineIntegral chi.primitiveCharacter u sigma T -
      horizontalBoundaryIntegral chi.primitiveCharacter u sigma c T +
      insideKernelError chi.primitiveCharacter N c T -
      coefficientTail chi.primitiveCharacter u c T (Finset.Icc 1 N) -
      imprimitiveMangoldtCorrection chi (Finset.Icc 1 N)

/-- Exact formula at a real arithmetic endpoint, while its zero sum remains
at the canonical half-integer Perron endpoint. -/
theorem ambientTwistedPsi_eq_principal_sub_perronZero_add_alignedRemainder
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {sigma T t : ℝ}
    (hlegal : paperEdgeContourLegal chi sigma T)
    (hN : 1 ≤ ⌊t⌋₊) :
    ambientTwistedPsi chi t =
      principalCoefficient chi * t -
        multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T
          (halfIntegerPoint ⌊t⌋₊) +
        alignedEndpointRemainder chi sigma T t := by
  have hc : 1 ≤ standardEdge ⌊t⌋₊ :=
    (standardEdge_gt_one ⌊t⌋₊ hN).le
  obtain ⟨hbottom, htop⟩ := hlegal.horizontal_nonzero hc
  have hformula :=
    UniformPsiDeterministicBridge.ambientTwistedMangoldtPrefix_eq_primitive_explicit_formula
      chi ⌊t⌋₊ hlegal.2.1.1 (by linarith [hlegal.2.1.2])
        (standardEdge_gt_one ⌊t⌋₊ hN) hlegal.1
        hlegal.2.2.1 hbottom htop
  unfold ambientTwistedPsi
  rw [hformula]
  simp only [alignedEndpointRemainder]
  ring

/-- On positive-left-edge support, the Perron zero-sum difference is exactly
the integral of the truncated zero field between the two half-integers. -/
theorem intervalIntegral_perronZeroField_eq_perronZeroSum_sub
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {sigma T a b : ℝ}
    (hsigma : 0 < sigma) (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ in a..b, perronZeroField chi sigma T t) =
      multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T b -
        multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T a := by
  let zeros := zeroSupport chi.primitiveCharacter sigma T
  let mult := zeroMultiplicity chi.primitiveCharacter sigma T
  have hzeros : ∀ rho ∈ zeros, 0 ≤ rho.re := by
    intro rho hrho
    exact hsigma.le.trans
      (PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
        chi.primitiveCharacter sigma T hrho).1.1
  have hint :=
    MAPEndpointRegularizedZeroPrimitive.intervalIntegral_finiteZeroField_endpoint
      zeros mult hzeros ha hb
  change (∫ t : ℝ in a..b, finiteZeroField zeros mult t) = _
  rw [hint]
  unfold MAPEndpointRegularizedZeroPrimitive.endpointFiniteZeroPrimitive
    multiplicityWeightedPerronZeroSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  have hre : sigma ≤ rho.re :=
    (PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
      chi.primitiveCharacter sigma T hrho).1.1
  have hrho0 : rho ≠ 0 := by
    intro hz
    subst rho
    norm_num at hre
    linarith
  simp only [MAPEndpointRegularizedZeroPrimitive.endpointRegularizedZeroTerm,
    if_neg hrho0, APFoundation.regularizedZeroTerm]
  field_simp [hrho0]
  simp [mult]

/-- Exact aligned window identity.  The zero integral is over the canonical
half-integer endpoints; the only remaining tail is the difference of the
aligned endpoint remainders. -/
theorem ambientCharacterWindowError_eq_alignedZeroIntegral_add_remainder
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {sigma T x Y : ℝ}
    (hlegal : paperEdgeContourLegal chi sigma T)
    (hY : 0 ≤ Y)
    (hNx : 1 ≤ ⌊x⌋₊) (hNxY : 1 ≤ ⌊x + Y⌋₊) :
    APMaximalExplicitFormulaBridge.ambientCharacterWindowError chi
        (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y =
      -(∫ t : ℝ in halfIntegerPoint ⌊x⌋₊..halfIntegerPoint ⌊x + Y⌋₊,
          perronZeroField chi sigma T t) +
        (alignedEndpointRemainder chi sigma T (x + Y) -
          alignedEndpointRemainder chi sigma T x) := by
  have hformulaX :=
    ambientTwistedPsi_eq_principal_sub_perronZero_add_alignedRemainder
      chi hlegal hNx
  have hformulaXY :=
    ambientTwistedPsi_eq_principal_sub_perronZero_add_alignedRemainder
      chi hlegal hNxY
  have hzero := intervalIntegral_perronZeroField_eq_perronZeroSum_sub
    chi (T := T) hlegal.2.1.1
      (halfIntegerPoint_pos ⌊x⌋₊)
      (halfIntegerPoint_pos ⌊x + Y⌋₊)
  rw [APMaximalExplicitFormulaBridge.ambientCharacterWindowError,
    twistedMangoldtWindow_eq_ambientTwistedPsi_sub chi hY]
  rw [hformulaXY, hformulaX, hzero]
  unfold principalCoefficient
  by_cases hchi : chi = 1
  · simp [hchi]
    ring
  · simp [hchi]
    ring

/-- Principal half-integer displacement in an arithmetic window is at most
one.  This is the only new scalar cost introduced by endpoint alignment. -/
theorem abs_halfInteger_window_sub_length_le_one
    {x Y : ℝ} (hx : 0 ≤ x) (hY : 0 ≤ Y) :
    |(halfIntegerPoint ⌊x + Y⌋₊ - halfIntegerPoint ⌊x⌋₊) - Y| ≤ 1 := by
  have ha := abs_halfIntegerPoint_floor_sub_le x hx
  have hb := abs_halfIntegerPoint_floor_sub_le (x + Y) (by linarith)
  have htri :
      |(halfIntegerPoint ⌊x + Y⌋₊ - (x + Y)) -
          (halfIntegerPoint ⌊x⌋₊ - x)| ≤
        |halfIntegerPoint ⌊x + Y⌋₊ - (x + Y)| +
          |halfIntegerPoint ⌊x⌋₊ - x| := abs_sub _ _
  have hid :
      (halfIntegerPoint ⌊x + Y⌋₊ - halfIntegerPoint ⌊x⌋₊) - Y =
        (halfIntegerPoint ⌊x + Y⌋₊ - (x + Y)) -
          (halfIntegerPoint ⌊x⌋₊ - x) := by ring
  rw [hid]
  linarith

/-- The norm of the truncated Perron zero field is continuous on every
positive interval. -/
theorem continuousOn_norm_perronZeroField
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    (sigma T : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => ‖perronZeroField chi sigma T t‖)
      (Set.Icc a b) := by
  apply ContinuousOn.norm
  unfold perronZeroField finiteZeroField
  apply continuousOn_finsetSum
  intro rho hrho
  intro t ht
  have htpos : 0 < t := ha.trans_le ht.1
  exact (continuousAt_const.mul
    (Complex.continuousAt_ofReal_cpow_const t (rho - 1)
      (Or.inr htpos.ne'))).continuousWithinAt

/-- Enlarge the floor-aligned interval by a fixed half unit at each end. -/
theorem aligned_zeroIntegral_norm_le_enlarged
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {sigma T x Y : ℝ} (hx : 1 ≤ x) (hY : 0 ≤ Y) :
    (∫ t : ℝ in halfIntegerPoint ⌊x⌋₊..halfIntegerPoint ⌊x + Y⌋₊,
        ‖perronZeroField chi sigma T t‖) ≤
      ∫ t : ℝ in x - 1 / 2..x + Y + 1 / 2,
        ‖perronZeroField chi sigma T t‖ := by
  have ha := abs_halfIntegerPoint_floor_sub_le x (zero_le_one.trans hx)
  have hb := abs_halfIntegerPoint_floor_sub_le (x + Y) (by linarith)
  have hab : halfIntegerPoint ⌊x⌋₊ ≤
      halfIntegerPoint ⌊x + Y⌋₊ := by
    unfold halfIntegerPoint
    have hf : ⌊x⌋₊ ≤ ⌊x + Y⌋₊ := Nat.floor_mono (by linarith)
    have hfr : (⌊x⌋₊ : ℝ) ≤ (⌊x + Y⌋₊ : ℝ) := by exact_mod_cast hf
    linarith
  apply intervalIntegral.integral_mono_interval
  · linarith [(abs_le.mp ha).1]
  · exact hab
  · linarith [(abs_le.mp hb).2]
  · exact Filter.Eventually.of_forall fun t => norm_nonneg _
  · have hleft : 0 < x - 1 / 2 := by linarith
    have hcont := continuousOn_norm_perronZeroField chi sigma T
      (a := x - 1 / 2) (b := x + Y + 1 / 2) hleft (by linarith)
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le
      (by linarith : x - 1 / 2 ≤ x + Y + 1 / 2)] using hcont

/-- After enlargement, division by the original legal length costs at most
a factor two once `Y ≥ 1`. -/
theorem aligned_zeroAverage_le_two_enlargedAverage
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {sigma T x Y : ℝ} (hx : 1 ≤ x) (hY : 1 ≤ Y) :
    Y⁻¹ * (∫ t : ℝ in
        halfIntegerPoint ⌊x⌋₊..halfIntegerPoint ⌊x + Y⌋₊,
          ‖perronZeroField chi sigma T t‖) ≤
      2 * ((Y + 1)⁻¹ *
        ∫ t : ℝ in x - 1 / 2..x + Y + 1 / 2,
          ‖perronZeroField chi sigma T t‖) := by
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  have hY1pos : 0 < Y + 1 := by linarith
  have hmono := aligned_zeroIntegral_norm_le_enlarged
    chi (sigma := sigma) (T := T) hx (zero_le_one.trans hY)
  have hleft0 : 0 ≤
      ∫ t : ℝ in halfIntegerPoint ⌊x⌋₊..halfIntegerPoint ⌊x + Y⌋₊,
        ‖perronZeroField chi sigma T t‖ := by
    apply intervalIntegral.integral_nonneg
    · unfold halfIntegerPoint
      have hf : ⌊x⌋₊ ≤ ⌊x + Y⌋₊ := Nat.floor_mono (by linarith)
      have hfr : (⌊x⌋₊ : ℝ) ≤ (⌊x + Y⌋₊ : ℝ) := by exact_mod_cast hf
      linarith
    · intro t ht
      exact norm_nonneg _
  have hright0 : 0 ≤
      ∫ t : ℝ in x - 1 / 2..x + Y + 1 / 2,
        ‖perronZeroField chi sigma T t‖ := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact norm_nonneg _
  have hratio : (Y + 1) / Y ≤ 2 := by
    apply (div_le_iff₀ hYpos).2
    linarith
  calc
    Y⁻¹ * (∫ t : ℝ in
        halfIntegerPoint ⌊x⌋₊..halfIntegerPoint ⌊x + Y⌋₊,
          ‖perronZeroField chi sigma T t‖) ≤
      Y⁻¹ * (∫ t : ℝ in x - 1 / 2..x + Y + 1 / 2,
        ‖perronZeroField chi sigma T t‖) := by
      exact mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hYpos.le)
    _ = ((Y + 1) / Y) * ((Y + 1)⁻¹ *
        ∫ t : ℝ in x - 1 / 2..x + Y + 1 / 2,
          ‖perronZeroField chi sigma T t‖) := by
      field_simp
    _ ≤ 2 * ((Y + 1)⁻¹ *
        ∫ t : ℝ in x - 1 / 2..x + Y + 1 / 2,
          ‖perronZeroField chi sigma T t‖) := by
      exact mul_le_mul_of_nonneg_right hratio
        (mul_nonneg (inv_nonneg.mpr hY1pos.le) hright0)

/-- Pointwise character bridge with the aligned zero average. -/
theorem norm_ambientCharacterWindowError_div_le_alignedAverage_add_tail
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {sigma T x Y : ℝ}
    (hlegal : paperEdgeContourLegal chi sigma T)
    (hx : 1 ≤ x) (hY : 1 ≤ Y)
    (hNx : 1 ≤ ⌊x⌋₊) (hNxY : 1 ≤ ⌊x + Y⌋₊) :
    ‖APMaximalExplicitFormulaBridge.ambientCharacterWindowError chi
        (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y / Y‖ ≤
      2 * ((Y + 1)⁻¹ *
        ∫ t : ℝ in x - 1 / 2..x + Y + 1 / 2,
          ‖perronZeroField chi sigma T t‖) +
      ‖(alignedEndpointRemainder chi sigma T (x + Y) -
          alignedEndpointRemainder chi sigma T x) / Y‖ := by
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  rw [ambientCharacterWindowError_eq_alignedZeroIntegral_add_remainder
    chi hlegal (zero_le_one.trans hY) hNx hNxY]
  have hnormInt :
      ‖∫ t : ℝ in halfIntegerPoint ⌊x⌋₊..halfIntegerPoint ⌊x + Y⌋₊,
          perronZeroField chi sigma T t‖ ≤
        ∫ t : ℝ in halfIntegerPoint ⌊x⌋₊..halfIntegerPoint ⌊x + Y⌋₊,
          ‖perronZeroField chi sigma T t‖ := by
    have hab : halfIntegerPoint ⌊x⌋₊ ≤
        halfIntegerPoint ⌊x + Y⌋₊ := by
      unfold halfIntegerPoint
      have hf : ⌊x⌋₊ ≤ ⌊x + Y⌋₊ := Nat.floor_mono (by linarith)
      have hfr : (⌊x⌋₊ : ℝ) ≤ (⌊x + Y⌋₊ : ℝ) := by exact_mod_cast hf
      linarith
    have hcont := continuousOn_norm_perronZeroField chi sigma T
      (a := halfIntegerPoint ⌊x⌋₊)
      (b := halfIntegerPoint ⌊x + Y⌋₊)
      (halfIntegerPoint_pos _) hab
    have hint : IntervalIntegrable
        (fun t : ℝ => ‖perronZeroField chi sigma T t‖) volume
        (halfIntegerPoint ⌊x⌋₊) (halfIntegerPoint ⌊x + Y⌋₊) := by
      apply ContinuousOn.intervalIntegrable
      simpa only [Set.uIcc_of_le hab] using hcont
    exact intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall fun t ht => le_rfl) hint
  calc
    ‖(-(∫ t : ℝ in halfIntegerPoint ⌊x⌋₊..halfIntegerPoint ⌊x + Y⌋₊,
          perronZeroField chi sigma T t) +
        (alignedEndpointRemainder chi sigma T (x + Y) -
          alignedEndpointRemainder chi sigma T x)) / Y‖ ≤
      Y⁻¹ * (∫ t : ℝ in
        halfIntegerPoint ⌊x⌋₊..halfIntegerPoint ⌊x + Y⌋₊,
          ‖perronZeroField chi sigma T t‖) +
        ‖(alignedEndpointRemainder chi sigma T (x + Y) -
          alignedEndpointRemainder chi sigma T x) / Y‖ := by
      rw [add_div]
      calc
        ‖(-(∫ t : ℝ in halfIntegerPoint ⌊x⌋₊..halfIntegerPoint ⌊x + Y⌋₊,
              perronZeroField chi sigma T t)) / (Y : ℂ) +
            (alignedEndpointRemainder chi sigma T (x + Y) -
              alignedEndpointRemainder chi sigma T x) / (Y : ℂ)‖ ≤
          ‖(-(∫ t : ℝ in halfIntegerPoint ⌊x⌋₊..halfIntegerPoint ⌊x + Y⌋₊,
              perronZeroField chi sigma T t)) / (Y : ℂ)‖ +
            ‖(alignedEndpointRemainder chi sigma T (x + Y) -
              alignedEndpointRemainder chi sigma T x) / (Y : ℂ)‖ :=
          norm_add_le _ _
        _ = Y⁻¹ * ‖∫ t : ℝ in
              halfIntegerPoint ⌊x⌋₊..halfIntegerPoint ⌊x + Y⌋₊,
                perronZeroField chi sigma T t‖ +
            ‖(alignedEndpointRemainder chi sigma T (x + Y) -
              alignedEndpointRemainder chi sigma T x) / Y‖ := by
          rw [norm_div, norm_neg, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hYpos, div_eq_inv_mul]
        _ ≤ Y⁻¹ * (∫ t : ℝ in
              halfIntegerPoint ⌊x⌋₊..halfIntegerPoint ⌊x + Y⌋₊,
                ‖perronZeroField chi sigma T t‖) +
            ‖(alignedEndpointRemainder chi sigma T (x + Y) -
              alignedEndpointRemainder chi sigma T x) / Y‖ := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hnormInt (inv_nonneg.mpr hYpos.le))
            le_rfl
    _ ≤ 2 * ((Y + 1)⁻¹ *
        ∫ t : ℝ in x - 1 / 2..x + Y + 1 / 2,
          ‖perronZeroField chi sigma T t‖) +
      ‖(alignedEndpointRemainder chi sigma T (x + Y) -
          alignedEndpointRemainder chi sigma T x) / Y‖ := by
      exact add_le_add
        (aligned_zeroAverage_le_two_enlargedAverage
          chi (sigma := sigma) (T := T) hx hY) le_rfl

end
end MAPAPHalfIntegerAlignedTail

#print axioms MAPAPHalfIntegerAlignedTail.ambientTwistedPsi_eq_principal_sub_perronZero_add_alignedRemainder
#print axioms MAPAPHalfIntegerAlignedTail.intervalIntegral_perronZeroField_eq_perronZeroSum_sub
#print axioms MAPAPHalfIntegerAlignedTail.ambientCharacterWindowError_eq_alignedZeroIntegral_add_remainder
#print axioms MAPAPHalfIntegerAlignedTail.abs_halfInteger_window_sub_length_le_one
#print axioms MAPAPHalfIntegerAlignedTail.aligned_zeroIntegral_norm_le_enlarged
#print axioms MAPAPHalfIntegerAlignedTail.aligned_zeroAverage_le_two_enlargedAverage
#print axioms MAPAPHalfIntegerAlignedTail.norm_ambientCharacterWindowError_div_le_alignedAverage_add_tail
