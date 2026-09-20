import RamachandraPrincipalHighContourTails
import JutilaPrimitiveFunctionalEquation
import KoukNegativeHalfStripEmpty

/-!
# Exact conductor-one shifted Lemma 3 identity

The primitive principal character contributes one translated zeta residue.
This file welds that residue-aware contour shift to the primitive functional
equation and the reflected-head deformation.
-/

namespace RamachandraPrincipalHighSourceIdentity

open Complex MeasureTheory Set Filter
open scoped BigOperators LSeries.notation Interval Topology
open BHPRamachandraMeanValueFromDyadicAFE
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedRightLineIdentity
open RamachandraShiftedGammaPoleContour
open RamachandraShiftedFunctionalEquationBridge
open RamachandraShiftedHeadContourTails
open RamachandraPrincipalHighContourIdentity
open RamachandraPrincipalHighContourTails

noncomputable section

set_option maxHeartbeats 800000

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

/-- Principal functional equation in Ramachandra's exact orientation on the
negative half-strip used by the long line. -/
theorem LFunction_eq_ramachandraFunctionalFactor_mul_dual_principal
    {z : ℂ} (hleft : (-1 / 2 : ℝ) ≤ z.re) (hright : z.re < 0) :
    DirichletCharacter.LFunction chiOne z =
      ramachandraFunctionalFactor chiOne z *
        DirichletCharacter.LFunction chiOne⁻¹ (1 - z) := by
  have hprim : DirichletCharacter.IsPrimitive chiOne :=
    DirichletCharacter.isPrimitive_one_level_one
  have hz : z ≠ 0 := by
    intro h
    subst z
    norm_num at hright
  have hdual : 1 - z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hgamma : DirichletCharacter.gammaFactor chiOne z ≠ 0 :=
    KoukNegativeHalfStripEmpty.gammaFactor_ne_zero_on_negativeHalfStrip
      chiOne hleft hright
  have hgammaDual : DirichletCharacter.gammaFactor chiOne⁻¹ (1 - z) ≠ 0 :=
    JutilaPrimitiveFunctionalEquation.gammaFactor_ne_zero_of_re_pos
      chiOne⁻¹ (by simp; linarith)
  have hfe :=
    JutilaPrimitiveFunctionalEquation.primitive_LFunction_functionalEquation
      hprim z (Or.inl hz) (Or.inl hdual) hgamma hgammaDual
  apply mul_right_cancel₀ hgamma
  rw [hfe]
  unfold ramachandraFunctionalFactor
  field_simp [hgamma]

theorem LFunction_sq_eq_ramachandraFunctionalFactor_sq_mul_dual_sq_principal
    {z : ℂ} (hleft : (-1 / 2 : ℝ) ≤ z.re) (hright : z.re < 0) :
    DirichletCharacter.LFunction chiOne z ^ 2 =
      ramachandraFunctionalFactor chiOne z ^ 2 *
        DirichletCharacter.LFunction chiOne⁻¹ (1 - z) ^ 2 := by
  rw [LFunction_eq_ramachandraFunctionalFactor_mul_dual_principal
    hleft hright]
  ring

/-- Pointwise functional-equation split on the literal long line. -/
theorem shiftedGammaRawIntegrand_longLine_eq_tail_add_head_principal
    (X sigma t v : ℝ) :
    shiftedGammaRawIntegrand chiOne (ramachandraShiftedPoint sigma t) X
        (((-(sigma + 1 / 4) : ℝ) : ℂ) + v * I) =
      ramachandraShiftedContourIntegrand chiOne X sigma
          (-(sigma + 1 / 4)) t v true +
        ramachandraShiftedContourIntegrand chiOne X sigma
          (-(sigma + 1 / 4)) t v false := by
  let s : ℂ := ramachandraShiftedPoint sigma t
  let w : ℂ := (((-(sigma + 1 / 4) : ℝ) : ℂ) + v * I)
  let z : ℂ := s + w
  have hzre : z.re = -(1 / 4 : ℝ) := by
    simp [z, s, w, ramachandraShiftedPoint]
  have hfe : DirichletCharacter.LFunction chiOne z ^ 2 =
      ramachandraFunctionalFactor chiOne z ^ 2 *
        DirichletCharacter.LFunction chiOne⁻¹ (1 - z) ^ 2 :=
    LFunction_sq_eq_ramachandraFunctionalFactor_sq_mul_dual_sq_principal
      (by rw [hzre]; norm_num) (by rw [hzre]; norm_num)
  have hzSeries : 1 < (1 - z).re := by rw [Complex.sub_re, hzre]; norm_num
  have hpartition := ramachandraReflectedTail_add_head_eq_LFunction_sq
    chiOne (X := X) hzSeries
  unfold shiftedGammaRawIntegrand ramachandraShiftedContourIntegrand
  dsimp [z, s, w] at hfe hpartition ⊢
  rw [hfe, ← hpartition]
  ring

/-- The full principal raw long-line integral is the sum of the literal
reflected tail and head integrals. -/
theorem shiftedGamma_long_integral_eq_tail_add_head_principal
    {X sigma t : ℝ} (hX : 0 < X)
    (hsigmaLo : -(1 / 4 : ℝ) < sigma)
    (hsigmaHi : sigma < 3 / 4) :
    (∫ v : ℝ,
      shiftedGammaRawIntegrand chiOne (ramachandraShiftedPoint sigma t) X
        (((-(sigma + 1 / 4) : ℝ) : ℂ) + v * I)) =
      (∫ v : ℝ,
        ramachandraShiftedContourIntegrand chiOne X sigma
          (-(sigma + 1 / 4)) t v true) +
      ∫ v : ℝ,
        ramachandraShiftedContourIntegrand chiOne X sigma
          (-(sigma + 1 / 4)) t v false := by
  let raw : ℝ → ℂ := fun v =>
    shiftedGammaRawIntegrand chiOne (ramachandraShiftedPoint sigma t) X
      (((-(sigma + 1 / 4) : ℝ) : ℂ) + v * I)
  let tail : ℝ → ℂ := fun v =>
    ramachandraShiftedContourIntegrand chiOne X sigma
      (-(sigma + 1 / 4)) t v true
  let head : ℝ → ℂ := fun v =>
    ramachandraShiftedContourIntegrand chiOne X sigma
      (-(sigma + 1 / 4)) t v false
  have hraw : Integrable raw := by
    simpa [raw] using
      (integrable_shiftedGammaRaw_vertical_principal
        (ramachandraShiftedPoint sigma t) hX
        (c := -(sigma + 1 / 4))
        (by linarith) (by linarith) (by linarith)
        (by simp [ramachandraShiftedPoint]; norm_num)
        (by simp [ramachandraShiftedPoint]; norm_num)
        (by simp [ramachandraShiftedPoint]; norm_num))
  have hhead : Integrable head := by
    simpa [head, RamachandraShiftedNonprincipalContourIdentity.shiftedContourIntegrand_false_eq_shiftedHeadIntegrand]
      using (integrable_shiftedHead_vertical chiOne
        DirichletCharacter.isPrimitive_one_level_one
        (ramachandraShiftedPoint sigma t) hX
        (show -1 < -(sigma + 1 / 4) by linarith)
        (show -(sigma + 1 / 4) < 0 by linarith)
        (show -(1 / 4 : ℝ) ≤
            (ramachandraShiftedPoint sigma t).re - (sigma + 1 / 4) by
          simp [ramachandraShiftedPoint])
        (show (ramachandraShiftedPoint sigma t).re - (sigma + 1 / 4) ≤
            1 / 2 by simp [ramachandraShiftedPoint]; norm_num))
  have hpw : ∀ v : ℝ, raw v = tail v + head v := by
    intro v
    simpa [raw, tail, head] using
      shiftedGammaRawIntegrand_longLine_eq_tail_add_head_principal
        X sigma t v
  have htail : Integrable tail := by
    have hdiff : Integrable (fun v => raw v - head v) := hraw.sub hhead
    refine hdiff.congr (Filter.Eventually.of_forall ?_)
    intro v
    change raw v - head v = tail v
    rw [hpw v]
    ring
  rw [show (∫ v : ℝ, raw v) = ∫ v : ℝ, tail v + head v by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall hpw]
  rw [MeasureTheory.integral_add htail hhead]

/-- Exact principal shifted Lemma 3 decomposition.  The fourth term is the
negative translated-zeta residue and is not hidden in a generic error. -/
theorem LFunction_sq_eq_shiftedDirect_sub_long_sub_short_add_principalResidue
    {X sigma t : ℝ} (hX : 0 < X)
    (hsigmaLo : 1 / 4 < sigma) (hsigmaHi : sigma < 3 / 4)
    (hlongNear : -(sigma + 1 / 4) ≤ -(Real.log X)⁻¹)
    (hnearHi : -(Real.log X)⁻¹ < 0)
    (hnearZHi : sigma - (Real.log X)⁻¹ ≤ 1 / 2) :
    DirichletCharacter.LFunction chiOne
        (ramachandraShiftedPoint sigma t) ^ 2 =
      ramachandraShiftedDirect chiOne X sigma t -
        ramachandraShiftedContourPiece chiOne X sigma
          (-(sigma + 1 / 4)) t true -
        ramachandraShiftedContourPiece chiOne X sigma
          (-(Real.log X)⁻¹) t false -
        principalTranslatedFirstDifference
          (ramachandraShiftedPoint sigma t) X
          (principalTranslatedPole (ramachandraShiftedPoint sigma t)) := by
  let s : ℂ := ramachandraShiftedPoint sigma t
  let a : ℝ := -(sigma + 1 / 4)
  let b : ℝ := 1
  let k : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hright : ramachandraShiftedDirect chiOne X sigma t =
      k * ∫ v : ℝ,
        shiftedGammaRawIntegrand chiOne s X ((b : ℂ) + v * I) := by
    simpa [ramachandraShiftedDirect, s, b, k, shiftedGammaRawIntegrand] using
      (smoothedSeries_eq_LFunctionSq_gamma_rightLine_unconditional
        chiOne (c := (1 : ℝ)) (by norm_num) hX
        (ramachandraShiftedPoint sigma t)
        (by simp [ramachandraShiftedPoint]; linarith))
  have hsne : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s, ramachandraShiftedPoint] at hre
    linarith
  have hshift :
      k * ∫ v : ℝ,
          shiftedGammaRawIntegrand chiOne s X ((b : ℂ) + v * I) =
        DirichletCharacter.LFunction chiOne s ^ 2 +
          principalTranslatedFirstDifference s X (principalTranslatedPole s) +
          k * ∫ v : ℝ,
            shiftedGammaRawIntegrand chiOne s X ((a : ℂ) + v * I) := by
    simpa [s, a, b, k] using
      (full_shiftedGamma_principal_vertical_integral_eq s hX hsne
        (r0 := (1 / 8 : ℝ)) (rp := (1 / 8 : ℝ))
        (a := -(sigma + 1 / 4)) (b := 1)
        (by linarith) (by norm_num) (by linarith) (by norm_num)
        (by norm_num) (by simp [principalTranslatedPole, s,
          ramachandraShiftedPoint]; linarith)
        (by simp [principalTranslatedPole, s,
          ramachandraShiftedPoint]; linarith)
        (by linarith) (by norm_num)
        (by simp [s, ramachandraShiftedPoint]; norm_num)
        (by simp [s, ramachandraShiftedPoint]; linarith)
        (by simp [s, ramachandraShiftedPoint]; norm_num)
        (by
          simp [s, ramachandraShiftedPoint]
          rw [abs_of_pos (by linarith)]
          norm_num at hsigmaLo ⊢
          exact hsigmaLo.le))
  have hsplitInt := shiftedGamma_long_integral_eq_tail_add_head_principal
    hX (by linarith) hsigmaHi (t := t)
  have hsplit :
      k * ∫ v : ℝ,
          shiftedGammaRawIntegrand chiOne s X ((a : ℂ) + v * I) =
        ramachandraShiftedContourPiece chiOne X sigma a t true +
          ramachandraShiftedContourPiece chiOne X sigma a t false := by
    rw [hsplitInt]
    simp only [ramachandraShiftedContourPiece, a, k]
    ring
  have hhead :
      ramachandraShiftedContourPiece chiOne X sigma
          (-(Real.log X)⁻¹) t false =
        ramachandraShiftedContourPiece chiOne X sigma a t false := by
    simpa [a] using
      (RamachandraShiftedNonprincipalContourIdentity.shiftedLongHead_eq_shiftedShortHead
        chiOne DirichletCharacter.isPrimitive_one_level_one hX
        hlongNear (by linarith) hnearHi hnearZHi (t := t))
  dsimp [s] at hshift ⊢
  dsimp [a] at hsplit hhead
  linear_combination (-1) * hright + (-1) * hshift +
    (-1) * hsplit + hhead

/-- The literal conductor-one residue used as the fourth piece in the
primitive contour reduction. -/
def principalShiftedSourceRemainder (T sigma t : ℝ) : ℂ :=
  -principalTranslatedFirstDifference
    (ramachandraShiftedPoint sigma t) T
    (principalTranslatedPole (ramachandraShiftedPoint sigma t))

/-- Source-range principal identity for the high-scale branch `T ≥ 9`.
The smaller compact range is handled directly by the principal low-range
estimate; no contour identity is needed there. -/
theorem LFunction_sq_eq_sourcePieces_principal
    {q : ℕ} [NeZero q] {T sigma t : ℝ}
    (hT : 9 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹) :
    DirichletCharacter.LFunction chiOne
        (ramachandraShiftedPoint sigma t) ^ 2 =
      primitiveShiftedDirect chiOne T sigma t -
        primitiveShiftedLongContour chiOne T sigma t -
        primitiveShiftedShortContour chiOne T sigma t +
        principalShiftedSourceRemainder T sigma t := by
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hqone
  have hTpos : 0 < T := by linarith
  have hqTnine : (9 : ℝ) ≤ (q : ℝ) * T := by
    nlinarith [mul_le_mul hqone hT (by norm_num : (0 : ℝ) ≤ 9) hqpos.le]
  have hexpTwo : Real.exp 2 < (9 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hlogqTtwo : 2 < Real.log ((q : ℝ) * T) := by
    rw [Real.lt_log_iff_exp_lt (mul_pos hqpos hTpos)]
    exact hexpTwo.trans_le hqTnine
  have hradius : (100 * Real.log ((q : ℝ) * T))⁻¹ <
      (1 / 100 : ℝ) := by
    rw [inv_lt_comm₀ (by positivity) (by norm_num)]
    norm_num
    linarith
  have hoff : |sigma - (1 / 2 : ℝ)| < 1 / 100 :=
    hstrip.trans_lt hradius
  have hsigmaLo : 1 / 4 < sigma := by
    have := (abs_lt.mp hoff).1
    linarith
  have hsigmaHi : sigma < 3 / 4 := by
    have := (abs_lt.mp hoff).2
    linarith
  have hlogTtwo : 2 < Real.log T := by
    rw [Real.lt_log_iff_exp_lt hTpos]
    exact hexpTwo.trans_le hT
  have hlogTpos : 0 < Real.log T := by linarith
  have hinvThalf : (Real.log T)⁻¹ < (1 / 2 : ℝ) := by
    rw [inv_lt_comm₀ hlogTpos (by norm_num)]
    norm_num
    exact hlogTtwo
  have hlongNear :
      -(sigma + 1 / 4) ≤ -(Real.log T)⁻¹ := by
    have hsigmaHalf : (49 / 100 : ℝ) < sigma := by
      have := (abs_lt.mp hoff).1
      linarith
    linarith
  have hnearHi : -(Real.log T)⁻¹ < 0 :=
    neg_neg_of_pos (inv_pos.mpr hlogTpos)
  have hTleqT : T ≤ (q : ℝ) * T := by
    nlinarith [mul_le_mul hqone (le_refl T) hTpos.le (by positivity : (0 : ℝ) ≤ q)]
  have hlogTleqT : Real.log T ≤ Real.log ((q : ℝ) * T) :=
    Real.log_le_log hTpos hTleqT
  have hdenCompare : Real.log T ≤
      100 * Real.log ((q : ℝ) * T) := by
    calc
      Real.log T ≤ Real.log ((q : ℝ) * T) := hlogTleqT
      _ ≤ 100 * Real.log ((q : ℝ) * T) := by nlinarith
  have hradiusLeInvT :
      (100 * Real.log ((q : ℝ) * T))⁻¹ ≤ (Real.log T)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hlogTpos hdenCompare
  have hnearZHi : sigma - (Real.log T)⁻¹ ≤ 1 / 2 := by
    have hupper := (abs_le.mp hstrip).2
    linarith
  simpa [primitiveShiftedDirect, primitiveShiftedLongContour,
    primitiveShiftedShortContour, primitiveShiftedScale,
    principalShiftedSourceRemainder] using
    (LFunction_sq_eq_shiftedDirect_sub_long_sub_short_add_principalResidue
      (X := T) hTpos hsigmaLo hsigmaHi hlongNear hnearHi hnearZHi
      (t := t))

/-- Canonical source remainder across primitive conductors.  It is zero at
every nonprincipal conductor and is exactly the translated-zeta residue at
conductor one. -/
def canonicalPrimitiveShiftedRemainder
    {d : ℕ} [NeZero d] (_psi : DirichletCharacter ℂ d)
    (T sigma t : ℝ) : ℂ :=
  if d = 1 then principalShiftedSourceRemainder T sigma t else 0

/-- Exact branch weld for every primitive character.  This is the pointwise
identity consumed by the fourth-moment reduction; no fourth-moment estimate
is assumed. -/
theorem LFunction_sq_eq_sourcePieces_allPrimitive
    {q d : ℕ} [NeZero q] [NeZero d]
    (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive)
    {T sigma t : ℝ} (hdq : d ∣ q) (hT : 9 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹) :
    DirichletCharacter.LFunction psi
        (ramachandraShiftedPoint sigma t) ^ 2 =
      primitiveShiftedDirect psi T sigma t -
        primitiveShiftedLongContour psi T sigma t -
        primitiveShiftedShortContour psi T sigma t +
        canonicalPrimitiveShiftedRemainder psi T sigma t := by
  by_cases hd : d = 1
  · subst d
    have hpsi : psi = chiOne := Subsingleton.elim _ _
    subst psi
    simpa [canonicalPrimitiveShiftedRemainder] using
      (LFunction_sq_eq_sourcePieces_principal
        (q := q) (T := T) (sigma := sigma) (t := t) hT hstrip)
  · have hpsi : psi ≠ 1 := by
      intro h
      exact hd
        (JutilaPrimitiveFunctionalEquation.level_eq_one_of_isPrimitive_eq_one
          hprim h)
    have hnon :=
      RamachandraShiftedNonprincipalContourIdentity.LFunction_sq_eq_sourcePieces_nonprincipal
        psi hprim hpsi hdq (by linarith) hstrip (t := t)
    simpa [canonicalPrimitiveShiftedRemainder, hd] using hnon

end
end RamachandraPrincipalHighSourceIdentity

#print axioms RamachandraPrincipalHighSourceIdentity.LFunction_eq_ramachandraFunctionalFactor_mul_dual_principal
#print axioms RamachandraPrincipalHighSourceIdentity.shiftedGamma_long_integral_eq_tail_add_head_principal
#print axioms RamachandraPrincipalHighSourceIdentity.LFunction_sq_eq_shiftedDirect_sub_long_sub_short_add_principalResidue
#print axioms RamachandraPrincipalHighSourceIdentity.LFunction_sq_eq_sourcePieces_principal
#print axioms RamachandraPrincipalHighSourceIdentity.LFunction_sq_eq_sourcePieces_allPrimitive
