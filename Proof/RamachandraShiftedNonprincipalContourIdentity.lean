import RamachandraShiftedRightLineIdentity
import RamachandraShiftedGammaPoleContour
import RamachandraShiftedFunctionalEquationBridge
import RamachandraShiftedHeadContourTails

/-!
# Exact nonprincipal shifted Lemma 3 identity

This module welds the premise-free Mellin inversion, Gamma-pole displacement,
primitive functional equation, and reflected-head displacement.  Its conclusion
is the literal `S - I₁ - I₂` identity used in Ramachandra's omitted shifted
argument, before any mean-value estimate is applied.
-/

namespace RamachandraShiftedNonprincipalContourIdentity

open Complex MeasureTheory Set Filter
open scoped BigOperators LSeries.notation Interval Topology
open BHPRamachandraMeanValueFromDyadicAFE
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedRightLineIdentity
open RamachandraShiftedGammaPoleContour
open RamachandraShiftedFunctionalEquationBridge
open RamachandraShiftedHeadFiniteContour
open RamachandraShiftedHeadContourTails

noncomputable section

set_option maxHeartbeats 800000

/-- Moduli `1` and `2` have only the principal Dirichlet character. -/
theorem three_le_modulus_of_nonprincipal
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hpsi : psi ≠ 1) : 3 ≤ d := by
  have hd0 : d ≠ 0 := NeZero.ne d
  have hd1 : d ≠ 1 := by
    intro hd
    subst d
    exact hpsi (Subsingleton.elim psi 1)
  have hd2 : d ≠ 2 := by
    intro hd
    subst d
    have hcardTot : Fintype.card (DirichletCharacter ℂ 2) =
        Nat.totient 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ 2
    have hcard : Fintype.card (DirichletCharacter ℂ 2) = 1 := by
      rw [hcardTot, Nat.totient_two]
    have hsub : ∀ a b : DirichletCharacter ℂ 2, a = b :=
      Fintype.card_le_one_iff.mp (by omega)
    exact hpsi (hsub psi 1)
  omega

/-- On the long line, the literal reflected head is exactly the generic head
integrand used in the pole-free deformation. -/
theorem shiftedContourIntegrand_false_eq_shiftedHeadIntegrand
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (X sigma u t v : ℝ) :
    ramachandraShiftedContourIntegrand psi X sigma u t v false =
      shiftedHeadIntegrand psi (ramachandraShiftedPoint sigma t) X
        ((u : ℂ) + v * I) := by
  rfl

/-- The long-line reflected head is integrable under the exact shifted-strip
conditions used below. -/
theorem integrable_shiftedContourIntegrand_long_head
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hprim : psi.IsPrimitive)
    {X sigma t : ℝ} (hX : 0 < X)
    (hsigmaLo : -(1 / 4 : ℝ) < sigma)
    (hsigmaHi : sigma < 3 / 4) :
    Integrable (fun v : ℝ =>
      ramachandraShiftedContourIntegrand psi X sigma
        (-(sigma + 1 / 4)) t v false) := by
  simpa [shiftedContourIntegrand_false_eq_shiftedHeadIntegrand] using
    (integrable_shiftedHead_vertical psi
      hprim
      (ramachandraShiftedPoint sigma t) hX
      (show -1 < -(sigma + 1 / 4) by linarith)
      (show -(sigma + 1 / 4) < 0 by linarith)
      (show -(1 / 4 : ℝ) ≤
          (ramachandraShiftedPoint sigma t).re - (sigma + 1 / 4) by
        simp [ramachandraShiftedPoint])
      (show (ramachandraShiftedPoint sigma t).re - (sigma + 1 / 4) ≤
          1 / 2 by
        simp [ramachandraShiftedPoint]
        norm_num))

/-- The primitive functional equation splits the entire long-line raw
integral into the two literal reflected integrals. -/
theorem shiftedGamma_long_integral_eq_tail_add_head
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hprim : psi.IsPrimitive) (hpsi : psi ≠ 1)
    {X sigma t : ℝ} (hX : 0 < X)
    (hsigmaLo : -(1 / 4 : ℝ) < sigma)
    (hsigmaHi : sigma < 3 / 4) :
    (∫ v : ℝ,
      shiftedGammaRawIntegrand psi (ramachandraShiftedPoint sigma t) X
        (((-(sigma + 1 / 4) : ℝ) : ℂ) + v * I)) =
      (∫ v : ℝ,
        ramachandraShiftedContourIntegrand psi X sigma
          (-(sigma + 1 / 4)) t v true) +
      ∫ v : ℝ,
        ramachandraShiftedContourIntegrand psi X sigma
          (-(sigma + 1 / 4)) t v false := by
  let raw : ℝ → ℂ := fun v =>
    shiftedGammaRawIntegrand psi (ramachandraShiftedPoint sigma t) X
      (((-(sigma + 1 / 4) : ℝ) : ℂ) + v * I)
  let tail : ℝ → ℂ := fun v =>
    ramachandraShiftedContourIntegrand psi X sigma
      (-(sigma + 1 / 4)) t v true
  let head : ℝ → ℂ := fun v =>
    ramachandraShiftedContourIntegrand psi X sigma
      (-(sigma + 1 / 4)) t v false
  have hraw : Integrable raw := by
    apply integrable_shiftedGammaRaw_vertical psi hpsi
      (ramachandraShiftedPoint sigma t) hX
    · linarith
    · linarith
    · linarith
    · simp [ramachandraShiftedPoint]
      norm_num
    · simp [ramachandraShiftedPoint]
      norm_num
  have hhead : Integrable head := by
    simpa [head] using integrable_shiftedContourIntegrand_long_head
      psi hprim hX hsigmaLo hsigmaHi
  have hpw : ∀ v : ℝ, raw v = tail v + head v := by
    intro v
    simpa [raw, tail, head] using
      shiftedGammaRawIntegrand_longLine_eq_shiftedContour_tail_add_head
        hprim hpsi X sigma t v
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

/-- Exact displacement of the literal reflected head from the source long
line to the source near line. -/
theorem shiftedLongHead_eq_shiftedShortHead
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hprim : psi.IsPrimitive) {X sigma t : ℝ}
    (hX : 0 < X)
    (hlongNear : -(sigma + 1 / 4) ≤ -(Real.log X)⁻¹)
    (hlongLo : -1 < -(sigma + 1 / 4))
    (hnearHi : -(Real.log X)⁻¹ < 0)
    (hnearZHi : sigma - (Real.log X)⁻¹ ≤ 1 / 2) :
    ramachandraShiftedContourPiece psi X sigma
        (-(Real.log X)⁻¹) t false =
      ramachandraShiftedContourPiece psi X sigma
        (-(sigma + 1 / 4)) t false := by
  simpa [ramachandraShiftedContourPiece,
    shiftedContourIntegrand_false_eq_shiftedHeadIntegrand] using
    (full_shiftedHead_vertical_integral_eq psi hprim
      (ramachandraShiftedPoint sigma t) hX hlongNear hlongLo hnearHi
      (by simp [ramachandraShiftedPoint])
      (by simpa [ramachandraShiftedPoint] using hnearZHi))

/-- Premise-free exact shifted Lemma 3 decomposition for every primitive
nonprincipal character.  The hypotheses are only elementary source-parameter
inequalities ensuring that the two head lines stay in the certified strip. -/
theorem LFunction_sq_eq_shiftedDirect_sub_long_sub_short_nonprincipal
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hprim : psi.IsPrimitive) (hpsi : psi ≠ 1)
    {X sigma t : ℝ} (hX : 0 < X)
    (hsigmaLo : 1 / 4 < sigma) (hsigmaHi : sigma < 3 / 4)
    (hlongNear : -(sigma + 1 / 4) ≤ -(Real.log X)⁻¹)
    (hnearHi : -(Real.log X)⁻¹ < 0)
    (hnearZHi : sigma - (Real.log X)⁻¹ ≤ 1 / 2) :
    DirichletCharacter.LFunction psi
        (ramachandraShiftedPoint sigma t) ^ 2 =
      ramachandraShiftedDirect psi X sigma t -
        ramachandraShiftedContourPiece psi X sigma
          (-(sigma + 1 / 4)) t true -
        ramachandraShiftedContourPiece psi X sigma
          (-(Real.log X)⁻¹) t false := by
  let s : ℂ := ramachandraShiftedPoint sigma t
  let a : ℝ := -(sigma + 1 / 4)
  let c : ℝ := 3 / 4
  let k : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hright :
      ramachandraShiftedDirect psi X sigma t =
        k * ∫ v : ℝ,
          shiftedGammaRawIntegrand psi s X ((c : ℂ) + v * I) := by
    simpa [ramachandraShiftedDirect, s, c, k,
      shiftedGammaRawIntegrand] using
      (smoothedSeries_eq_LFunctionSq_gamma_rightLine_unconditional
        psi (c := (3 / 4 : ℝ)) (by norm_num) hX
        (ramachandraShiftedPoint sigma t)
        (by simp [ramachandraShiftedPoint]; linarith))
  have hshift :
      k * ∫ v : ℝ,
          shiftedGammaRawIntegrand psi s X ((c : ℂ) + v * I) =
        DirichletCharacter.LFunction psi s ^ 2 +
          k * ∫ v : ℝ,
            shiftedGammaRawIntegrand psi s X ((a : ℂ) + v * I) := by
    simpa [s, a, c, k] using
      (full_shiftedGamma_vertical_integral_eq_residue_add_left_unconditional
        psi hpsi (ramachandraShiftedPoint sigma t) hX
        (r := (1 / 8 : ℝ)) (a := -(sigma + 1 / 4))
        (b := (3 / 4 : ℝ))
        (by norm_num)
        (by linarith)
        (by linarith)
        (by norm_num)
        (by linarith)
        (by norm_num [ramachandraShiftedPoint])
        (by norm_num [ramachandraShiftedPoint])
        (by simp [ramachandraShiftedPoint]; linarith))
  have hsplitInt := shiftedGamma_long_integral_eq_tail_add_head
    psi hprim hpsi hX (by linarith) hsigmaHi (t := t)
  have hsplit :
      k * ∫ v : ℝ,
          shiftedGammaRawIntegrand psi s X ((a : ℂ) + v * I) =
        ramachandraShiftedContourPiece psi X sigma a t true +
          ramachandraShiftedContourPiece psi X sigma a t false := by
    rw [hsplitInt]
    simp only [ramachandraShiftedContourPiece, a, k]
    ring
  have hhead :
      ramachandraShiftedContourPiece psi X sigma
          (-(Real.log X)⁻¹) t false =
        ramachandraShiftedContourPiece psi X sigma a t false := by
    simpa [a] using shiftedLongHead_eq_shiftedShortHead
      psi hprim hX hlongNear (by linarith) hnearHi hnearZHi
  dsimp [s] at hshift ⊢
  dsimp [a] at hsplit hhead
  linear_combination (-1) * hright + (-1) * hshift + (-1) * hsplit + hhead

/-- The ambient source strip and `d ∣ q` imply every elementary line-position
hypothesis in the exact nonprincipal contour identity.  Thus the remainder is
literally zero for all primitive nonprincipal characters in Theorem 6. -/
theorem LFunction_sq_eq_sourcePieces_nonprincipal
    {q d : ℕ} [NeZero q] [NeZero d]
    (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive)
    (hpsi : psi ≠ 1) {T sigma t : ℝ}
    (hdq : d ∣ q) (hT : 3 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹) :
    DirichletCharacter.LFunction psi
        (ramachandraShiftedPoint sigma t) ^ 2 =
      primitiveShiftedDirect psi T sigma t -
        primitiveShiftedLongContour psi T sigma t -
        primitiveShiftedShortContour psi T sigma t := by
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num) hqone
  have hTpos : 0 < T := by linarith
  have hqTpos : 0 < (q : ℝ) * T := mul_pos hqpos hTpos
  have hqTthree : (3 : ℝ) ≤ (q : ℝ) * T := by
    nlinarith [mul_le_mul hqone hT (by norm_num : (0 : ℝ) ≤ 3) hqpos.le]
  have hlogthree : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  have hlogqT : 1 < Real.log ((q : ℝ) * T) := by
    exact hlogthree.trans_le (Real.log_le_log (by norm_num) hqTthree)
  have hden : (100 : ℝ) < 100 * Real.log ((q : ℝ) * T) := by
    nlinarith
  have hradius : (100 * Real.log ((q : ℝ) * T))⁻¹ <
      (1 / 100 : ℝ) := by
    rw [inv_lt_comm₀ (by positivity) (by norm_num)]
    norm_num
    exact hlogqT
  have hoff : |sigma - (1 / 2 : ℝ)| < 1 / 100 :=
    hstrip.trans_lt hradius
  have hsigmaLo : 1 / 4 < sigma := by
    have := (abs_lt.mp hoff).1
    linarith
  have hsigmaHi : sigma < 3 / 4 := by
    have := (abs_lt.mp hoff).2
    linarith
  have hdthree : 3 ≤ d := three_le_modulus_of_nonprincipal psi hpsi
  have hXpos : 0 < primitiveShiftedScale d T := by
    unfold primitiveShiftedScale
    exact mul_pos (by exact_mod_cast (NeZero.pos d)) hTpos
  have hXnine : (9 : ℝ) ≤ primitiveShiftedScale d T := by
    unfold primitiveShiftedScale
    have hdthreeR : (3 : ℝ) ≤ d := by exact_mod_cast hdthree
    nlinarith [mul_le_mul hdthreeR hT (by norm_num : (0 : ℝ) ≤ 3)
      (by positivity : (0 : ℝ) ≤ d)]
  have hexpTwo : Real.exp 2 < (9 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hlogXtwo : 2 < Real.log (primitiveShiftedScale d T) := by
    rw [Real.lt_log_iff_exp_lt hXpos]
    exact hexpTwo.trans_le hXnine
  have hlogXpos : 0 < Real.log (primitiveShiftedScale d T) := by linarith
  have hinvXhalf : (Real.log (primitiveShiftedScale d T))⁻¹ <
      (1 / 2 : ℝ) := by
    rw [inv_lt_comm₀ hlogXpos (by norm_num)]
    norm_num
    exact hlogXtwo
  have hlongNear :
      -(sigma + 1 / 4) ≤
        -(Real.log (primitiveShiftedScale d T))⁻¹ := by
    have hsigmaHalf : (49 / 100 : ℝ) < sigma := by
      have := (abs_lt.mp hoff).1
      linarith
    linarith
  have hnearHi :
      -(Real.log (primitiveShiftedScale d T))⁻¹ < 0 := by
    exact neg_neg_of_pos (inv_pos.mpr hlogXpos)
  have hdleq : d ≤ q := Nat.le_of_dvd (NeZero.pos q) hdq
  have hXleqT : primitiveShiftedScale d T ≤ (q : ℝ) * T := by
    unfold primitiveShiftedScale
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdleq) hTpos.le
  have hlogXleqT : Real.log (primitiveShiftedScale d T) ≤
      Real.log ((q : ℝ) * T) := Real.log_le_log hXpos hXleqT
  have hdenCompare : Real.log (primitiveShiftedScale d T) ≤
      100 * Real.log ((q : ℝ) * T) := by
    calc
      Real.log (primitiveShiftedScale d T) ≤
          Real.log ((q : ℝ) * T) := hlogXleqT
      _ ≤ 100 * Real.log ((q : ℝ) * T) := by nlinarith
  have hradiusLeInvX :
      (100 * Real.log ((q : ℝ) * T))⁻¹ ≤
        (Real.log (primitiveShiftedScale d T))⁻¹ := by
    simpa [one_div] using
      (one_div_le_one_div_of_le hlogXpos hdenCompare)
  have hnearZHi :
      sigma - (Real.log (primitiveShiftedScale d T))⁻¹ ≤ 1 / 2 := by
    have hupper := (abs_le.mp hstrip).2
    linarith
  simpa [primitiveShiftedDirect, primitiveShiftedLongContour,
    primitiveShiftedShortContour] using
    (LFunction_sq_eq_shiftedDirect_sub_long_sub_short_nonprincipal
      psi hprim hpsi hXpos hsigmaLo hsigmaHi hlongNear hnearHi hnearZHi
      (t := t))

end
end RamachandraShiftedNonprincipalContourIdentity

#print axioms RamachandraShiftedNonprincipalContourIdentity.shiftedGamma_long_integral_eq_tail_add_head
#print axioms RamachandraShiftedNonprincipalContourIdentity.shiftedLongHead_eq_shiftedShortHead
#print axioms RamachandraShiftedNonprincipalContourIdentity.LFunction_sq_eq_shiftedDirect_sub_long_sub_short_nonprincipal
#print axioms RamachandraShiftedNonprincipalContourIdentity.LFunction_sq_eq_sourcePieces_nonprincipal
