import KoukTheorem113FullSupportFormula
import KoukNegativeHalfPlaneNonvanishing

/-!
# The `-1/2` Kouk rectangle has no negative-strip zeros

For a primitive character the functional equation puts every zero with
negative real part at an archimedean Gamma pole.  There is no such pole in
`-1/2 ≤ Re s < 0`, for either parity.  Thus choosing the canonical left edge
`-1/2` makes the auxiliary negative-strip divisor literally empty; no
triangle estimate or limiting far-left cancellation is required.
-/

namespace KoukNegativeHalfStripEmpty

open Set DirichletZeros PrimitiveExplicitFormulaSpine
open KoukTheorem113FullSupportFormula
open KoukNegativeHalfPlaneNonvanishing

noncomputable section

/-- Neither parity has an archimedean zero in the open negative half-strip
whose left boundary is `-1/2`. -/
theorem gammaFactor_ne_zero_on_negativeHalfStrip
    {q : ℕ} (chi : DirichletCharacter ℂ q) {s : ℂ}
    (hleft : (-1 / 2 : ℝ) ≤ s.re) (hright : s.re < 0) :
    DirichletCharacter.gammaFactor chi s ≠ 0 := by
  rcases chi.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def, Ne, Complex.Gammaℝ_eq_zero_iff]
    push_neg
    intro n hn
    have hre := congrArg Complex.re hn
    simp at hre
    have hnzero : n = 0 := by
      by_contra hn0
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith
    subst n
    norm_num at hre
    linarith
  · rw [hodd.gammaFactor_def, Ne, Complex.Gammaℝ_eq_zero_iff]
    push_neg
    intro n hn
    have hre := congrArg Complex.re hn
    simp at hre
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith

/-- The primitive regularized L-function is zero-free throughout
`-1/2 ≤ Re s < 0`. -/
theorem regularizedLFunction_ne_zero_on_negativeHalfStrip
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) {s : ℂ}
    (hleft : (-1 / 2 : ℝ) ≤ s.re) (hright : s.re < 0) :
    regularizedLFunction chi s ≠ 0 :=
  regularizedLFunction_ne_zero_of_primitive_of_re_neg_of_gamma_ne_zero
    chi hprimitive hright
      (gammaFactor_ne_zero_on_negativeHalfStrip chi hleft hright)

/-- With left edge `-1/2`, the difference between the negative rectangle
divisor and the displayed full support is exactly empty. -/
theorem negativeStripZeroSupport_negativeHalf_eq_empty
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) (T : ℝ) :
    negativeStripZeroSupport chi (negativeHalfIntegerEdge 0) T = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro rho hrho
  have hparts := Finset.mem_sdiff.mp hrho
  have houter := hparts.1
  have hnotFull := hparts.2
  have hrect := mem_zeroRectangle_of_mem_zeroSupport
    chi (negativeHalfIntegerEdge 0) T houter
  have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport
    chi (negativeHalfIntegerEdge 0) T houter
  have hreNeg : rho.re < 0 := by
    by_contra hnot
    have hre0 : 0 ≤ rho.re := not_lt.mp hnot
    have hfullRect : rho ∈ zeroRectangle 0 T := by
      rw [zeroRectangle, Complex.mem_reProdIm]
      exact ⟨⟨hre0, hrect.1.2⟩, hrect.2⟩
    exact hnotFull ((MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
      chi 0 T hfullRect).2 hzero)
  have hleft : (-1 / 2 : ℝ) ≤ rho.re := by
    have h := hrect.1.1
    norm_num [negativeHalfIntegerEdge] at h ⊢
    exact h
  exact (regularizedLFunction_ne_zero_on_negativeHalfStrip
    chi hprimitive hleft hreNeg) hzero

end
end KoukNegativeHalfStripEmpty

#print axioms KoukNegativeHalfStripEmpty.negativeStripZeroSupport_negativeHalf_eq_empty
