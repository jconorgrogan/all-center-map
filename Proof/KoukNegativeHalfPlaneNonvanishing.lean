import KoukGammaFactorLogDerivative
import TrivialZeroEndpoint

/-!
# Negative-half-plane nonvanishing away from trivial Gamma zeros

This formalizes the zero classification needed for the omitted far-left move
in Koukoulopoulos Theorem 11.3.  For a primitive character and `Re s < 0`,
the functional equation and Euler-product nonvanishing show that `L(s,chi)`
can vanish only where its Gamma factor vanishes.  In particular every
negative half-integer vertical line is zero-free for both parities.
-/

namespace KoukNegativeHalfPlaneNonvanishing

open Complex
open PrimitiveTruncatedExplicitFormulaBridge
open MAPTrivialZeroEndpoint

noncomputable section

/-- Completed L is nonzero in the negative half-plane for a primitive
character.  Trivial zeros arise only after division by the Gamma factor. -/
theorem completedLFunction_ne_zero_of_primitive_of_re_neg
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) {s : ℂ} (hs : s.re < 0) :
    DirichletCharacter.completedLFunction chi s ≠ 0 := by
  let u : ℂ := 1 - s
  have hure : 1 < u.re := by
    dsimp only [u]
    simp only [sub_re, one_re]
    linarith
  have hu0 : u ≠ 0 := by
    intro hu
    rw [hu] at hure
    norm_num at hure
  have hLinv : DirichletCharacter.LFunction chi⁻¹ u ≠ 0 :=
    LFunction_ne_zero_of_one_lt_re chi⁻¹ hure
  have heqInv :=
    DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi⁻¹ u
      (Or.inl hu0)
  have hcompInv :
      DirichletCharacter.completedLFunction chi⁻¹ u ≠ 0 := by
    intro hzero
    rw [hzero, zero_div] at heqInv
    exact hLinv heqInv
  have hqpow : (q : ℂ) ^ (u - 1 / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr <| Or.inl <|
      Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hroot := rootNumber_ne_zero_of_primitive hprimitive
  have hFE := hprimitive.completedLFunction_one_sub u
  have hleft : 1 - u = s := by
    dsimp only [u]
    ring
  rw [hleft] at hFE
  rw [hFE]
  exact mul_ne_zero (mul_ne_zero hqpow hroot) hcompInv

/-- In `Re s < 0`, primitive L is nonzero at every point where the Gamma
factor is nonzero. -/
theorem LFunction_ne_zero_of_primitive_of_re_neg_of_gamma_ne_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) {s : ℂ} (hs : s.re < 0)
    (hgamma : DirichletCharacter.gammaFactor chi s ≠ 0) :
    DirichletCharacter.LFunction chi s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz] at hs
    norm_num at hs
  have heq := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    chi s (Or.inl hs0)
  rw [heq]
  exact div_ne_zero
    (completedLFunction_ne_zero_of_primitive_of_re_neg chi hprimitive hs)
    hgamma

/-- The regularized L-function used by the compact divisor has the same
negative-half-plane nonvanishing. -/
theorem regularizedLFunction_ne_zero_of_primitive_of_re_neg_of_gamma_ne_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) {s : ℂ} (hs : s.re < 0)
    (hgamma : DirichletCharacter.gammaFactor chi s ≠ 0) :
    DirichletZeros.regularizedLFunction chi s ≠ 0 := by
  have hL := LFunction_ne_zero_of_primitive_of_re_neg_of_gamma_ne_zero
    chi hprimitive hs hgamma
  classical
  by_cases hchi : chi = 1
  · have hs1 : s ≠ 1 := by
      intro hsone
      rw [hsone] at hs
      norm_num at hs
    simp only [DirichletZeros.regularizedLFunction, hchi, if_true]
    unfold DirichletCharacter.LFunctionTrivChar₁
    rw [Function.update_of_ne hs1]
    have hLtriv : DirichletCharacter.LFunctionTrivChar q s ≠ 0 := by
      simpa only [hchi] using hL
    exact mul_ne_zero (sub_ne_zero.mpr hs1) hLtriv
  · simpa [DirichletZeros.regularizedLFunction, hchi] using hL

/-- Canonical negative half-integer left edge. -/
def negativeHalfIntegerEdge (M : ℕ) : ℝ :=
  -(M : ℝ) - 1 / 2

theorem negativeHalfIntegerEdge_neg (M : ℕ) :
    negativeHalfIntegerEdge M < 0 := by
  unfold negativeHalfIntegerEdge
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  linarith

/-- Neither even nor odd real Gamma factor vanishes on a negative
half-integer vertical line. -/
theorem gammaFactor_ne_zero_on_negativeHalfIntegerLine
    {q : ℕ} (chi : DirichletCharacter ℂ q) (M : ℕ) (t : ℝ) :
    DirichletCharacter.gammaFactor chi
      ((negativeHalfIntegerEdge M : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  rcases chi.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def, Ne, Complex.Gammaℝ_eq_zero_iff]
    push_neg
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num [negativeHalfIntegerEdge] at hre
    have hre' : (2 * M + 1 : ℝ) = 4 * n := by
      push_cast
      linarith
    have hnat : 2 * M + 1 = 4 * n := by exact_mod_cast hre'
    omega
  · rw [hodd.gammaFactor_def, Ne, Complex.Gammaℝ_eq_zero_iff]
    push_neg
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num [negativeHalfIntegerEdge] at hre
    have hre' : (2 * M + 1 : ℝ) = 4 * n + 2 := by
      push_cast
      linarith
    have hnat : 2 * M + 1 = 4 * n + 2 := by exact_mod_cast hre'
    omega

/-- Gamma-factor zeros are real; every point of nonzero imaginary part is
therefore Gamma-zero-free, independently of parity. -/
theorem gammaFactor_ne_zero_of_im_ne_zero
    {q : ℕ} (chi : DirichletCharacter ℂ q) {s : ℂ}
    (him : s.im ≠ 0) :
    DirichletCharacter.gammaFactor chi s ≠ 0 := by
  rcases chi.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def, Ne, Complex.Gammaℝ_eq_zero_iff]
    push_neg
    intro n hn
    have hi := congrArg Complex.im hn
    simp at hi
    exact him hi
  · rw [hodd.gammaFactor_def, Ne, Complex.Gammaℝ_eq_zero_iff]
    push_neg
    intro n hn
    have hi := congrArg Complex.im hn
    simp at hi
    exact him hi

/-- Negative-half-plane nonvanishing on every nonreal horizontal edge. -/
theorem regularizedLFunction_ne_zero_of_primitive_of_re_neg_of_im_ne_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) {s : ℂ}
    (hre : s.re < 0) (him : s.im ≠ 0) :
    DirichletZeros.regularizedLFunction chi s ≠ 0 :=
  regularizedLFunction_ne_zero_of_primitive_of_re_neg_of_gamma_ne_zero
    chi hprimitive hre (gammaFactor_ne_zero_of_im_ne_zero chi him)

/-- The entire canonical far-left vertical segment is zero-free. -/
theorem regularizedLFunction_ne_zero_on_negativeHalfIntegerLine
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) (M : ℕ) (t : ℝ) :
    DirichletZeros.regularizedLFunction chi
      ((negativeHalfIntegerEdge M : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  apply regularizedLFunction_ne_zero_of_primitive_of_re_neg_of_gamma_ne_zero
    chi hprimitive
  · simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    exact negativeHalfIntegerEdge_neg M
  · exact gammaFactor_ne_zero_on_negativeHalfIntegerLine chi M t

/-- Extend full-critical-strip horizontal nonvanishing across the canonical
negative half-integer left edge and past the Euler-product line. -/
theorem negativeHalfInteger_horizontal_nonzero_of_fullStrip
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) (M : ℕ) {T c : ℝ}
    (hT : 0 < T) (hc : 1 ≤ c)
    (hbottomFull : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      DirichletZeros.regularizedLFunction chi
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopFull : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      DirichletZeros.regularizedLFunction chi
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    (∀ r ∈ Set.Icc (negativeHalfIntegerEdge M) c,
      DirichletZeros.regularizedLFunction chi
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0) ∧
    (∀ r ∈ Set.Icc (negativeHalfIntegerEdge M) c,
      DirichletZeros.regularizedLFunction chi
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) := by
  constructor
  · intro r hr
    by_cases hr0 : r < 0
    · apply regularizedLFunction_ne_zero_of_primitive_of_re_neg_of_im_ne_zero
        chi hprimitive
      · simpa only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          mul_zero, neg_zero, zero_mul, sub_zero, add_zero] using hr0
      · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
          mul_one, zero_mul, add_zero]
        linarith
    · have hrzero : 0 ≤ r := not_lt.mp hr0
      by_cases hr1 : r ≤ 1
      · exact hbottomFull r ⟨hrzero, hr1⟩
      · apply MAPMellinDetectorLeaf.regularizedLFunction_ne_zero_of_one_le_re
        simpa only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          mul_zero, neg_zero, zero_mul, sub_zero, add_zero] using
          (not_le.mp hr1).le
  · intro r hr
    by_cases hr0 : r < 0
    · apply regularizedLFunction_ne_zero_of_primitive_of_re_neg_of_im_ne_zero
        chi hprimitive
      · simpa only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          mul_zero, zero_mul, sub_zero, add_zero] using hr0
      · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
          mul_one, zero_mul, add_zero]
        simpa using hT.ne'
    · have hrzero : 0 ≤ r := not_lt.mp hr0
      by_cases hr1 : r ≤ 1
      · exact htopFull r ⟨hrzero, hr1⟩
      · apply MAPMellinDetectorLeaf.regularizedLFunction_ne_zero_of_one_le_re
        simpa only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          mul_zero, zero_mul, sub_zero, add_zero] using
          (not_le.mp hr1).le

end
end KoukNegativeHalfPlaneNonvanishing

#print axioms KoukNegativeHalfPlaneNonvanishing.completedLFunction_ne_zero_of_primitive_of_re_neg
#print axioms KoukNegativeHalfPlaneNonvanishing.regularizedLFunction_ne_zero_on_negativeHalfIntegerLine
