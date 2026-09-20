import BHPCorrectedContourShift

/-!
# Exact external source boundaries below BHP Lemma 9

This file separates the two cited inputs used before equation (3.36):

* Rademacher's vertical-strip bound, as quoted in BHP Lemma 8;
* Titchmarsh Theorem 3.19, specialized to BHP's finite character prefix.

Neither source is replaced by equation (3.36).  In particular, the right-line
integral below is the literal `/w` integral from `BHPCorrectedContourShift`.
The first theorem after the source declarations derives the pointwise bound
on either horizontal edge and keeps every scalar visible.
-/

namespace MAPBHPRademacherTitchmarshSources

open Complex MeasureTheory
open MAPMRTLemma211AllCharacterSource
open MAPBHPCorrectedContourShift

noncomputable section

/-- BHP Lemma 8, in the exact epsilon-dependent form printed in the paper.
The quantifier order records that the implied constant may depend on epsilon
but is uniform in the character, conductor, ordinate, and strip coordinate.
The exponent is literally `1 + epsilon - sigma` (there is no factor `1/2`).
Consequently the next displayed line of BHP, which takes
`epsilon = 1 / log x0`, additionally needs quantitative control of this
epsilon-dependent constant and does not follow from this source type alone. -/
def BHPLemma8RademacherSource : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C₈ : ℝ, 0 < C₈ ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
        (sigma u : ℝ),
        0 ≤ sigma → sigma ≤ 1 + epsilon →
        ((sigma : ℂ) + u * Complex.I) ≠ 1 →
        ‖DirichletCharacter.LFunction chi
            ((sigma : ℂ) + u * Complex.I)‖ ≤
          C₈ *
            ((((q : ℝ) * (|u| + 1)) ^
                (1 + epsilon - sigma)) +
              1 / ‖((sigma : ℂ) + u * Complex.I) - 1‖)

/-- Titchmarsh Theorem 3.19 at BHP's parameters.  This is the actual
finite-height Perron approximation before the contour is moved.  The harmless
ambient logarithm is explicit, as is the endpoint term `X^(-1/2)` printed in
the source.

The statement is intentionally source-facing and remains uninhabited here. -/
def BHPTheorem319TruncatedPerronSource : Prop :=
  ∃ C₃₁₉ : ℝ, 0 < C₃₁₉ ∧
    ∀ (q X : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (t T x0 : ℝ),
      2 ≤ X → 2 ≤ T →
      (q : ℝ) ≤ x0 → (X : ℝ) ≤ x0 → T ≤ x0 →
      ‖criticalPrefixPolynomial q X chi t -
          bhpVerticalLineIntegral chi (X : ℝ) t
            ((1 / 2 : ℝ) + (Real.log x0)⁻¹) T‖ ≤
        C₃₁₉ *
          (Real.log x0 * Real.sqrt (X : ℝ) / T +
            1 / Real.sqrt (X : ℝ))

/-- The log-linear endpoint principle used on the horizontal edges.  This is
the precise deterministic reason BHP obtains a sum of the two endpoint
contributions rather than their product. -/
theorem rpow_interpolation_le_endpoint_sum
    {A B delta x c : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hdx : delta ≤ x) (hxc : x ≤ c) :
    A ^ x * B ^ (c - x) ≤
      A ^ delta * B ^ (c - delta) + A ^ c := by
  rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB,
    Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB,
    Real.rpow_def_of_pos hA]
  rw [← Real.exp_add, ← Real.exp_add]
  by_cases hAB : A ≤ B
  · have hlog : Real.log A ≤ Real.log B :=
      Real.strictMonoOn_log.monotoneOn hA hB hAB
    have hexp :
        Real.exp (Real.log A * x + Real.log B * (c - x)) ≤
          Real.exp (Real.log A * delta + Real.log B * (c - delta)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact hexp.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have hBA : B ≤ A := le_of_not_ge hAB
    have hlog : Real.log B ≤ Real.log A :=
      Real.strictMonoOn_log.monotoneOn hB hA hBA
    have hexp :
        Real.exp (Real.log A * x + Real.log B * (c - x)) ≤
          Real.exp (Real.log A * c) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact hexp.trans (le_add_of_nonneg_left (Real.exp_pos _).le)

/-- Rademacher on one literal horizontal point.  Taking `v=H` or `v=-H`
gives the top or bottom edge.  The proof is only norm algebra and the retained
Perron denominator; no maximum or endpoint interpolation is hidden. -/
theorem norm_bhpPerronIntegrand_horizontal_le
    (hRademacher : BHPLemma8RademacherSource)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {epsilon X t x v H : ℝ}
    (hepsilon : 0 < epsilon) (hX : 0 < X) (hH : 0 < H)
    (hv : |v| = H)
    (hsigma0 : 0 ≤ (1 / 2 : ℝ) + x)
    (hsigma1 : (1 / 2 : ℝ) + x ≤ 1 + epsilon)
    (hpole : ((((1 / 2 : ℝ) + x : ℝ) : ℂ) +
      (t + v) * Complex.I) ≠ 1) :
    ∃ C₈ : ℝ, 0 < C₈ ∧
      ‖bhpPerronIntegrand chi X t
          ((x : ℂ) + Complex.I * v)‖ ≤
        (C₈ *
          ((((q : ℝ) * (|t + v| + 1)) ^
              (1 + epsilon - ((1 / 2 : ℝ) + x))) +
            1 / ‖(((((1 / 2 : ℝ) + x : ℝ) : ℂ) +
              (t + v) * Complex.I) - 1)‖)) *
          ((X ^ x) / H) := by
  obtain ⟨C₈, hC₈, hsource⟩ := hRademacher epsilon hepsilon
  refine ⟨C₈, hC₈, ?_⟩
  have hpole' : ((((1 / 2 : ℝ) + x : ℝ) : ℂ) +
      ((t + v : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    simpa using hpole
  have hL := hsource q chi ((1 / 2 : ℝ) + x) (t + v)
    hsigma0 hsigma1 hpole'
  have hpow :
      ‖Complex.exp ((((x : ℂ) + Complex.I * v) * Real.log X))‖ =
        X ^ x := by
    rw [← PerronKernel.verticalPower_eq_exp hX x v]
    exact PerronKernel.norm_verticalPower hX x v
  have hden : H ≤ ‖(x : ℂ) + Complex.I * v‖ := by
    rw [← hv]
    calc
      |v| = |(((x : ℂ) + Complex.I * v).im)| := by simp
      _ ≤ ‖(x : ℂ) + Complex.I * v‖ := Complex.abs_im_le_norm _
  have hdenpos : 0 < ‖(x : ℂ) + Complex.I * v‖ := hH.trans_le hden
  have hpow0 : 0 ≤ X ^ x := Real.rpow_nonneg hX.le _
  let A : ℝ := (((q : ℝ) * (|t + v| + 1)) ^
      (1 + epsilon - ((1 / 2 : ℝ) + x))) +
        1 / ‖(((((1 / 2 : ℝ) + x : ℝ) : ℂ) +
          (t + v) * Complex.I) - 1)‖
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  unfold bhpPerronIntegrand
  rw [norm_div, norm_mul, hpow]
  have harg :
      ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) +
          ((x : ℂ) + Complex.I * v)) =
        ((((1 / 2 : ℝ) + x : ℝ) : ℂ) +
          (t + v) * Complex.I) := by
    push_cast
    ring
  rw [harg]
  calc
    ‖DirichletCharacter.LFunction chi
          (((1 / 2 + x : ℝ) : ℂ) +
            ((t : ℂ) + (v : ℂ)) * Complex.I)‖ * X ^ x /
          ‖(x : ℂ) + Complex.I * v‖ ≤
        (C₈ * A) * X ^ x / ‖(x : ℂ) + Complex.I * v‖ := by
      gcongr
      simpa [A] using hL
    _ ≤ (C₈ * A) * X ^ x / H := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg hC₈.le hA0) hpow0) hH hden
    _ = (C₈ * A) * (X ^ x / H) := by ring
    _ = (C₈ *
          ((((q : ℝ) * (|t + v| + 1)) ^
              (1 + epsilon - ((1 / 2 : ℝ) + x))) +
            1 / ‖(((((1 / 2 : ℝ) + x : ℝ) : ℂ) +
              (t + v) * Complex.I) - 1)‖)) *
          (X ^ x / H) := by rfl

/-- Deterministic integration of both oriented horizontal edges.  The
pointwise hypotheses can be supplied by
`norm_bhpPerronIntegrand_horizontal_le` at `v=H` and `v=-H`. -/
theorem norm_bhpHorizontalBoundaryIntegral_le_of_pointwise
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X t delta c H Mtop Mbottom : ℝ}
    (hdc : delta ≤ c) (hMtop : 0 ≤ Mtop) (hMbottom : 0 ≤ Mbottom)
    (htop : ∀ x ∈ Set.uIoc delta c,
      ‖bhpPerronIntegrand chi X t
        ((x : ℂ) + Complex.I * H)‖ ≤ Mtop)
    (hbottom : ∀ x ∈ Set.uIoc delta c,
      ‖bhpPerronIntegrand chi X t
        ((x : ℂ) - Complex.I * H)‖ ≤ Mbottom) :
    ‖bhpHorizontalBoundaryIntegral chi X t delta c H‖ ≤
      ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I‖ *
        ((Mtop + Mbottom) * (c - delta)) := by
  have htopInt :
      ‖∫ x in delta..c,
          bhpPerronIntegrand chi X t
            ((x : ℂ) + Complex.I * H)‖ ≤
        Mtop * (c - delta) := by
    simpa [abs_of_nonneg (sub_nonneg.mpr hdc)] using
      (intervalIntegral.norm_integral_le_of_norm_le_const htop)
  have hbottomInt :
      ‖∫ x in delta..c,
          bhpPerronIntegrand chi X t
            ((x : ℂ) - Complex.I * H)‖ ≤
        Mbottom * (c - delta) := by
    simpa [abs_of_nonneg (sub_nonneg.mpr hdc)] using
      (intervalIntegral.norm_integral_le_of_norm_le_const hbottom)
  let k : ℂ := (((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I
  change ‖k * (∫ x in delta..c, bhpPerronIntegrand chi X t
      ((x : ℂ) + Complex.I * H)) -
    k * (∫ x in delta..c, bhpPerronIntegrand chi X t
      ((x : ℂ) - Complex.I * H))‖ ≤
      ‖k‖ * ((Mtop + Mbottom) * (c - delta))
  calc
    ‖k * (∫ x in delta..c, bhpPerronIntegrand chi X t
          ((x : ℂ) + Complex.I * H)) -
        k * (∫ x in delta..c, bhpPerronIntegrand chi X t
          ((x : ℂ) - Complex.I * H))‖ ≤
        ‖k * (∫ x in delta..c, bhpPerronIntegrand chi X t
          ((x : ℂ) + Complex.I * H))‖ +
        ‖k * (∫ x in delta..c, bhpPerronIntegrand chi X t
          ((x : ℂ) - Complex.I * H))‖ := norm_sub_le _ _
    _ = ‖k‖ * ‖∫ x in delta..c, bhpPerronIntegrand chi X t
          ((x : ℂ) + Complex.I * H)‖ +
        ‖k‖ * ‖∫ x in delta..c, bhpPerronIntegrand chi X t
          ((x : ℂ) - Complex.I * H)‖ := by
      exact congrArg₂ (fun a b : ℝ => a + b)
        (norm_mul k (∫ x in delta..c, bhpPerronIntegrand chi X t
          ((x : ℂ) + Complex.I * H)))
        (norm_mul k (∫ x in delta..c, bhpPerronIntegrand chi X t
          ((x : ℂ) - Complex.I * H)))
    _ ≤ ‖k‖ * (Mtop * (c - delta)) +
        ‖k‖ * (Mbottom * (c - delta)) := by gcongr
    _ = ‖k‖ * ((Mtop + Mbottom) * (c - delta)) := by ring

end
end MAPBHPRademacherTitchmarshSources

#print axioms MAPBHPRademacherTitchmarshSources.norm_bhpPerronIntegrand_horizontal_le
#print axioms MAPBHPRademacherTitchmarshSources.rpow_interpolation_le_endpoint_sum
#print axioms MAPBHPRademacherTitchmarshSources.norm_bhpHorizontalBoundaryIntegral_le_of_pointwise
