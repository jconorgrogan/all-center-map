import GammaCompactStripSharp

/-!
# Huxley 1972, equation (3.15): the exact numerical contradiction

After the class-I and class-II alternatives have both failed, Huxley's
identity (3.5) leaves the real-part lower bound displayed in (3.15).  This
file certifies its numerical content.  The remaining source work is therefore
the analytic derivation of (3.5), (3.10), and the two class witnesses, not the
last arithmetic comparison.
-/

namespace MAPPrincipalZetaHuxley1972Equation315ClassifierArithmetic

/-- The two `1/10` tails and the `2l` class-I blocks of size `(6l)⁻¹`
still leave more than `1/3`, as soon as `Y>15/2`.  This is exactly the
displayed arithmetic in Huxley (3.15). -/
theorem equation315_realPart_gt_oneThird
    {Y ell : ℝ} (hY : 15 / 2 < Y) (hell : 0 < ell) :
    1 - 1 / Y - 1 / 10 - 1 / 10 -
        (2 * ell) * (6 * ell)⁻¹ > 1 / 3 := by
  have hYpos : 0 < Y := by linarith
  have hellne : ell ≠ 0 := ne_of_gt hell
  have htail : 1 / Y < (2 / 15 : ℝ) := by
    exact (div_lt_iff₀ hYpos).2 (by nlinarith)
  rw [show (2 * ell) * (6 * ell)⁻¹ = (1 / 3 : ℝ) by
    field_simp [hellne] <;> ring]
  nlinarith

/-- Consequently, a complex number whose real part has the lower bound in
(3.15) cannot be zero.  This is the literal final contradiction used by the
classifier. -/
theorem equation315_nonzero_of_realPart_lowerBound
    {Y ell : ℝ} (hY : 15 / 2 < Y) (hell : 0 < ell) {z : ℂ}
    (hz : 1 - 1 / Y - 1 / 10 - 1 / 10 -
        (2 * ell) * (6 * ell)⁻¹ ≤ z.re) :
    z ≠ 0 := by
  intro hzero
  have hgt := equation315_realPart_gt_oneThird hY hell
  have hpos : 0 < 1 - 1 / Y - 1 / 10 - 1 / 10 -
      (2 * ell) * (6 * ell)⁻¹ := by linarith
  rw [hzero] at hz
  norm_num only [Complex.zero_re] at hz
  exact (not_lt_of_ge hz) hpos

/-- The exact logical weld after Huxley's contour shift.  If failure of every
class-I witness forces the right side of (3.5) above `1/3` in real part, and
failure of every class-II witness forces the left side below `1/3` in norm,
the equality (3.5) forces one of the two classes.  The two implications are
kept as hypotheses because deriving them is the remaining analytic source
work; this theorem certifies that no further classifier logic is missing. -/
theorem classI_or_classII_of_equation35_bounds
    {ClassI ClassII : Prop} {left right : ℂ}
    (hequation35 : left = right)
    (hright : ¬ ClassI → 1 / 3 < right.re)
    (hleft : ¬ ClassII → ‖left‖ < 1 / 3) :
    ClassI ∨ ClassII := by
  by_contra hclasses
  push Not at hclasses
  have hright' := hright hclasses.1
  have hleft' := hleft hclasses.2
  have hreNorm : right.re ≤ ‖right‖ :=
    (le_abs_self right.re).trans (Complex.abs_re_le_norm right)
  rw [hequation35] at hleft'
  linarith

/-- Exact aggregation on the right side of (3.5).  The four losses are the
source's `1/Y`, residue `1/10`, far tail `1/10`, and at most `2l` dyadic
blocks of size `(6l)⁻¹`.  All analytic content is visible in the hypotheses;
the theorem discharges the triangle/real-part arithmetic leading to (3.15). -/
theorem equation315_right_real_gt_oneThird_of_source_bounds
    {ι : Type*} [DecidableEq ι] (blocks : Finset ι) (blockTerm : ι → ℂ)
    {Y ell : ℝ} (hY : 15 / 2 < Y) (hell : 0 < ell)
    (hcard : (blocks.card : ℝ) ≤ 2 * ell)
    (hblock : ∀ i ∈ blocks, ‖blockTerm i‖ ≤ (6 * ell)⁻¹)
    {mainTerm residueTerm tailTerm right : ℂ}
    (hmain : 1 - 1 / Y ≤ mainTerm.re)
    (hresidue : ‖residueTerm‖ ≤ 1 / 10)
    (htail : ‖tailTerm‖ ≤ 1 / 10)
    (hright : right = mainTerm + residueTerm + tailTerm +
        ∑ i ∈ blocks, blockTerm i) :
    1 / 3 < right.re := by
  have hell6 : 0 < 6 * ell := by positivity
  have hunit : 0 < (6 * ell)⁻¹ := inv_pos.mpr hell6
  have hblockRe : ∀ i ∈ blocks, -(6 * ell)⁻¹ ≤ (blockTerm i).re := by
    intro i hi
    have habs := Complex.abs_re_le_norm (blockTerm i)
    have hnorm := hblock i hi
    have hneg : -‖blockTerm i‖ ≤ (blockTerm i).re :=
      neg_le_of_abs_le habs
    linarith
  have hsumRe :
      -((blocks.card : ℝ) * (6 * ell)⁻¹) ≤
        (∑ i ∈ blocks, blockTerm i).re := by
    calc
      -((blocks.card : ℝ) * (6 * ell)⁻¹) =
          ∑ _i ∈ blocks, -(6 * ell)⁻¹ := by simp
      _ ≤ ∑ i ∈ blocks, (blockTerm i).re := by
        exact Finset.sum_le_sum fun i hi => hblockRe i hi
      _ = (∑ i ∈ blocks, blockTerm i).re := by simp
  have hblockBudget :
      (blocks.card : ℝ) * (6 * ell)⁻¹ ≤
        (2 * ell) * (6 * ell)⁻¹ :=
    mul_le_mul_of_nonneg_right hcard hunit.le
  have hsumSource :
      -((2 * ell) * (6 * ell)⁻¹) ≤
        (∑ i ∈ blocks, blockTerm i).re := by
    linarith
  have hresidueRe : -(1 / 10 : ℝ) ≤ residueTerm.re := by
    have habs := Complex.abs_re_le_norm residueTerm
    have hneg : -‖residueTerm‖ ≤ residueTerm.re :=
      neg_le_of_abs_le habs
    linarith
  have htailRe : -(1 / 10 : ℝ) ≤ tailTerm.re := by
    have habs := Complex.abs_re_le_norm tailTerm
    have hneg : -‖tailTerm‖ ≤ tailTerm.re :=
      neg_le_of_abs_le habs
    linarith
  have hsourceNumeric := equation315_realPart_gt_oneThird hY hell
  rw [hright]
  simp only [Complex.add_re]
  linarith

/-- Finite-set form of the (3.9)--(3.15) partition.  Once each zero is
classified by the literal exceptional/class-I/class-II predicates, the
cardinality inequality used by the terminal ledger is automatic. -/
theorem card_le_exceptional_add_classI_add_classII
    {α : Type*} [DecidableEq α] (zeros : Finset α)
    (exceptional classI classII : α → Prop)
    [DecidablePred exceptional] [DecidablePred classI] [DecidablePred classII]
    (hcover : ∀ z ∈ zeros, exceptional z ∨ classI z ∨ classII z) :
    zeros.card ≤
      (zeros.filter exceptional).card +
        (zeros.filter classI).card + (zeros.filter classII).card := by
  have hsubset : zeros ⊆
      zeros.filter exceptional ∪
        (zeros.filter classI ∪ zeros.filter classII) := by
    intro z hz
    rcases hcover z hz with he | hI | hII
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, he⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hI⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hII⟩))
  calc
    zeros.card ≤
        (zeros.filter exceptional ∪
          (zeros.filter classI ∪ zeros.filter classII)).card :=
      Finset.card_le_card hsubset
    _ ≤ (zeros.filter exceptional).card +
          (zeros.filter classI ∪ zeros.filter classII).card :=
      Finset.card_union_le _ _
    _ ≤ (zeros.filter exceptional).card +
          ((zeros.filter classI).card + (zeros.filter classII).card) := by
      gcongr
      exact Finset.card_union_le _ _
    _ = (zeros.filter exceptional).card +
          (zeros.filter classI).card + (zeros.filter classII).card := by omega

end MAPPrincipalZetaHuxley1972Equation315ClassifierArithmetic

#print axioms MAPPrincipalZetaHuxley1972Equation315ClassifierArithmetic.equation315_realPart_gt_oneThird
#print axioms MAPPrincipalZetaHuxley1972Equation315ClassifierArithmetic.equation315_nonzero_of_realPart_lowerBound
#print axioms MAPPrincipalZetaHuxley1972Equation315ClassifierArithmetic.classI_or_classII_of_equation35_bounds
#print axioms MAPPrincipalZetaHuxley1972Equation315ClassifierArithmetic.equation315_right_real_gt_oneThird_of_source_bounds
#print axioms MAPPrincipalZetaHuxley1972Equation315ClassifierArithmetic.card_le_exceptional_add_classI_add_classII
