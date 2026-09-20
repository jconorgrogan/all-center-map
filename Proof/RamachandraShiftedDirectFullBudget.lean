import RamachandraShiftedDirectAssembly

/-!
# Full shifted direct-series second moment

This file combines the exact finite dyadic assembly with the explicit
exponentially small infinite tail.  It closes the passage from the literal
continuous direct series `S(s)` to a finite source budget; no fourth-moment
or contour premise is used.
-/

namespace RamachandraShiftedDirectFullBudget

open scoped BigOperators Interval LSeries.notation
open Complex MeasureTheory CGLProofDAG
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedCoefficientEnergy
open RamachandraShiftedDirectSeries
open RamachandraShiftedDirectAssembly
open MRTLemma215DyadicPartition
open MAPMRTLemma210OrthogonalityReduction

noncomputable section

/-- The explicit uniform tail envelope after the source prefix `[1,M]`. -/
def shiftedDirectTailEnvelope (M : ℕ) (X : ℝ) : ℝ :=
  (M + 1 : ℝ) * (Real.exp (-(1 / X))) ^ (M + 1) *
    (Real.exp (-(1 / X)) /
        (1 - Real.exp (-(1 / X))) ^ 2 +
      (1 - Real.exp (-(1 / X)))⁻¹)

/-- The literal shifted smoothed direct series is continuous in the ordinate.
The proof is uniform convergence against the same geometric majorant used for
its explicit tail. -/
theorem continuous_primitiveShiftedDirect
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {T sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hscale : 0 < primitiveShiftedScale d T) :
    Continuous (fun t => primitiveShiftedDirect psi T sigma t) := by
  let X := primitiveShiftedScale d T
  let r : ℝ := Real.exp (-(1 / X))
  have hneg : -(1 / X) < 0 := by
    have hinv : 0 < 1 / X := one_div_pos.mpr hscale
    linarith
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hneg
  have hrnorm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_pos hrpos] using hrlt
  have hmajor : Summable (fun n : ℕ => (n : ℝ) * r ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).summable
  have hcont' : ∀ n : ℕ,
      Continuous (fun t => shiftedDirectTerm psi sigma X t n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      simpa [shiftedDirectTerm, LSeries.term_zero] using
        (continuous_const : Continuous (fun _t : ℝ => (0 : ℂ)))
    · have heq : (fun t => shiftedDirectTerm psi sigma X t n) =
          fun t => (shiftedSmoothedDivisorBlockCoeff sigma X n * psi n) *
            twistedPhase n t := by
        funext t
        exact shiftedDirectTerm_eq_blockTerm psi (Nat.pos_of_ne_zero hn)
          sigma X t
      rw [heq]
      unfold twistedPhase
      fun_prop
  have hbound : ∀ n t,
      ‖shiftedDirectTerm psi sigma X t n‖ ≤ (n : ℝ) * r ^ n := by
    intro n t
    by_cases hn : n = 0
    · subst n
      simp [shiftedDirectTerm, LSeries.term_zero]
    · have h := norm_shiftedDirectTerm_le_nat_mul_exp psi
          (Nat.pos_of_ne_zero hn) (X := X) (t := t) hsigma
      rw [exp_neg_nat_div_eq_pow (X := X) n] at h
      simpa [r] using h
  have hsum := continuous_tsum hcont' hmajor hbound
  change Continuous (fun t => ∑' n : ℕ,
    shiftedDirectTerm psi sigma X t n)
  exact hsum

/-- Complete all-character direct-series second moment: a certified finite
prefix plus the literal explicit tail.  Restricting to primitive characters
can only decrease the left side. -/
theorem integral_sum_norm_primitiveShiftedDirect_sq_le
    (d M : ℕ) [NeZero d] (hM : 1 ≤ M)
    {T Y sigma delta : ℝ}
    (hT : 0 < T)
    (hNY : ∀ j : Fin (sourceDyadicCount M),
      (2 * 2 ^ (j : ℕ) : ℕ) ≤ Y)
    (hdelta : 0 ≤ delta)
    (hsigma : |sigma - 1 / 2| ≤ delta)
    (hsigma0 : 0 ≤ sigma) :
    (∫ t in (-T)..T,
      ∑ psi : DirichletCharacter ℂ d,
        ‖primitiveShiftedDirect psi T sigma t‖ ^ 2) ≤
      2 * (4 * (d : ℝ) * T +
        2 * (sourceDyadicCount M : ℝ) *
          ∑ j : Fin (sourceDyadicCount M),
            directSourceShellCost d M T Y delta j) +
      4 * (d : ℝ) * T *
        shiftedDirectTailEnvelope M (primitiveShiftedScale d T) ^ 2 := by
  let X := primitiveShiftedScale d T
  let B := shiftedDirectTailEnvelope M X
  let P : DirichletCharacter ℂ d → ℝ → ℂ := fun psi t =>
    twistedFinitePolynomial d (Finset.Icc 1 M)
      (shiftedSmoothedDivisorBlockCoeff sigma X) psi t
  have hscale : 0 < X := by
    dsimp [X, primitiveShiftedScale]
    exact mul_pos (by exact_mod_cast (NeZero.pos d)) hT
  have htail (psi : DirichletCharacter ℂ d) (t : ℝ) :
      ‖∑' k : ℕ, shiftedDirectTerm psi sigma X t (k + (M + 1))‖ ≤ B := by
    simpa [B, shiftedDirectTailEnvelope] using
      norm_shiftedDirectTail_le psi M hsigma0 hscale (t := t)
  have hpoint (psi : DirichletCharacter ℂ d) (t : ℝ) :
      ‖primitiveShiftedDirect psi T sigma t‖ ^ 2 ≤
        2 * ‖P psi t‖ ^ 2 + 2 * B ^ 2 := by
    rw [primitiveShiftedDirect_eq_prefix_add_tail psi M hsigma0 hscale,
      sum_range_shiftedDirectTerm_eq_prefixPolynomial]
    have htri := norm_add_le (P psi t)
      (∑' k : ℕ, shiftedDirectTerm psi sigma X t (k + (M + 1)))
    have hsq : ‖P psi t +
        ∑' k : ℕ, shiftedDirectTerm psi sigma X t (k + (M + 1))‖ ^ 2 ≤
        (‖P psi t‖ +
          ‖∑' k : ℕ, shiftedDirectTerm psi sigma X t (k + (M + 1))‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 htri
    calc
      _ ≤ (‖P psi t‖ +
          ‖∑' k : ℕ,
            shiftedDirectTerm psi sigma X t (k + (M + 1))‖) ^ 2 := hsq
      _ ≤ (‖P psi t‖ + B) ^ 2 := by
        gcongr
        exact htail psi t
      _ ≤ 2 * ‖P psi t‖ ^ 2 + 2 * B ^ 2 := by
        nlinarith [sq_nonneg (‖P psi t‖ - B)]
  have hleftCont : Continuous (fun t : ℝ =>
      ∑ psi : DirichletCharacter ℂ d,
        ‖primitiveShiftedDirect psi T sigma t‖ ^ 2) := by
    apply continuous_finsetSum
    intro psi hpsi
    exact (continuous_primitiveShiftedDirect psi hsigma0 hscale).norm.pow 2
  have hprefixCont : Continuous (fun t : ℝ =>
      ∑ psi : DirichletCharacter ℂ d, ‖P psi t‖ ^ 2) := by
    apply continuous_finsetSum
    intro psi hpsi
    dsimp [P]
    unfold twistedFinitePolynomial twistedPhase
    fun_prop
  have hcard : (Fintype.card (DirichletCharacter ℂ d) : ℝ) ≤ d := by
    exact_mod_cast MAPMRTCorollary53Source.card_dirichletCharacters_le_modulus d
  calc
    (∫ t in (-T)..T,
      ∑ psi : DirichletCharacter ℂ d,
        ‖primitiveShiftedDirect psi T sigma t‖ ^ 2) ≤
      ∫ t in (-T)..T,
        (2 * ∑ psi : DirichletCharacter ℂ d, ‖P psi t‖ ^ 2 +
          2 * (Fintype.card (DirichletCharacter ℂ d) : ℝ) * B ^ 2) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact hleftCont.intervalIntegrable _ _
      · exact ((continuous_const.mul hprefixCont).add continuous_const).intervalIntegrable _ _
      · intro t ht
        calc
          (∑ psi : DirichletCharacter ℂ d,
              ‖primitiveShiftedDirect psi T sigma t‖ ^ 2) ≤
            ∑ psi : DirichletCharacter ℂ d,
              (2 * ‖P psi t‖ ^ 2 + 2 * B ^ 2) :=
            Finset.sum_le_sum fun psi hpsi => hpoint psi t
          _ = 2 * ∑ psi : DirichletCharacter ℂ d, ‖P psi t‖ ^ 2 +
              2 * (Fintype.card (DirichletCharacter ℂ d) : ℝ) * B ^ 2 := by
            rw [Finset.sum_add_distrib]
            simp_rw [← Finset.mul_sum]
            simp
            ring
    _ = 2 * (∫ t in (-T)..T,
          ∑ psi : DirichletCharacter ℂ d, ‖P psi t‖ ^ 2) +
        4 * T * (Fintype.card (DirichletCharacter ℂ d) : ℝ) * B ^ 2 := by
      rw [intervalIntegral.integral_add
        (f := fun t => 2 * ∑ psi : DirichletCharacter ℂ d, ‖P psi t‖ ^ 2)
        (g := fun _t => 2 * (Fintype.card (DirichletCharacter ℂ d) : ℝ) * B ^ 2)
        ((continuous_const.mul hprefixCont).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ 2 * (4 * (d : ℝ) * T +
          2 * (sourceDyadicCount M : ℝ) *
            ∑ j : Fin (sourceDyadicCount M),
              directSourceShellCost d M T Y delta j) +
        4 * T * (d : ℝ) * B ^ 2 := by
      have hp := integral_sum_norm_shiftedDirectPrefix_sq_le
        d M hM (T := T) (X := X) (Y := Y) (sigma := sigma)
          (delta := delta) hT.le hscale hNY hdelta hsigma
      have htailCard :
          4 * T * (Fintype.card (DirichletCharacter ℂ d) : ℝ) * B ^ 2 ≤
            4 * T * (d : ℝ) * B ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcard (by positivity)) (sq_nonneg B)
      exact add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num)) htailCard
    _ = _ := by dsimp only [B, X]; ring

/-- Primitive-family form of the full direct-series estimate.  This is the
literal `S` leaf in `PrimitiveShiftedContourBudgets`, before the final
one-variable choice of the truncation parameter `M`. -/
theorem primitiveFamilyDirectSecondMoment_le_explicit
    (d M : ℕ) [NeZero d] (hM : 1 ≤ M)
    {T Y sigma delta : ℝ}
    (hT : 0 < T)
    (hNY : ∀ j : Fin (sourceDyadicCount M),
      (2 * 2 ^ (j : ℕ) : ℕ) ≤ Y)
    (hdelta : 0 ≤ delta)
    (hsigma : |sigma - 1 / 2| ≤ delta)
    (hsigma0 : 0 ≤ sigma) :
    primitiveFamilyDirectSecondMoment d T sigma ≤
      2 * (4 * (d : ℝ) * T +
        2 * (sourceDyadicCount M : ℝ) *
          ∑ j : Fin (sourceDyadicCount M),
            directSourceShellCost d M T Y delta j) +
      4 * (d : ℝ) * T *
        shiftedDirectTailEnvelope M (primitiveShiftedScale d T) ^ 2 := by
  classical
  have hscale : 0 < primitiveShiftedScale d T := by
    unfold primitiveShiftedScale
    exact mul_pos (by exact_mod_cast (NeZero.pos d)) hT
  have hcont (psi : DirichletCharacter ℂ d) : Continuous (fun t =>
      ‖primitiveShiftedDirect psi T sigma t‖ ^ 2) :=
    (continuous_primitiveShiftedDirect psi hsigma0 hscale).norm.pow 2
  calc
    primitiveFamilyDirectSecondMoment d T sigma ≤
        ∑ psi : DirichletCharacter ℂ d,
          ∫ t in (-T)..T, ‖primitiveShiftedDirect psi T sigma t‖ ^ 2 := by
      unfold primitiveFamilyDirectSecondMoment
      apply Finset.sum_le_sum
      intro psi hpsi
      by_cases hp : psi.IsPrimitive
      · simp [hp]
      · simp only [hp, if_false]
        apply intervalIntegral.integral_nonneg (by linarith)
        intro t ht
        positivity
    _ = ∫ t in (-T)..T,
        ∑ psi : DirichletCharacter ℂ d,
          ‖primitiveShiftedDirect psi T sigma t‖ ^ 2 := by
      rw [intervalIntegral.integral_finsetSum]
      intro psi hpsi
      exact (hcont psi).intervalIntegrable _ _
    _ ≤ _ := integral_sum_norm_primitiveShiftedDirect_sq_le
      d M hM hT hNY hdelta hsigma hsigma0


end
end RamachandraShiftedDirectFullBudget

#print axioms RamachandraShiftedDirectFullBudget.continuous_primitiveShiftedDirect
#print axioms RamachandraShiftedDirectFullBudget.integral_sum_norm_primitiveShiftedDirect_sq_le
#print axioms RamachandraShiftedDirectFullBudget.primitiveFamilyDirectSecondMoment_le_explicit
