import GammaCompactStripSharp

/-!
# Huxley 1972, equation (3.14): a certified Gamma-shell normalizer

Huxley chooses `c₂>0` so that a low central Gamma block plus the dyadic
Gamma tails have total normalized mass at most `2*pi/3`.  The source leaves
the choice implicit.  Here the sharp central-line Gamma bound makes the
choice explicit.  This is an elementary summability statement, not a
zero-density or large-value input.
-/

namespace MAPPrincipalZetaHuxley1972Equation314GammaNormalizer

open Filter
open MAPGammaCompactStripSharp

noncomputable section

/-- The explicit majorant for the source shell indexed by `n=k+1`:
`3 * 2^(2n+2) * exp(-(pi/2) 2^n)`. -/
def equation314TailMajorant (k : ℕ) : ℝ :=
  3 * (2 : ℝ) ^ (2 * (k + 1) + 2) *
    Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ (k + 1))

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega

private theorem four_mul_exp_neg_pi_half_lt_one :
    4 * Real.exp (-(Real.pi / 2)) < 1 := by
  have hexp32 : (4 : ℝ) < Real.exp (3 / 2 : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg
      (x := (3 / 2 : ℝ)) (by norm_num) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hpi : (3 / 2 : ℝ) < Real.pi / 2 := by
    linarith [Real.pi_gt_three]
  have hexppi : (4 : ℝ) < Real.exp (Real.pi / 2) :=
    hexp32.trans (Real.exp_lt_exp.mpr hpi)
  have hexppos : 0 < Real.exp (Real.pi / 2) := Real.exp_pos _
  rw [show Real.exp (-(Real.pi / 2)) =
      (Real.exp (Real.pi / 2))⁻¹ by rw [Real.exp_neg]]
  rw [← div_eq_mul_inv]
  exact (div_lt_one hexppos).2 hexppi

/-- The literal (3.14) tail majorant is summable. -/
theorem summable_equation314TailMajorant :
    Summable equation314TailMajorant := by
  let r : ℝ := 4 * Real.exp (-(Real.pi / 2))
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    simpa [r] using four_mul_exp_neg_pi_half_lt_one
  have hgeom : Summable (fun k : ℕ => 48 * r ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left 48
  apply Summable.of_nonneg_of_le
    (fun k => by unfold equation314TailMajorant; positivity) _ hgeom
  intro k
  have hpowNat : k + 1 ≤ 2 ^ (k + 1) := nat_le_two_pow (k + 1)
  have hpi0 : 0 < Real.pi / 2 := by positivity
  have hexpMono :
      Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ (k + 1)) ≤
        Real.exp (-(Real.pi / 2) * (k + 1)) := by
    have hcast : ((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      exact_mod_cast hpowNat
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left
      (by simpa [Nat.cast_add, Nat.cast_one] using hcast)
      (by nlinarith [Real.pi_pos])
  have hpowSplit :
      (2 : ℝ) ^ (2 * (k + 1) + 2) = 16 * (4 : ℝ) ^ k := by
    rw [show 2 * (k + 1) + 2 = 2 * k + 4 by omega,
      pow_add, pow_mul]
    norm_num
    ring
  have hexpSplit :
      Real.exp (-(Real.pi / 2) * (k + 1)) =
        Real.exp (-(Real.pi / 2)) *
          (Real.exp (-(Real.pi / 2))) ^ k := by
    rw [show -(Real.pi / 2) * (k + 1) =
        -(Real.pi / 2) + k * (-(Real.pi / 2)) by ring,
      Real.exp_add, Real.exp_nat_mul]
  have hexpOne : Real.exp (-(Real.pi / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos]
  calc
    equation314TailMajorant k =
        3 * (2 : ℝ) ^ (2 * (k + 1) + 2) *
          Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ (k + 1)) := rfl
    _ ≤ 3 * (2 : ℝ) ^ (2 * (k + 1) + 2) *
          Real.exp (-(Real.pi / 2) * (k + 1)) :=
      mul_le_mul_of_nonneg_left hexpMono (by positivity)
    _ ≤ 48 * r ^ k := by
      rw [hpowSplit, hexpSplit]
      dsimp [r]
      rw [mul_pow]
      have hnonneg :
          0 ≤ (4 : ℝ) ^ k * (Real.exp (-(Real.pi / 2))) ^ k := by
        positivity
      nlinarith

/-- Low-block bound used in the first term of (3.14). -/
theorem equation314_lowGamma_le_three
    {t : ℝ} (_ht : |t| ≤ 2) :
    ‖Complex.Gamma (centralPoint t)‖ ≤ 3 := by
  calc
    ‖Complex.Gamma (centralPoint t)‖ ≤
        3 * Real.exp (-(Real.pi / 2) * |t|) :=
      norm_Gamma_centralPoint_le_exp_pi_half t
    _ ≤ 3 * 1 := by
      gcongr
      rw [Real.exp_le_one_iff]
      nlinarith [Real.pi_pos, abs_nonneg t]
    _ = 3 := by ring

/-- Every dyadic shell is bounded by the corresponding explicit term in
the summable (3.14) majorant. -/
theorem equation314_shellGamma_le_majorant
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : (2 : ℝ) ^ n ≤ |t|) :
    (2 : ℝ) ^ (2 * n + 2) * ‖Complex.Gamma (centralPoint t)‖ ≤
      equation314TailMajorant (n - 1) := by
  have hindex : n - 1 + 1 = n := by omega
  have hexp : Real.exp (-(Real.pi / 2) * |t|) ≤
      Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ n) := by
    apply Real.exp_le_exp.mpr
    have hpi0 : 0 < Real.pi / 2 := by positivity
    nlinarith
  calc
    (2 : ℝ) ^ (2 * n + 2) * ‖Complex.Gamma (centralPoint t)‖ ≤
        (2 : ℝ) ^ (2 * n + 2) *
          (3 * Real.exp (-(Real.pi / 2) * |t|)) := by
      gcongr
      exact norm_Gamma_centralPoint_le_exp_pi_half t
    _ ≤ (2 : ℝ) ^ (2 * n + 2) *
          (3 * Real.exp (-(Real.pi / 2) * (2 : ℝ) ^ n)) := by
      gcongr
    _ = equation314TailMajorant (n - 1) := by
      simp only [equation314TailMajorant, hindex]
      ring

/-- A concrete positive `c₂` satisfying the numerical budget in Huxley
(3.14), after replacing each maximum by the certified pointwise majorant. -/
def equation314Normalizer : ℝ :=
  Real.pi / (3 * (24 + ∑' k : ℕ, equation314TailMajorant k))

theorem equation314Normalizer_pos : 0 < equation314Normalizer := by
  unfold equation314Normalizer
  apply div_pos Real.pi_pos
  have hsum0 : 0 ≤ ∑' k : ℕ, equation314TailMajorant k :=
    tsum_nonneg (fun k => by unfold equation314TailMajorant; positivity)
  positivity

theorem equation314Normalizer_budget :
    equation314Normalizer *
        (8 * 3 + ∑' k : ℕ, equation314TailMajorant k) ≤
      2 * Real.pi / 3 := by
  have hsum0 : 0 ≤ ∑' k : ℕ, equation314TailMajorant k :=
    tsum_nonneg (fun k => by unfold equation314TailMajorant; positivity)
  have hden : 0 < 3 * (24 + ∑' k : ℕ, equation314TailMajorant k) := by
    positivity
  unfold equation314Normalizer
  have hK : 0 < 24 + ∑' k : ℕ, equation314TailMajorant k := by
    positivity
  norm_num
  have heq :
      Real.pi / (3 * (24 + ∑' k : ℕ, equation314TailMajorant k)) *
          (24 + ∑' k : ℕ, equation314TailMajorant k) =
        Real.pi / 3 := by
    field_simp [ne_of_gt hK]
  rw [heq]
  nlinarith [Real.pi_pos]

/-- Equation (3.14) has exactly the normalization needed after the
`1/(2*pi)` in Huxley's contour integral. -/
theorem equation314_normalized_budget_le_oneThird :
    equation314Normalizer *
          (8 * 3 + ∑' k : ℕ, equation314TailMajorant k) /
        (2 * Real.pi) ≤ 1 / 3 := by
  have hpi2 : 0 < 2 * Real.pi := by positivity
  rw [div_le_iff₀ hpi2]
  have hbudget := equation314Normalizer_budget
  nlinarith

/-- The remaining factor from moving the contour is `Y^(alpha-beta)`.
On Huxley's zero rectangle (`alpha ≤ beta`) and for `Y ≥ 1`, it can only
decrease the normalized (3.14) budget. -/
theorem equation314_scaled_budget_le_oneThird
    {Y alpha beta : ℝ} (hY : 1 ≤ Y) (hab : alpha ≤ beta) :
    (equation314Normalizer *
          (8 * 3 + ∑' k : ℕ, equation314TailMajorant k) /
        (2 * Real.pi)) * Real.rpow Y (alpha - beta) ≤ 1 / 3 := by
  have hscale0 : 0 ≤ Real.rpow Y (alpha - beta) :=
    Real.rpow_nonneg (zero_le_one.trans hY) _
  have hscale1 : Real.rpow Y (alpha - beta) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hY (by linarith)
  have hsum0 : 0 ≤ ∑' k : ℕ, equation314TailMajorant k :=
    tsum_nonneg (fun k => by unfold equation314TailMajorant; positivity)
  have hbudget0 : 0 ≤ equation314Normalizer *
          (8 * 3 + ∑' k : ℕ, equation314TailMajorant k) /
        (2 * Real.pi) := by
    exact div_nonneg
      (mul_nonneg equation314Normalizer_pos.le (by norm_num; positivity))
      (by positivity)
  calc
    (equation314Normalizer *
          (8 * 3 + ∑' k : ℕ, equation314TailMajorant k) /
        (2 * Real.pi)) * Real.rpow Y (alpha - beta) ≤
        (equation314Normalizer *
          (8 * 3 + ∑' k : ℕ, equation314TailMajorant k) /
        (2 * Real.pi)) * 1 :=
      mul_le_mul_of_nonneg_left hscale1 hbudget0
    _ ≤ 1 / 3 := by simpa using equation314_normalized_budget_le_oneThird

/-- A fully explicit sufficient form of Huxley's equation (3.14).  The first
conjunct controls the central block.  The second controls every point in the
`n`th dyadic shell by the summable term with index `n-1`.  The last conjunct
is the literal `2*pi/3` budget after those two pointwise replacements.

Writing the source's maxima as pointwise universal bounds avoids introducing
an unnecessary choice of maximizers. -/
theorem exists_equation314_gamma_shell_normalizer :
    ∃ c₂ : ℝ, 0 < c₂ ∧
      (∀ t : ℝ, |t| ≤ 2 →
        8 * c₂ * ‖Complex.Gamma (centralPoint t)‖ ≤ 24 * c₂) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, (2 : ℝ) ^ n ≤ |t| →
        c₂ * (2 : ℝ) ^ (2 * n + 2) *
            ‖Complex.Gamma (centralPoint t)‖ ≤
          c₂ * equation314TailMajorant (n - 1)) ∧
      c₂ * (24 + ∑' k : ℕ, equation314TailMajorant k) ≤
        2 * Real.pi / 3 := by
  refine ⟨equation314Normalizer, equation314Normalizer_pos, ?_, ?_, ?_⟩
  · intro t ht
    have hgamma := equation314_lowGamma_le_three ht
    have hc : 0 ≤ equation314Normalizer := equation314Normalizer_pos.le
    nlinarith
  · intro n hn t ht
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left
        (equation314_shellGamma_le_majorant hn ht)
        equation314Normalizer_pos.le)
  · simpa [show (8 : ℝ) * 3 = 24 by norm_num] using
      equation314Normalizer_budget

end
end MAPPrincipalZetaHuxley1972Equation314GammaNormalizer

#print axioms MAPPrincipalZetaHuxley1972Equation314GammaNormalizer.summable_equation314TailMajorant
#print axioms MAPPrincipalZetaHuxley1972Equation314GammaNormalizer.equation314Normalizer_budget
#print axioms MAPPrincipalZetaHuxley1972Equation314GammaNormalizer.equation314_scaled_budget_le_oneThird
#print axioms MAPPrincipalZetaHuxley1972Equation314GammaNormalizer.exists_equation314_gamma_shell_normalizer
