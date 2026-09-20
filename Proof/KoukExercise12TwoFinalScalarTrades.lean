import KoukExercise12TwoPowerGeometry
import KoukExercise12TwoPointwiseLocalFormula
import SupportBoundaryQuantitative

/-! Reusable algebraic trades for the final pointwise SW collapse. -/

namespace MAPKoukExercise12TwoFinalScalarTrades

open PrimitiveTruncatedExplicitFormulaBridge PaperEdgePrimitiveComponents

noncomputable section

theorem rpow_neg_nat_eq_one_div_pow
    {L : ℝ} (hL : 0 < L) (A : ℕ) :
    Real.rpow L (-(A : ℝ)) = 1 / L ^ A := by
  calc
    Real.rpow L (-(A : ℝ)) = (Real.rpow L (A : ℝ))⁻¹ :=
      Real.rpow_neg hL.le (A : ℝ)
    _ = (L ^ A)⁻¹ := congrArg Inv.inv (Real.rpow_natCast L A)
    _ = 1 / L ^ A := by ring

/-- An `X^(3/4)` term times a fixed polylog is below the exact SW target once
the combined log power is absorbed by `X^(1/4)`. -/
theorem threeQuarter_mul_polylog_le_div
    {X L : ℝ} {P A : ℕ} (hX : 0 < X) (hL : 0 < L)
    (hpoly : L ^ (P + A) ≤ Real.rpow X (1 / 4 : ℝ)) :
    Real.rpow X (3 / 4 : ℝ) * L ^ P ≤ X / L ^ A := by
  rw [le_div_iff₀ (pow_pos hL A)]
  calc
    Real.rpow X (3 / 4 : ℝ) * L ^ P * L ^ A =
        Real.rpow X (3 / 4 : ℝ) * L ^ (P + A) := by rw [pow_add]; ring
    _ ≤ Real.rpow X (3 / 4 : ℝ) * Real.rpow X (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg hX.le _)
    _ = Real.rpow X ((3 / 4 : ℝ) + (1 / 4 : ℝ)) :=
      (Real.rpow_add hX (3 / 4 : ℝ) (1 / 4 : ℝ)).symm
    _ = X := by norm_num

/-- A selected height `T > log(X)^D` converts a numerator log power into the
exact inverse-log target. -/
theorem polylog_div_selectedHeight_le
    {L T : ℝ} {P A D : ℕ} (hL : 1 ≤ L) (hT : L ^ D < T)
    (hdegree : P + A ≤ D) :
    L ^ P / T ≤ 1 / L ^ A := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hpowD : 0 < L ^ D := pow_pos hLpos D
  have hTpos : 0 < T := hpowD.trans hT
  have hfirst : L ^ P / T ≤ L ^ P / L ^ D :=
    div_le_div_of_nonneg_left (pow_nonneg hLpos.le P) hpowD hT.le
  refine hfirst.trans ?_
  rw [div_le_div_iff₀ hpowD (pow_pos hLpos A)]
  calc
    L ^ P * L ^ A = L ^ (P + A) := by rw [pow_add]
    _ ≤ L ^ D := pow_le_pow_right₀ hL hdegree
    _ = 1 * L ^ D := by ring

theorem halfIntegerPoint_rpow_standardEdge_le_nine_mul
    {X t : ℝ} (hX : 2 ≤ X) (ht : t ∈ Set.Icc X (2 * X)) :
    Real.rpow (halfIntegerPoint ⌊t⌋₊) (standardEdge ⌊t⌋₊) ≤ 9 * X := by
  obtain ⟨hN, -, hxUpper, -⟩ :=
    MAPKoukExercise12TwoEndpointScalars.halfIntegerPoint_floor_range hX ht
  have hxone : 1 < halfIntegerPoint ⌊t⌋₊ := by
    have hNR : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hN
    unfold halfIntegerPoint
    linarith
  have hbase := PaperEdgePerronRemainder.rpow_standardEdge_le
    hxone (halfIntegerPoint_pos _) le_rfl
  exact hbase.trans (by
    have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
    calc
      Real.exp 1 * halfIntegerPoint ⌊t⌋₊ ≤ 3 * (3 * X) :=
        mul_le_mul he hxUpper (halfIntegerPoint_pos _).le (by norm_num)
      _ = 9 * X := by ring)

theorem standardEdge_sub_sigma_div_pi_le_two
    {N : ℕ} {sigma : ℝ} (hN : 1 ≤ N) (hsigma : 0 < sigma) :
    (standardEdge N - sigma) / Real.pi ≤ 2 := by
  have hedge :=
    MAPKoukExercise12TwoPointwiseLocalFormula.standardEdge_lt_four N hN
  have hnum : standardEdge N - sigma ≤ 4 := by linarith
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hnonneg : (0 : ℝ) ≤ 4 := by norm_num
  calc
    (standardEdge N - sigma) / Real.pi ≤ 4 / Real.pi :=
      div_le_div_of_nonneg_right hnum Real.pi_pos.le
    _ ≤ 4 / 3 := div_le_div_of_nonneg_left hnonneg (by norm_num) hpi.le
    _ ≤ 2 := by norm_num

end
end MAPKoukExercise12TwoFinalScalarTrades

#print axioms MAPKoukExercise12TwoFinalScalarTrades.threeQuarter_mul_polylog_le_div
#print axioms MAPKoukExercise12TwoFinalScalarTrades.polylog_div_selectedHeight_le
#print axioms MAPKoukExercise12TwoFinalScalarTrades.halfIntegerPoint_rpow_standardEdge_le_nine_mul
