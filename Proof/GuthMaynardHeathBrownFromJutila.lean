import GuthMaynardHeathBrownIccIocEndpointAdapter

/-!
# Source descent from the Heath--Brown block to Jutila's weighted moment

This file supplies the missing direction in the existing endpoint adapters.
On `(M,2M]`, inserting the inverse-square-root weights costs at most `2M`.
Consequently Jutila's three-term bound implies the literal coefficient-one
Heath--Brown inequality, including the closed-left endpoint.
-/

namespace GuthMaynardHeathBrownFromJutila

open scoped BigOperators
open GuthMaynardHeathBrownInterface
open GuthMaynardHeathBrownMajorant
open GuthMaynardHeathBrownIccIocEndpointAdapter
open GuthMaynardLengthComparison

noncomputable section

/-- The three-term weighted moment shape in Jutila's coefficient-one theorem,
kept local so this finite bridge does not import the later recurrence DAG. -/
def jutilaThreeTermShape (T M : ℝ) (W : Finset ℝ) : ℝ :=
  (W.card : ℝ) * M +
    Real.rpow (W.card : ℝ) (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ) +
    (W.card : ℝ) ^ 2

theorem one_le_two_mul_M_mul_inverseSqrtWeights
    {M m n : ℕ} (hm : m ∈ Finset.Ioc M (2 * M))
    (hn : n ∈ Finset.Ioc M (2 * M)) :
    (1 : ℝ) ≤ 2 * (M : ℝ) * inverseSqrtWeight m * inverseSqrtWeight n := by
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le M) (Finset.mem_Ioc.mp hm).1)
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le M) (Finset.mem_Ioc.mp hn).1)
  have hMnonneg : (0 : ℝ) ≤ 2 * (M : ℝ) := by positivity
  have hmupper : (m : ℝ) ≤ 2 * (M : ℝ) := by
    exact_mod_cast (Finset.mem_Ioc.mp hm).2
  have hnupper : (n : ℝ) ≤ 2 * (M : ℝ) := by
    exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hsm : Real.sqrt (m : ℝ) ≤ Real.sqrt (2 * (M : ℝ)) :=
    Real.sqrt_le_sqrt hmupper
  have hsn : Real.sqrt (n : ℝ) ≤ Real.sqrt (2 * (M : ℝ)) :=
    Real.sqrt_le_sqrt hnupper
  have hprod : Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ) ≤ 2 * (M : ℝ) := by
    calc
      Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ) ≤
          Real.sqrt (2 * (M : ℝ)) * Real.sqrt (2 * (M : ℝ)) := by
        exact mul_le_mul hsm hsn (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = 2 * (M : ℝ) := by
        simpa [pow_two] using Real.sq_sqrt hMnonneg
  have hden : 0 < Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ) :=
    mul_pos (Real.sqrt_pos.2 hmpos) (Real.sqrt_pos.2 hnpos)
  unfold inverseSqrtWeight
  rw [show 2 * (M : ℝ) * (Real.sqrt (m : ℝ))⁻¹ *
      (Real.sqrt (n : ℝ))⁻¹ =
      (2 * (M : ℝ)) / (Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ)) by
        field_simp]
  exact (le_div_iff₀ hden).2 (by simpa using hprod)

/-- The open-left unweighted ratio block costs at most `2M` times Jutila's
literal inverse-square-root moment. -/
theorem openLeftRatioSecondMoment_le_two_mul_jutila
    (M : ℕ) (W : Finset ℝ) :
    openLeftRatioSecondMoment M W ≤
      2 * (M : ℝ) * jutilaSecondMoment (M : ℝ) W := by
  rw [jutilaSecondMoment_eq_coefficientOneRatioQuadratic]
  unfold openLeftRatioSecondMoment ratioKernelSquare
    coefficientOneRatioQuadratic coefficientOneRatioSummand
  rw [realDyadicIoc_natCast]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hw := one_le_two_mul_M_mul_inverseSqrtWeights hm hn
  calc
    ‖GuthMaynardRatioKernelIdentity.ratioDirichletKernel W
        ((m : ℝ) / (n : ℝ))‖ ^ 2 =
        1 * ‖GuthMaynardRatioKernelIdentity.ratioDirichletKernel W
          ((m : ℝ) / (n : ℝ))‖ ^ 2 := by ring
    _ ≤ (2 * (M : ℝ) * inverseSqrtWeight m * inverseSqrtWeight n) *
        ‖GuthMaynardRatioKernelIdentity.ratioDirichletKernel W
          ((m : ℝ) / (n : ℝ))‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = 2 * (M : ℝ) *
        (inverseSqrtWeight m * inverseSqrtWeight n *
          ‖GuthMaynardRatioKernelIdentity.ratioDirichletKernel W
            ((m : ℝ) / (n : ℝ))‖ ^ 2) := by ring

/-- Exact finite descent for the literal target quadratic form.  This is the
closed-endpoint strengthening needed before any analytic Jutila estimate is
inserted. -/
theorem differenceQuadraticForm_one_le_two_mul_jutila_add_endpoint
    (M : ℕ) (W : Finset ℝ) (hM : 1 ≤ M) :
    differenceQuadraticForm (fun _ => (1 : ℂ)) M W ≤
      2 * (M : ℝ) * jutilaSecondMoment (M : ℝ) W +
        (2 * (M : ℝ) + 1) * (W.card : ℝ) ^ 2 := by
  exact (differenceQuadraticForm_one_le_openLeft_add_endpointBound M W hM).trans
    (add_le_add (openLeftRatioSecondMoment_le_two_mul_jutila M W) le_rfl)

/-- Pointwise source descent.  A Jutila three-term estimate gives the exact
Heath--Brown coefficient-one shape; only an absolute constant changes. -/
theorem differenceQuadraticForm_one_le_of_jutila
    {C eta T : ℝ} {M : ℕ} {W : Finset ℝ}
    (heta : 0 ≤ eta) (hT : 1 ≤ T) (hM : 1 ≤ M)
    (hJ : jutilaSecondMoment (M : ℝ) W ≤
      C * Real.rpow T eta * jutilaThreeTermShape T M W) :
    differenceQuadraticForm (fun _ => (1 : ℂ)) M W ≤
      (2 * C + 3) * Real.rpow T eta * heathBrownShape T M W := by
  have hpow : 1 ≤ Real.rpow T eta := Real.one_le_rpow hT heta
  have hM0 : 0 ≤ (M : ℝ) := by positivity
  have hW0 : 0 ≤ (W.card : ℝ) := by positivity
  have hshape0 := heathBrownShape_nonneg (le_trans zero_le_one hT) M W
  have hshapeEq :
      (M : ℝ) * jutilaThreeTermShape T M W = heathBrownShape T M W := by
    unfold jutilaThreeTermShape heathBrownShape
    ring
  have hendpointShape :
      (M : ℝ) * (W.card : ℝ) ^ 2 ≤ heathBrownShape T M W := by
    unfold heathBrownShape
    have hTpow : 0 ≤ Real.rpow T (1 / 2 : ℝ) :=
      Real.rpow_nonneg (le_trans zero_le_one hT) _
    have hWpow : 0 ≤ Real.rpow (W.card : ℝ) (5 / 4 : ℝ) :=
      Real.rpow_nonneg hW0 _
    nlinarith [mul_nonneg hW0 hM0,
      mul_nonneg hWpow (mul_nonneg hTpow hM0)]
  have hend :=
    differenceQuadraticForm_one_le_two_mul_jutila_add_endpoint M W hM
  have hendpointCoeff : (2 * (M : ℝ) + 1) ≤ 3 * (M : ℝ) := by
    exact_mod_cast (show 2 * M + 1 ≤ 3 * M by omega)
  calc
    differenceQuadraticForm (fun _ => (1 : ℂ)) M W ≤
        2 * (M : ℝ) * jutilaSecondMoment (M : ℝ) W +
          (2 * (M : ℝ) + 1) * (W.card : ℝ) ^ 2 := hend
    _ ≤ 2 * (M : ℝ) * jutilaSecondMoment (M : ℝ) W +
          3 * (M : ℝ) * (W.card : ℝ) ^ 2 := by gcongr
    _ ≤ 2 * (M : ℝ) *
          (C * Real.rpow T eta * jutilaThreeTermShape T M W) +
          3 * (M : ℝ) * (W.card : ℝ) ^ 2 := by gcongr
    _ = 2 * C * Real.rpow T eta * heathBrownShape T M W +
          3 * (M : ℝ) * (W.card : ℝ) ^ 2 := by
      rw [← hshapeEq]
      ring
    _ ≤ 2 * C * Real.rpow T eta * heathBrownShape T M W +
          3 * Real.rpow T eta * heathBrownShape T M W := by
      apply add_le_add_right
      calc
        3 * (M : ℝ) * (W.card : ℝ) ^ 2 ≤
            3 * heathBrownShape T M W := by nlinarith
        _ ≤ 3 * Real.rpow T eta * heathBrownShape T M W := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hpow) hshape0]
    _ = (2 * C + 3) * Real.rpow T eta * heathBrownShape T M W := by ring

end
end GuthMaynardHeathBrownFromJutila

#print axioms GuthMaynardHeathBrownFromJutila.openLeftRatioSecondMoment_le_two_mul_jutila
#print axioms GuthMaynardHeathBrownFromJutila.differenceQuadraticForm_one_le_two_mul_jutila_add_endpoint
#print axioms GuthMaynardHeathBrownFromJutila.differenceQuadraticForm_one_le_of_jutila
