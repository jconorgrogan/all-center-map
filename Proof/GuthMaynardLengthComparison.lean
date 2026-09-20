import GuthMaynardHeathBrownMajorant
import GuthMaynardRatioKernelIdentity

/-!
# The exact Heath--Brown--Jutila length comparison

Lemma 29.8 in the cached third volume defines

`S(X) = sum_{t,u in W} |sum_{X < n <= 2X} n^(-1/2+i(t-u))|^2`

for a real length `X`, and proves `S(X / k) <= k S(X)` for a positive
natural number `k`.  The proof expands the square, sends `(m,n)` to
`(km,kn)`, and enlarges the resulting image using termwise nonnegativity.

This file certifies that exact deterministic step.  In particular:

* `realDyadicIoc X` represents the literal open-left, closed-right condition
  `X < n <= 2X`, even when `X` is not integral;
* `coefficientOneRatioQuadratic` is the expanded coefficient-one ratio-kernel
  form, with the exact inverse-square-root weights;
* `jutilaSecondMoment` is the unexpanded quadratic form, with phase
  `n^(-1/2+i(t-u))`;
* the factor `k` is an equality coming from the inverse-square-root weights;
  the only inequality is enlargement of the scaled image, whose summands are
  nonnegative.

The source writes only `k in N`; positivity is required for division by `k`
and for the injectivity of `n |-> kn`, so it is exposed as `0 < k` below.
-/

namespace GuthMaynardLengthComparison

open scoped BigOperators
open GuthMaynardHeathBrownInterface
open GuthMaynardHeathBrownMajorant
open GuthMaynardRatioKernelIdentity

noncomputable section

/-! ## Literal real-length index sets -/

/-- The natural numbers in the literal real interval `(X, 2X]`.

The ambient `range` is only a finiteness witness.  The membership theorem
below removes it completely, so no floor or ceiling convention enters the
statement of the comparison theorem. -/
def realDyadicIoc (X : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil (2 * X) + 1)).filter
    (fun n => X < (n : ℝ) ∧ (n : ℝ) ≤ 2 * X)

@[simp]
theorem mem_realDyadicIoc_iff {X : ℝ} {n : ℕ} :
    n ∈ realDyadicIoc X ↔ X < (n : ℝ) ∧ (n : ℝ) ≤ 2 * X := by
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · intro hn
    apply Finset.mem_filter.mpr
    refine ⟨?_, hn⟩
    have hnceilR : (n : ℝ) ≤ (Nat.ceil (2 * X) : ℝ) :=
      hn.2.trans (Nat.le_ceil (2 * X))
    have hnceil : n ≤ Nat.ceil (2 * X) := by
      exact_mod_cast hnceilR
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hnceil)

/-- The endpoint convention specializes exactly to `Finset.Ioc`, not to the
closed interval `Finset.Icc` used by some neighboring source interfaces. -/
theorem realDyadicIoc_natCast (M : ℕ) :
    realDyadicIoc (M : ℝ) = Finset.Ioc M (2 * M) := by
  ext n
  simp only [mem_realDyadicIoc_iff, Finset.mem_Ioc]
  norm_cast

/-- Every integer in a nonempty interval `(X,2X]` is positive.  This is the
precise positivity needed to interpret the ratio phase without a zero
convention. -/
theorem pos_of_mem_realDyadicIoc {X : ℝ} {n : ℕ}
    (hn : n ∈ realDyadicIoc X) : 0 < n := by
  rw [mem_realDyadicIoc_iff] at hn
  by_contra hnot
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnot
  subst n
  norm_num at hn
  linarith

/-! ## The expanded coefficient-one form -/

/-- The source coefficient `n^(-1/2)`, kept in a form whose exact scaling law
under `n |-> kn` is transparent. -/
def inverseSqrtWeight (n : ℕ) : ℝ := (Real.sqrt (n : ℝ))⁻¹

theorem inverseSqrtWeight_nonneg (n : ℕ) : 0 ≤ inverseSqrtWeight n := by
  unfold inverseSqrtWeight
  positivity

/-- A single summand after expanding the ordered-pair second moment.  The
coefficient inside `ratioDirichletKernel` is literally one for every `t in W`;
the two displayed weights are the source factor `(mn)^(-1/2)`. -/
def coefficientOneRatioSummand (W : Finset ℝ) (m n : ℕ) : ℝ :=
  inverseSqrtWeight m * inverseSqrtWeight n *
    ‖ratioDirichletKernel W ((m : ℝ) / (n : ℝ))‖ ^ 2

theorem coefficientOneRatioSummand_nonneg (W : Finset ℝ) (m n : ℕ) :
    0 ≤ coefficientOneRatioSummand W m n := by
  unfold coefficientOneRatioSummand
  exact mul_nonneg
    (mul_nonneg (inverseSqrtWeight_nonneg m)
      (inverseSqrtWeight_nonneg n))
    (sq_nonneg _)

/-- The literal expanded form on `(X,2X] x (X,2X]` from the proof of
Lemma 29.8. -/
def coefficientOneRatioQuadratic (X : ℝ) (W : Finset ℝ) : ℝ :=
  ∑ m ∈ realDyadicIoc X, ∑ n ∈ realDyadicIoc X,
    coefficientOneRatioSummand W m n

/-! ## Exact scaling identities -/

/-- Multiplication by a positive natural number, as an embedding. -/
def scaleEmbedding (k : ℕ) (hk : 0 < k) : ℕ ↪ ℕ where
  toFun n := k * n
  inj' := fun _ _ h => Nat.mul_left_cancel hk h

@[simp]
theorem scaleEmbedding_apply (k : ℕ) (hk : 0 < k) (n : ℕ) :
    scaleEmbedding k hk n = k * n := rfl

theorem inverseSqrtWeight_mul (k n : ℕ) :
    inverseSqrtWeight (k * n) =
      inverseSqrtWeight k * inverseSqrtWeight n := by
  simp only [inverseSqrtWeight, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg k), mul_inv_rev]
  exact mul_comm _ _

theorem natCast_mul_inverseSqrtWeight_sq (k : ℕ) (hk : 0 < k) :
    (k : ℝ) * inverseSqrtWeight k ^ 2 = 1 := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsqrt : Real.sqrt (k : ℝ) ≠ 0 := (Real.sqrt_pos.2 hkR).ne'
  unfold inverseSqrtWeight
  rw [inv_pow]
  field_simp
  exact (Real.sq_sqrt hkR.le).symm

/-- Scaling both positive integer arguments leaves the ratio phase unchanged.
This fixes the orientation as `(m/n)^(it)`, matching the displayed proof. -/
theorem ratioDirichletKernel_scale (W : Finset ℝ) (k m n : ℕ)
    (hk : 0 < k) :
    ratioDirichletKernel W
        (((k * m : ℕ) : ℝ) / ((k * n : ℕ) : ℝ)) =
      ratioDirichletKernel W ((m : ℝ) / (n : ℝ)) := by
  congr 1
  push_cast
  exact mul_div_mul_left (m : ℝ) (n : ℝ) (by exact_mod_cast hk.ne')

/-- The factor `k` in Lemma 29.8 is an exact termwise identity. -/
theorem coefficientOneRatioSummand_scale (W : Finset ℝ) (k m n : ℕ)
    (hk : 0 < k) :
    coefficientOneRatioSummand W m n =
      (k : ℝ) * coefficientOneRatioSummand W (k * m) (k * n) := by
  rw [coefficientOneRatioSummand, coefficientOneRatioSummand,
    inverseSqrtWeight_mul, inverseSqrtWeight_mul,
    ratioDirichletKernel_scale W k m n hk]
  have hkweight := natCast_mul_inverseSqrtWeight_sq k hk
  symm
  calc
    (k : ℝ) *
        (inverseSqrtWeight k * inverseSqrtWeight m *
          (inverseSqrtWeight k * inverseSqrtWeight n) *
            ‖ratioDirichletKernel W ((m : ℝ) / (n : ℝ))‖ ^ 2) =
        ((k : ℝ) * inverseSqrtWeight k ^ 2) *
          (inverseSqrtWeight m * inverseSqrtWeight n *
            ‖ratioDirichletKernel W ((m : ℝ) / (n : ℝ))‖ ^ 2) := by ring
    _ = inverseSqrtWeight m * inverseSqrtWeight n *
          ‖ratioDirichletKernel W ((m : ℝ) / (n : ℝ))‖ ^ 2 := by
      rw [hkweight]
      ring

/-- The scaled small interval is a subset of the large interval, with the
source's open-left and closed-right endpoints preserved exactly. -/
theorem map_scaleEmbedding_subset (X : ℝ) (k : ℕ) (hk : 0 < k) :
    (realDyadicIoc (X / (k : ℝ))).map (scaleEmbedding k hk) ⊆
      realDyadicIoc X := by
  intro r hr
  rw [Finset.mem_map] at hr
  obtain ⟨n, hn, rfl⟩ := hr
  rw [mem_realDyadicIoc_iff] at hn ⊢
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  constructor
  · have h := (div_lt_iff₀ hkR).mp hn.1
    simpa [Nat.cast_mul, mul_comm] using h
  · have hrewrite : 2 * (X / (k : ℝ)) = (2 * X) / (k : ℝ) := by ring
    rw [hrewrite] at hn
    have h := (le_div_iff₀ hkR).mp hn.2
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using h

/-- Exact reindexing before positivity is used: the short form is `k` times
the same form restricted to the scaled image. -/
theorem coefficientOneRatioQuadratic_eq_scaleImage
    (X : ℝ) (k : ℕ) (W : Finset ℝ) (hk : 0 < k) :
    coefficientOneRatioQuadratic (X / (k : ℝ)) W =
      (k : ℝ) *
        ∑ m ∈ (realDyadicIoc (X / (k : ℝ))).map (scaleEmbedding k hk),
          ∑ n ∈ (realDyadicIoc (X / (k : ℝ))).map (scaleEmbedding k hk),
            coefficientOneRatioSummand W m n := by
  unfold coefficientOneRatioQuadratic
  let S := realDyadicIoc (X / (k : ℝ))
  let e := scaleEmbedding k hk
  change (∑ m ∈ S, ∑ n ∈ S, coefficientOneRatioSummand W m n) = _
  calc
    (∑ m ∈ S, ∑ n ∈ S, coefficientOneRatioSummand W m n) =
        ∑ m ∈ S, ∑ n ∈ S,
          (k : ℝ) * coefficientOneRatioSummand W (e m) (e n) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact coefficientOneRatioSummand_scale W k m n hk
    _ = (k : ℝ) *
        ∑ m ∈ S, ∑ n ∈ S,
          coefficientOneRatioSummand W (e m) (e n) := by
      simp_rw [Finset.mul_sum]
    _ = (k : ℝ) *
        ∑ m ∈ S.map e, ∑ n ∈ S.map e,
          coefficientOneRatioSummand W m n := by
      simp only [Finset.sum_map]

/-- Positivity/majorization is the only inequality in the source proof. -/
theorem coefficientOneRatioQuadratic_scaleImage_le
    (X : ℝ) (k : ℕ) (W : Finset ℝ) (hk : 0 < k) :
    (∑ m ∈ (realDyadicIoc (X / (k : ℝ))).map (scaleEmbedding k hk),
        ∑ n ∈ (realDyadicIoc (X / (k : ℝ))).map (scaleEmbedding k hk),
          coefficientOneRatioSummand W m n) ≤
      coefficientOneRatioQuadratic X W := by
  let A := (realDyadicIoc (X / (k : ℝ))).map (scaleEmbedding k hk)
  let B := realDyadicIoc X
  have hAB : A ⊆ B := map_scaleEmbedding_subset X k hk
  unfold coefficientOneRatioQuadratic
  change (∑ m ∈ A, ∑ n ∈ A, coefficientOneRatioSummand W m n) ≤
    ∑ m ∈ B, ∑ n ∈ B, coefficientOneRatioSummand W m n
  calc
    (∑ m ∈ A, ∑ n ∈ A, coefficientOneRatioSummand W m n) ≤
        ∑ m ∈ A, ∑ n ∈ B, coefficientOneRatioSummand W m n := by
      apply Finset.sum_le_sum
      intro m hm
      exact Finset.sum_le_sum_of_subset_of_nonneg hAB
        (fun n hnB hnA => coefficientOneRatioSummand_nonneg W m n)
    _ ≤ ∑ m ∈ B, ∑ n ∈ B, coefficientOneRatioSummand W m n := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hAB
        (fun m hmB hmA => Finset.sum_nonneg
          (fun n hnB => coefficientOneRatioSummand_nonneg W m n))

/-- Lemma 29.8 in exact real-length, open-left/closed-right form. -/
theorem coefficientOneRatioQuadratic_div_le
    (X : ℝ) (k : ℕ) (W : Finset ℝ) (hk : 0 < k) :
    coefficientOneRatioQuadratic (X / (k : ℝ)) W ≤
      (k : ℝ) * coefficientOneRatioQuadratic X W := by
  rw [coefficientOneRatioQuadratic_eq_scaleImage X k W hk]
  exact mul_le_mul_of_nonneg_left
    (coefficientOneRatioQuadratic_scaleImage_le X k W hk)
    (Nat.cast_nonneg k)

/-! ## Identification with Jutila's unexpanded `S(X)` -/

/-- The literal second moment before the square is expanded.  Through
`dirichletPhase`, its inner phase is
`exp (i * (t-u) * log n)`, so the full term is
`n^(-1/2+i(t-u))` with ordered pairs `(t,u) in W^2`. -/
def jutilaSecondMoment (X : ℝ) (W : Finset ℝ) : ℝ :=
  realGramQuadratic (realDyadicIoc X) W
    (fun n => ((inverseSqrtWeight n : ℝ) : ℂ)) dirichletPhase

/-- Expansion of the square gives exactly the coefficient-one ratio form.
This reuses both the finite Gram majorant identity and the exact ratio-kernel
identity, including positivity of every ratio in the real-length interval. -/
theorem jutilaSecondMoment_eq_coefficientOneRatioQuadratic
    (X : ℝ) (W : Finset ℝ) :
    jutilaSecondMoment X W = coefficientOneRatioQuadratic X W := by
  have hnonneg : ∀ n ∈ realDyadicIoc X, 0 ≤ inverseSqrtWeight n :=
    fun n hn => inverseSqrtWeight_nonneg n
  have hmajorant := absoluteCoefficientMajorant_real_nonnegative_eq
    (realDyadicIoc X) W inverseSqrtWeight dirichletPhase hnonneg
  unfold jutilaSecondMoment
  rw [← hmajorant]
  unfold absoluteCoefficientMajorant coefficientOneRatioQuadratic
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inverseSqrtWeight_nonneg m),
    abs_of_nonneg (inverseSqrtWeight_nonneg n)]
  rw [gramKernel_dirichletPhase_eq_ratioDirichletKernel W
    (pos_of_mem_realDyadicIoc hm) (pos_of_mem_realDyadicIoc hn)]
  rfl

/-- Source-facing `S(X/k) <= k S(X)`, now for Jutila's unexpanded second
moment itself. -/
theorem jutilaSecondMoment_div_le
    (X : ℝ) (k : ℕ) (W : Finset ℝ) (hk : 0 < k) :
    jutilaSecondMoment (X / (k : ℝ)) W ≤
      (k : ℝ) * jutilaSecondMoment X W := by
  rw [jutilaSecondMoment_eq_coefficientOneRatioQuadratic,
    jutilaSecondMoment_eq_coefficientOneRatioQuadratic]
  exact coefficientOneRatioQuadratic_div_le X k W hk

end

end GuthMaynardLengthComparison

#print axioms GuthMaynardLengthComparison.mem_realDyadicIoc_iff
#print axioms GuthMaynardLengthComparison.realDyadicIoc_natCast
#print axioms GuthMaynardLengthComparison.coefficientOneRatioQuadratic_div_le
#print axioms GuthMaynardLengthComparison.jutilaSecondMoment_eq_coefficientOneRatioQuadratic
#print axioms GuthMaynardLengthComparison.jutilaSecondMoment_div_le
