import FixedScaleAPZeroRoute
import AppendixA5ClosedLocalZeroCount

/-!
# Pair expansion for equation (2.8)

This staging file formalizes the exact finite pair expansion of the literal
zero field.  It is the first deterministic step from the weighted zero mass
(2.7) to the zero-field `L²` energy (2.8).
-/

namespace MAPAPZeroFieldEnergy28Core

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate
open APExplicitFormulaMajorantAdapter

noncomputable section

/-- One multiplicity-weighted pair kernel in the square of the finite zero
field. -/
def zeroPairKernel (multiplicity : ℂ → ℕ)
    (ρ ρ' : ℂ) (t : ℝ) : ℂ :=
  (multiplicity ρ : ℂ) * (multiplicity ρ' : ℂ) *
    (t : ℂ) ^ (ρ + conj ρ' - 2)

private theorem conj_ofReal_cpow_sub_one
    {t : ℝ} (ht : 0 < t) (ρ : ℂ) :
    conj ((t : ℂ) ^ (ρ - 1)) =
      (t : ℂ) ^ (conj ρ - 1) := by
  have harg : ((t : ℂ).arg) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht.le]
    exact ne_of_lt Real.pi_pos
  have hc := Complex.cpow_conj (t : ℂ) (ρ - 1) harg
  rw [map_sub, map_one, conj_ofReal] at hc
  exact hc.symm

/-- Exact pointwise pair expansion.  Multiplicities are retained on both
indices and no absolute values or diagonal truncation have been taken. -/
theorem finiteZeroField_mul_conj_eq_pairSum
    (zeros : Finset ℂ) (multiplicity : ℂ → ℕ)
    {t : ℝ} (ht : 0 < t) :
    finiteZeroField zeros multiplicity t *
        conj (finiteZeroField zeros multiplicity t) =
      ∑ ρ ∈ zeros, ∑ ρ' ∈ zeros,
        zeroPairKernel multiplicity ρ ρ' t := by
  classical
  unfold finiteZeroField
  rw [map_sum]
  simp only [map_sum, map_mul, map_natCast]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ' hρ'
  rw [conj_ofReal_cpow_sub_one ht]
  unfold zeroPairKernel
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  calc
    (multiplicity ρ : ℂ) * (t : ℂ) ^ (ρ - 1) *
        ((multiplicity ρ' : ℂ) * (t : ℂ) ^ (conj ρ' - 1)) =
      (multiplicity ρ : ℂ) * (multiplicity ρ' : ℂ) *
        ((t : ℂ) ^ (ρ - 1) * (t : ℂ) ^ (conj ρ' - 1)) := by ring
    _ = (multiplicity ρ : ℂ) * (multiplicity ρ' : ℂ) *
        (t : ℂ) ^ ((ρ - 1) + (conj ρ' - 1)) := by
          rw [Complex.cpow_add _ _ ht0]
    _ = _ := by
      congr 1
      ring

/-- The same identity in the literal squared-norm form integrated in (2.8). -/
theorem ofReal_norm_finiteZeroField_sq_eq_pairSum
    (zeros : Finset ℂ) (multiplicity : ℂ → ℕ)
    {t : ℝ} (ht : 0 < t) :
    ((‖finiteZeroField zeros multiplicity t‖ ^ 2 : ℝ) : ℂ) =
      ∑ ρ ∈ zeros, ∑ ρ' ∈ zeros,
        zeroPairKernel multiplicity ρ ρ' t := by
  rw [Complex.sq_norm, ← Complex.mul_conj]
  exact finiteZeroField_mul_conj_eq_pairSum zeros multiplicity ht

/-- Every pair kernel is interval integrable on the positive manuscript
interval. -/
theorem intervalIntegrable_zeroPairKernel
    (multiplicity : ℂ → ℕ) (ρ ρ' : ℂ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (zeroPairKernel multiplicity ρ ρ') volume a b := by
  unfold zeroPairKernel
  apply (show IntervalIntegrable
      (fun t : ℝ => (t : ℂ) ^ (ρ + conj ρ' - 2)) volume a b by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    apply (Complex.continuousAt_ofReal_cpow_const t
      (ρ + conj ρ' - 2) ?_).continuousWithinAt
    apply Or.inr
    have htmem := Set.mem_uIcc.mp ht
    rcases htmem with h | h
    · exact ne_of_gt (ha.trans_le h.1)
    · exact ne_of_gt (hb.trans_le h.1)).const_mul

theorem intervalIntegrable_zeroPairKernel_sum
    (zeros : Finset ℂ) (multiplicity : ℂ → ℕ) (ρ : ℂ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable
      (fun t : ℝ => ∑ ρ' ∈ zeros,
        zeroPairKernel multiplicity ρ ρ' t) volume a b := by
  classical
  induction zeros using Finset.induction_on with
  | empty => simp
  | @insert ρ' s hρ' ih =>
      simp only [Finset.sum_insert hρ']
      exact (intervalIntegrable_zeroPairKernel multiplicity ρ ρ' ha hb).add ih

/-- Exact integral pair expansion on a positive interval. -/
theorem integral_norm_finiteZeroField_sq_eq_pairIntegrals
    (zeros : Finset ℂ) (multiplicity : ℂ → ℕ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (((∫ t : ℝ in a..b,
        ‖finiteZeroField zeros multiplicity t‖ ^ 2) : ℝ) : ℂ) =
      ∑ ρ ∈ zeros, ∑ ρ' ∈ zeros,
        ∫ t : ℝ in a..b, zeroPairKernel multiplicity ρ ρ' t := by
  rw [← intervalIntegral.integral_ofReal]
  calc
    (∫ t : ℝ in a..b,
        ((‖finiteZeroField zeros multiplicity t‖ ^ 2 : ℝ) : ℂ)) =
        ∫ t : ℝ in a..b,
          ∑ ρ ∈ zeros, ∑ ρ' ∈ zeros,
            zeroPairKernel multiplicity ρ ρ' t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htpos : 0 < t := by
        rcases Set.mem_uIcc.mp ht with h | h
        · exact ha.trans_le h.1
        · exact hb.trans_le h.1
      exact ofReal_norm_finiteZeroField_sq_eq_pairSum
        zeros multiplicity htpos
    _ = ∑ ρ ∈ zeros,
        ∫ t : ℝ in a..b, ∑ ρ' ∈ zeros,
          zeroPairKernel multiplicity ρ ρ' t := by
      rw [intervalIntegral.integral_finsetSum]
      intro ρ hρ
      exact intervalIntegrable_zeroPairKernel_sum
        zeros multiplicity ρ ha hb
    _ = ∑ ρ ∈ zeros, ∑ ρ' ∈ zeros,
        ∫ t : ℝ in a..b, zeroPairKernel multiplicity ρ ρ' t := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [intervalIntegral.integral_finsetSum]
      intro ρ' hρ'
      exact intervalIntegrable_zeroPairKernel multiplicity ρ ρ' ha hb

/-- Exact nonresonant evaluation of one pair integral.  This is the source of
the ordinate-separation denominator in the manuscript proof of (2.8). -/
theorem integral_zeroPairKernel_eq_div
    (multiplicity : ℂ → ℕ) (ρ ρ' : ℂ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (him : ρ.im ≠ ρ'.im) :
    (∫ t : ℝ in a..b, zeroPairKernel multiplicity ρ ρ' t) =
      (multiplicity ρ : ℂ) * (multiplicity ρ' : ℂ) *
        (((b : ℂ) ^ (ρ + conj ρ' - 1) -
            (a : ℂ) ^ (ρ + conj ρ' - 1)) /
          (ρ + conj ρ' - 1)) := by
  let z : ℂ := ρ + conj ρ' - 2
  have hz : z ≠ -1 := by
    intro heq
    have hi : ρ.im - ρ'.im = 0 := by
      simpa [z, sub_eq_add_neg] using congrArg Complex.im heq
    exact him (by linarith)
  have hzero : (0 : ℝ) ∉ Set.uIcc a b := by
    intro h
    rcases Set.mem_uIcc.mp h with h | h <;> linarith
  unfold zeroPairKernel
  rw [intervalIntegral.integral_const_mul,
    integral_cpow (Or.inr ⟨hz, hzero⟩)]
  dsimp [z]
  congr 1
  · congr 2 <;> ring

/-- The ordinate gap is bounded by the norm of the exact denominator. -/
theorem ordinate_gap_le_pairDenominator (ρ ρ' : ℂ) :
    |ρ.im - ρ'.im| ≤ ‖ρ + conj ρ' - 1‖ := by
  have h := Complex.abs_im_le_norm (ρ + conj ρ' - 1)
  simpa only [Complex.sub_im, Complex.add_im, Complex.conj_im,
    Complex.one_im, Complex.neg_im, sub_zero, sub_eq_add_neg, neg_zero, add_zero] using h

/-- The exact antiderivative gives a numerator consisting only of the two
endpoint powers.  This form deliberately retains the full complex
denominator for the subsequent ordinate-gap comparison. -/
theorem norm_integral_zeroPairKernel_le_endpoint_div
    (multiplicity : ℂ → ℕ) (ρ ρ' : ℂ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (him : ρ.im ≠ ρ'.im) :
    ‖∫ t : ℝ in a..b, zeroPairKernel multiplicity ρ ρ' t‖ ≤
      ((multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ)) *
        (Real.rpow b (ρ.re + ρ'.re - 1) +
          Real.rpow a (ρ.re + ρ'.re - 1)) /
        ‖ρ + conj ρ' - 1‖ := by
  rw [integral_zeroPairKernel_eq_div multiplicity ρ ρ' ha hb him]
  simp only [norm_mul, norm_natCast, Nat.cast_nonneg, abs_of_nonneg,
    norm_div]
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _)
    (Nat.cast_nonneg _))
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  refine (norm_sub_le _ _).trans_eq ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hb,
    Complex.norm_cpow_eq_rpow_re_of_pos ha]
  congr 2 <;> simp

/-- Nonresonant endpoint bound with the manuscript's ordinate gap in the
denominator. -/
theorem norm_integral_zeroPairKernel_le_endpoint_gap
    (multiplicity : ℂ → ℕ) (ρ ρ' : ℂ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (him : ρ.im ≠ ρ'.im) :
    ‖∫ t : ℝ in a..b, zeroPairKernel multiplicity ρ ρ' t‖ ≤
      ((multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ)) *
        (Real.rpow b (ρ.re + ρ'.re - 1) +
          Real.rpow a (ρ.re + ρ'.re - 1)) /
        |ρ.im - ρ'.im| := by
  refine (norm_integral_zeroPairKernel_le_endpoint_div
    multiplicity ρ ρ' ha hb him).trans ?_
  apply div_le_div_of_nonneg_left
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (add_nonneg (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg ha.le _))
  · exact abs_pos.mpr (sub_ne_zero.mpr him)
  · exact ordinate_gap_le_pairDenominator ρ ρ'

/-- Uniform endpoint rescaling on the manuscript interval.  The exponent
`beta + beta' - 1` lies in `[-1,1]`, so the fixed endpoint ratios cost at most
`6` and `4`, respectively. -/
theorem manuscript_endpoint_rpow_sum_le
    {X β β' : ℝ} (hX : 0 < X)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβ'0 : 0 ≤ β') (hβ'1 : β' ≤ 1) :
    Real.rpow (6 * X) (β + β' - 1) +
        Real.rpow (X / 4) (β + β' - 1) ≤
      10 * Real.rpow X (β + β' - 1) := by
  let s : ℝ := β + β' - 1
  have hslo : -1 ≤ s := by dsimp [s]; linarith
  have hshi : s ≤ 1 := by dsimp [s]; linarith
  have h6 : Real.rpow (6 : ℝ) s ≤ 6 := by
    calc
      Real.rpow (6 : ℝ) s ≤ Real.rpow 6 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hshi
      _ = 6 := by simp
  have hquarter : Real.rpow (1 / 4 : ℝ) s ≤ 4 := by
    calc
      Real.rpow (1 / 4 : ℝ) s ≤ Real.rpow (1 / 4) (-1) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hslo
      _ = 4 := by norm_num [Real.rpow_neg_one]
  have hXs : 0 ≤ Real.rpow X s := Real.rpow_nonneg hX.le s
  rw [show β + β' - 1 = s by rfl]
  have h6X : Real.rpow (6 * X) s =
      Real.rpow 6 s * Real.rpow X s :=
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) hX.le
  rw [h6X]
  have hdiv : X / 4 = (1 / 4 : ℝ) * X := by ring
  rw [hdiv]
  have hquarterX : Real.rpow ((1 / 4 : ℝ) * X) s =
      Real.rpow (1 / 4 : ℝ) s * Real.rpow X s :=
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) hX.le
  rw [hquarterX]
  nlinarith

/-- Pointwise rescaling on `[X/4,6X]` for the (nonpositive) integrand
exponent. -/
theorem manuscript_point_rpow_le
    {X t β β' : ℝ} (hX : 0 < X)
    (htlow : X / 4 ≤ t)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβ'0 : 0 ≤ β') (hβ'1 : β' ≤ 1) :
    Real.rpow t (β + β' - 2) ≤
      16 * Real.rpow X (β + β' - 2) := by
  let e : ℝ := β + β' - 2
  have helo : -2 ≤ e := by dsimp [e]; linarith
  have hehi : e ≤ 0 := by dsimp [e]; linarith
  have hquarterXpos : 0 < X / 4 := by positivity
  have htpos : 0 < t := hquarterXpos.trans_le htlow
  have hbase : Real.rpow t e ≤ Real.rpow (X / 4) e :=
    Real.rpow_le_rpow_of_nonpos hquarterXpos htlow hehi
  have hquarter : Real.rpow (1 / 4 : ℝ) e ≤ 16 := by
    calc
      Real.rpow (1 / 4 : ℝ) e ≤ Real.rpow (1 / 4) (-2) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) helo
      _ = 16 := by norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hXe : 0 ≤ Real.rpow X e := Real.rpow_nonneg hX.le e
  have hdiv : X / 4 = (1 / 4 : ℝ) * X := by ring
  have hquarterX : Real.rpow (X / 4) e =
      Real.rpow (1 / 4 : ℝ) e * Real.rpow X e := by
    rw [hdiv]
    exact Real.mul_rpow (by norm_num) hX.le
  rw [show β + β' - 2 = e by rfl]
  calc
    Real.rpow t e ≤ Real.rpow (X / 4) e := hbase
    _ = Real.rpow (1 / 4 : ℝ) e * Real.rpow X e := hquarterX
    _ ≤ 16 * Real.rpow X e :=
      mul_le_mul_of_nonneg_right hquarter hXe

/-- The no-cancellation bound, used for ordinate pairs at distance at most
one (and in particular on the diagonal). -/
theorem norm_integral_zeroPairKernel_le_trivial
    (multiplicity : ℂ → ℕ) (ρ ρ' : ℂ)
    {X : ℝ} (hX : 0 < X)
    (hρ0 : 0 ≤ ρ.re) (hρ1 : ρ.re ≤ 1)
    (hρ'0 : 0 ≤ ρ'.re) (hρ'1 : ρ'.re ≤ 1) :
    ‖∫ t : ℝ in X / 4..6 * X,
        zeroPairKernel multiplicity ρ ρ' t‖ ≤
      96 * ((multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ)) *
        Real.rpow X (ρ.re + ρ'.re - 1) := by
  have hpoint : ∀ t ∈ Set.uIoc (X / 4) (6 * X),
      ‖zeroPairKernel multiplicity ρ ρ' t‖ ≤
        16 * ((multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ)) *
          Real.rpow X (ρ.re + ρ'.re - 2) := by
    intro t ht
    have hends : X / 4 ≤ 6 * X := by linarith
    rw [Set.uIoc_of_le hends, Set.mem_Ioc] at ht
    have htpos : 0 < t := (by positivity : 0 < X / 4).trans ht.1
    unfold zeroPairKernel
    simp only [norm_mul, norm_natCast]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    have hexp : (ρ + conj ρ' - 2).re =
        ρ.re + ρ'.re - 2 := by norm_num
    rw [hexp]
    have hrpow := manuscript_point_rpow_le hX ht.1.le
      hρ0 hρ1 hρ'0 hρ'1
    calc
      (multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ) *
          Real.rpow t (ρ.re + ρ'.re - 2) ≤
        (multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ) *
          (16 * Real.rpow X (ρ.re + ρ'.re - 2)) :=
        mul_le_mul_of_nonneg_left hrpow
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      _ = 16 * ((multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ)) *
          Real.rpow X (ρ.re + ρ'.re - 2) := by ring
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hpoint).trans ?_
  have hlen : |6 * X - X / 4| ≤ 6 * X := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hcoeff : 0 ≤
      16 * ((multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ)) *
        Real.rpow X (ρ.re + ρ'.re - 2) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (Real.rpow_nonneg hX.le _)
  have hscale : Real.rpow X (ρ.re + ρ'.re - 2) * X =
      Real.rpow X (ρ.re + ρ'.re - 1) := by
    calc
      Real.rpow X (ρ.re + ρ'.re - 2) * X =
          Real.rpow X (ρ.re + ρ'.re - 2) * Real.rpow X 1 := by simp
      _ = Real.rpow X ((ρ.re + ρ'.re - 2) + 1) :=
        (Real.rpow_add hX (ρ.re + ρ'.re - 2) 1).symm
      _ = Real.rpow X (ρ.re + ρ'.re - 1) := by ring_nf
  calc
    (16 * ((multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ)) *
          Real.rpow X (ρ.re + ρ'.re - 2)) *
        |6 * X - X / 4| ≤
      (16 * ((multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ)) *
          Real.rpow X (ρ.re + ρ'.re - 2)) * (6 * X) :=
        mul_le_mul_of_nonneg_left hlen hcoeff
    _ = 96 * ((multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ)) *
        Real.rpow X (ρ.re + ρ'.re - 1) := by
      rw [← hscale]
      ring

/-- The cancellation branch on the manuscript interval, after rescaling the
two endpoint powers. -/
theorem norm_integral_zeroPairKernel_le_far
    (multiplicity : ℂ → ℕ) (ρ ρ' : ℂ)
    {X : ℝ} (hX : 0 < X)
    (hρ0 : 0 ≤ ρ.re) (hρ1 : ρ.re ≤ 1)
    (hρ'0 : 0 ≤ ρ'.re) (hρ'1 : ρ'.re ≤ 1)
    (him : ρ.im ≠ ρ'.im) :
    ‖∫ t : ℝ in X / 4..6 * X,
        zeroPairKernel multiplicity ρ ρ' t‖ ≤
      10 * ((multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ)) *
        Real.rpow X (ρ.re + ρ'.re - 1) /
        |ρ.im - ρ'.im| := by
  have hraw := norm_integral_zeroPairKernel_le_endpoint_gap
    multiplicity ρ ρ' (by positivity : 0 < X / 4)
      (by positivity : 0 < 6 * X) him
  refine hraw.trans ?_
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  have hend := manuscript_endpoint_rpow_sum_le hX
    hρ0 hρ1 hρ'0 hρ'1
  have hm : 0 ≤ (multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    ((multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ)) *
        (Real.rpow (6 * X) (ρ.re + ρ'.re - 1) +
          Real.rpow (X / 4) (ρ.re + ρ'.re - 1)) ≤
      ((multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ)) *
        (10 * Real.rpow X (ρ.re + ρ'.re - 1)) :=
      mul_le_mul_of_nonneg_left hend hm
    _ = 10 * ((multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ)) *
        Real.rpow X (ρ.re + ρ'.re - 1) := by ring

/-- Literal pair-kernel estimate used in the manuscript proof of (2.8), with
an explicit absolute constant.  The proof splits at unit ordinate distance:
direct integration near the diagonal and the exact antiderivative off it. -/
theorem norm_integral_zeroPairKernel_le_manuscript
    (multiplicity : ℂ → ℕ) (ρ ρ' : ℂ)
    {X : ℝ} (hX : 0 < X)
    (hρ0 : 0 ≤ ρ.re) (hρ1 : ρ.re ≤ 1)
    (hρ'0 : 0 ≤ ρ'.re) (hρ'1 : ρ'.re ≤ 1) :
    ‖∫ t : ℝ in X / 4..6 * X,
        zeroPairKernel multiplicity ρ ρ' t‖ ≤
      192 * ((multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ)) *
        Real.rpow X (ρ.re + ρ'.re - 1) /
        (1 + |ρ.im - ρ'.im|) := by
  let d : ℝ := |ρ.im - ρ'.im|
  have hd0 : 0 ≤ d := abs_nonneg _
  have hden : 0 < 1 + d := by linarith
  have hbase : 0 ≤
      ((multiplicity ρ : ℝ) * (multiplicity ρ' : ℝ)) *
        Real.rpow X (ρ.re + ρ'.re - 1) := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Real.rpow_nonneg hX.le _)
  by_cases hd : d ≤ 1
  · have htriv := norm_integral_zeroPairKernel_le_trivial
      multiplicity ρ ρ' hX hρ0 hρ1 hρ'0 hρ'1
    refine htriv.trans ?_
    rw [show |ρ.im - ρ'.im| = d by rfl]
    apply (le_div_iff₀ hden).2
    nlinarith
  · have hd1 : 1 < d := lt_of_not_ge hd
    have him : ρ.im ≠ ρ'.im := by
      intro heq
      simp [d, heq] at hd1
      linarith
    have hfar := norm_integral_zeroPairKernel_le_far
      multiplicity ρ ρ' hX hρ0 hρ1 hρ'0 hρ'1 him
    refine hfar.trans ?_
    rw [show |ρ.im - ρ'.im| = d by rfl]
    have hdpos : 0 < d := lt_trans (by norm_num) hd1
    apply (div_le_div_iff₀ hdpos hden).2
    nlinarith

end
end MAPAPZeroFieldEnergy28Core

#print axioms MAPAPZeroFieldEnergy28Core.finiteZeroField_mul_conj_eq_pairSum
#print axioms MAPAPZeroFieldEnergy28Core.ofReal_norm_finiteZeroField_sq_eq_pairSum
#print axioms MAPAPZeroFieldEnergy28Core.integral_norm_finiteZeroField_sq_eq_pairIntegrals
