import KoukExercise12TwoZeroSum
import QuantitativeFiniteAperture
import WideDiskLocalLogDerivative

/-!
# Buffered contour aperture for Koukoulopoulos, Exercise 12.2(a)

The local logarithmic-derivative disk has radius three.  Hence a Perron
height selected in `(H,H+1)` is tested against the fixed divisor of height
`H+4`.  This removes the otherwise circular dependence between the selected
height and the local disk.
-/

namespace MAPKoukExercise12TwoContourAperture

open Complex Set Metric DirichletZeros PrimitiveExplicitFormulaSpine
open MAPLocalZeroWindow MAPPrimitiveLogDerivativeRemainderUnconditional
open WideDiskLFunctionGrowth WideDiskBlaschkeAssembly WideDiskLocalLogDerivative
open QuantitativeFiniteAperture
open scoped BigOperators

noncomputable section

def exerciseBufferedRealCoordinates
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (H : ℝ) : Finset ℝ :=
  insert 0 (zeroRealCoordinates chi (H + 3))

def exerciseBufferedImagCoordinates
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (H : ℝ) : Finset ℝ :=
  signedZeroImagCoordinates chi (H + 3)

def exerciseContourClearance
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (H : ℝ) : ℝ :=
  min
    ((1 / 2 : ℝ) /
      (4 * ((exerciseBufferedRealCoordinates chi H).card + 1)))
    (1 /
      (4 * ((exerciseBufferedImagCoordinates chi H).card + 1)))

theorem exerciseContourClearance_pos
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (H : ℝ) :
    0 < exerciseContourClearance chi H := by
  unfold exerciseContourClearance
  apply lt_min <;> positivity

theorem zeroSupport_card_le_dirichletZeroCount
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (sigma T : ℝ) :
    (zeroSupport chi sigma T).card ≤ dirichletZeroCount chi sigma T := by
  unfold dirichletZeroCount
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro rho hrho
  exact MAPZeroFreeSiegelSpine.zeroMultiplicity_pos_of_mem
    chi sigma T hrho

/-- The inverse aperture clearance costs at most one linear divisor count. -/
theorem inv_exerciseContourClearance_le_count
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (H : ℝ) :
    (exerciseContourClearance chi H)⁻¹ ≤
      16 * ((dirichletZeroCount chi 0 (H + 4) : ℝ) + 1) := by
  classical
  let S := zeroSupport chi 0 (H + 4)
  let Z := dirichletZeroCount chi 0 (H + 4)
  have hSZ : S.card ≤ Z := by
    dsimp [S, Z]
    exact zeroSupport_card_le_dirichletZeroCount chi 0 (H + 4)
  have hrealCard : (exerciseBufferedRealCoordinates chi H).card ≤ Z + 1 := by
    calc
      (exerciseBufferedRealCoordinates chi H).card ≤
          (zeroRealCoordinates chi (H + 3)).card + 1 := by
        unfold exerciseBufferedRealCoordinates
        exact Finset.card_insert_le _ _
      _ ≤ S.card + 1 := by
        apply Nat.add_le_add_right
        unfold zeroRealCoordinates
        have heq : zeroSupport chi 0 (H + 3 + 1) = S := by
          dsimp [S]
          congr 1
          ring
        rw [heq]
        exact Finset.card_image_le
      _ ≤ Z + 1 := Nat.add_le_add_right hSZ 1
  have himagCard : (exerciseBufferedImagCoordinates chi H).card ≤ 2 * Z := by
    calc
      (exerciseBufferedImagCoordinates chi H).card ≤
          2 * S.card := by
        unfold exerciseBufferedImagCoordinates signedZeroImagCoordinates
        calc
          ((zeroSupport chi 0 (H + 3 + 1)).image Complex.im ∪
              (zeroSupport chi 0 (H + 3 + 1)).image
                (fun rho => -rho.im)).card ≤
              ((zeroSupport chi 0 (H + 3 + 1)).image Complex.im).card +
              ((zeroSupport chi 0 (H + 3 + 1)).image
                (fun rho => -rho.im)).card := Finset.card_union_le _ _
          _ ≤ 2 * (zeroSupport chi 0 (H + 3 + 1)).card := by
            have h₁ := Finset.card_image_le (s := zeroSupport chi 0 (H + 3 + 1))
              (f := Complex.im)
            have h₂ := Finset.card_image_le
              (s := zeroSupport chi 0 (H + 3 + 1))
              (f := fun rho : ℂ => -rho.im)
            omega
          _ = 2 * S.card := by
            dsimp [S]
            congr 2
            ring
      _ ≤ 2 * Z := Nat.mul_le_mul_left 2 hSZ
  have hrealCast :
      ((exerciseBufferedRealCoordinates chi H).card : ℝ) ≤ (Z : ℝ) + 1 := by
    exact_mod_cast hrealCard
  have himagCast :
      ((exerciseBufferedImagCoordinates chi H).card : ℝ) ≤ 2 * (Z : ℝ) := by
    exact_mod_cast himagCard
  have hZ0 : (0 : ℝ) ≤ Z := by positivity
  have ha : 1 / (16 * ((Z : ℝ) + 1)) ≤
      (1 / 2 : ℝ) /
        (4 * ((exerciseBufferedRealCoordinates chi H).card + 1)) := by
    rw [show (1 / 2 : ℝ) /
        (4 * ((exerciseBufferedRealCoordinates chi H).card + 1)) =
          1 / (8 * ((exerciseBufferedRealCoordinates chi H).card + 1)) by
      field_simp
      norm_num]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hb : 1 / (16 * ((Z : ℝ) + 1)) ≤
      1 / (4 * ((exerciseBufferedImagCoordinates chi H).card + 1)) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hdLower : 1 / (16 * ((Z : ℝ) + 1)) ≤
      exerciseContourClearance chi H := by
    unfold exerciseContourClearance
    exact le_min ha hb
  have hbasePos : 0 < 1 / (16 * ((Z : ℝ) + 1)) := by positivity
  have hinv := (inv_le_inv₀ (exerciseContourClearance_pos chi H)
    hbasePos).2 hdLower
  calc
    (exerciseContourClearance chi H)⁻¹ ≤
        (1 / (16 * ((Z : ℝ) + 1)))⁻¹ := hinv
    _ = 16 * ((Z : ℝ) + 1) := by field_simp

/-- Quantitative aperture against the fixed height-`H+4` divisor. -/
theorem exists_exerciseContourAperture
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {H c : ℝ} :
    ∃ sigma ∈ Set.Ioo (0 : ℝ) (1 / 2),
      ∃ T ∈ Set.Ioo H (H + 1),
        exerciseContourClearance chi H ≤ sigma ∧
        (∀ u ∈ Set.Icc (-T) T,
          ∀ rho ∈ zeroSupport chi 0 (H + 4),
            exerciseContourClearance chi H ≤
              ‖((sigma : ℂ) + (u : ℂ) * Complex.I) - rho‖) ∧
        (∀ r ∈ Set.Icc sigma c,
          ∀ rho ∈ zeroSupport chi 0 (H + 4),
            exerciseContourClearance chi H ≤
              ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho‖) ∧
        (∀ r ∈ Set.Icc sigma c,
          ∀ rho ∈ zeroSupport chi 0 (H + 4),
            exerciseContourClearance chi H ≤
              ‖((r : ℂ) + (T : ℂ) * Complex.I) - rho‖) := by
  classical
  let S := zeroSupport chi 0 (H + 4)
  let R := exerciseBufferedRealCoordinates chi H
  let A := exerciseBufferedImagCoordinates chi H
  obtain ⟨sigma, hsigma, hsigmaClear⟩ :=
    exists_mem_Ioo_with_finset_clearance R
      (a := 0) (b := 1 / 2) (by norm_num)
  obtain ⟨T, hT, hTClear⟩ :=
    exists_mem_Ioo_with_finset_clearance A
      (a := H) (b := H + 1) (by linarith)
  have hzeroR : (0 : ℝ) ∈ R := by
    simp [R, exerciseBufferedRealCoordinates]
  have hsigmaRaw := hsigmaClear 0 hzeroR
  have hsigmaBase :
      (1 / 2 : ℝ) /
          (4 * ((exerciseBufferedRealCoordinates chi H).card + 1)) ≤ sigma := by
    dsimp [R] at hsigmaRaw
    norm_num [abs_of_pos hsigma.1] at hsigmaRaw
    exact hsigmaRaw
  have hdSigma : exerciseContourClearance chi H ≤ sigma :=
    (min_le_left _ _).trans hsigmaBase
  have hleft : ∀ u ∈ Set.Icc (-T) T, ∀ rho ∈ S,
      exerciseContourClearance chi H ≤
        ‖((sigma : ℂ) + (u : ℂ) * Complex.I) - rho‖ := by
    intro u hu rho hrho
    have hrho' : rho ∈ zeroSupport chi 0 (H + 3 + 1) := by
      dsimp only [S] at hrho
      convert hrho using 1 <;> ring
    have hrhoR : rho.re ∈ R := by
      simp only [R, exerciseBufferedRealCoordinates, Finset.mem_insert]
      right
      exact Finset.mem_image.mpr ⟨rho, hrho', rfl⟩
    have hcoord := hsigmaClear rho.re hrhoR
    have hcoord' :
        (1 / 2 : ℝ) /
            (4 * ((exerciseBufferedRealCoordinates chi H).card + 1)) ≤
          |sigma - rho.re| := by
      simpa [R] using hcoord
    exact ((min_le_left _ _).trans hcoord').trans (by
      simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
        Complex.ofReal_im, zero_mul, sub_zero, add_zero] using
          Complex.abs_re_le_norm
            (((sigma : ℂ) + (u : ℂ) * Complex.I) - rho))
  have hbottom : ∀ r ∈ Set.Icc sigma c, ∀ rho ∈ S,
      exerciseContourClearance chi H ≤
        ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho‖ := by
    intro r hr rho hrho
    have hrho' : rho ∈ zeroSupport chi 0 (H + 3 + 1) := by
      dsimp only [S] at hrho
      convert hrho using 1 <;> ring
    have hrhoA : -rho.im ∈ A := by
      dsimp [A, exerciseBufferedImagCoordinates]
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨rho, hrho', rfl⟩
    have hcoord := hTClear (-rho.im) hrhoA
    have hcoord' :
        1 / (4 * ((exerciseBufferedImagCoordinates chi H).card + 1)) ≤
          |T - (-rho.im)| := by
      simpa [A] using hcoord
    calc
      exerciseContourClearance chi H ≤ |T - (-rho.im)| :=
        (min_le_right _ _).trans hcoord'
      _ = |(-T) - rho.im| := by
        rw [show (-T) - rho.im = -(T - (-rho.im)) by ring, abs_neg]
      _ ≤ ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho‖ := by
        simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          mul_one, zero_mul, add_zero, zero_add] using
            Complex.abs_im_le_norm
              (((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - rho)
  have htop : ∀ r ∈ Set.Icc sigma c, ∀ rho ∈ S,
      exerciseContourClearance chi H ≤
        ‖((r : ℂ) + (T : ℂ) * Complex.I) - rho‖ := by
    intro r hr rho hrho
    have hrho' : rho ∈ zeroSupport chi 0 (H + 3 + 1) := by
      dsimp only [S] at hrho
      convert hrho using 1 <;> ring
    have hrhoA : rho.im ∈ A := by
      dsimp [A, exerciseBufferedImagCoordinates]
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨rho, hrho', rfl⟩
    have hcoord := hTClear rho.im hrhoA
    have hcoord' :
        1 / (4 * ((exerciseBufferedImagCoordinates chi H).card + 1)) ≤
          |T - rho.im| := by
      simpa [A] using hcoord
    exact ((min_le_right _ _).trans hcoord').trans (by
      simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
        mul_one, zero_mul, add_zero, zero_add] using
          Complex.abs_im_le_norm
            (((r : ℂ) + (T : ℂ) * Complex.I) - rho))
  exact ⟨sigma, hsigma, T, hT, hdSigma, hleft, hbottom, htop⟩

/-- A local radius-three zero at ordinate `t`, with nonnegative real part,
belongs to the fixed height-`H+4` divisor whenever `|t| ≤ H+1`. -/
theorem mem_globalBufferedSupport_of_mem_wide_of_nonneg_re
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {H t : ℝ} (ht : |t| ≤ H + 1) {rho : ℂ}
    (hrho : rho ∈ wideZeroSupport chi t) (hre : 0 ≤ rho.re) :
    rho ∈ zeroSupport chi 0 (H + 4) := by
  have hbase := mem_baseZeroSupport_of_mem_wideZeroSupport chi hrho
  have hrectBase := mem_zeroRectangle_of_mem_zeroSupport chi (-1) (|t| + 3) hbase
  have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport
    chi (-1) (|t| + 3) hbase
  have him : |rho.im| ≤ H + 4 := by
    have himBase : |rho.im| ≤ |t| + 3 := abs_le.mpr hrectBase.2
    linarith
  have hrect : rho ∈ zeroRectangle 0 (H + 4) := by
    rw [zeroRectangle, Complex.mem_reProdIm]
    exact ⟨⟨hre, hrectBase.1.2⟩, abs_le.mp him⟩
  exact (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
    chi 0 (H + 4) hrect).mpr hzero

/-- Global-buffer clearance plus the inserted lower boundary controls every
local radius-three zero. -/
theorem exerciseClearance_le_norm_sub_wide
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {H t r : ℝ} (ht : |t| ≤ H + 1)
    (hdSigma : exerciseContourClearance chi H ≤ r)
    {rho : ℂ} (hrho : rho ∈ wideZeroSupport chi t)
    (hdGlobal : ∀ z ∈ zeroSupport chi 0 (H + 4),
      exerciseContourClearance chi H ≤
        ‖((r : ℂ) + Complex.I * t) - z‖) :
    exerciseContourClearance chi H ≤
      ‖((r : ℂ) + Complex.I * t) - rho‖ := by
  by_cases hre : 0 ≤ rho.re
  · exact hdGlobal rho
      (mem_globalBufferedSupport_of_mem_wide_of_nonneg_re chi ht hrho hre)
  · have hr0 : 0 < r :=
      (exerciseContourClearance_pos chi H).trans_le hdSigma
    have hreal : r ≤ |r - rho.re| := by
      rw [abs_of_pos (by linarith)]
      linarith
    exact hdSigma.trans (hreal.trans (by
      simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
        Complex.ofReal_im, zero_mul, sub_zero, add_zero] using
          Complex.abs_re_le_norm (((r : ℂ) + Complex.I * t) - rho)))

/-- Explicit local-Blaschke bound for the source logarithmic derivative at
one point of the selected contour. -/
theorem norm_logDeriv_LFunction_le_of_wide_clearance
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {t r d : ℝ} (hr0 : 0 < r) (hr4 : r < 4) (hd : 0 < d)
    (hdist : ∀ rho ∈ wideZeroSupport chi t,
      d ≤ ‖((r : ℂ) + Complex.I * t) - rho‖) :
    ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * t)‖ ≤
      20 * (Real.log 21600 + 2 * Real.log (arithmeticScale q t)) +
        5520 * Real.log (arithmeticScale q t) +
        (5520 * Real.log (arithmeticScale q t)) / d := by
  let s : ℂ := (r : ℂ) + Complex.I * t
  have hsball : s ∈ Metric.ball (wideCenter t) 2 := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hdiff : s - wideCenter t = ((r - 2 : ℝ) : ℂ) := by
      dsimp [s, wideCenter]
      push_cast
      ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hsF : s ∉ wideZeroSupport chi t := by
    intro hsupp
    have hz := hdist s hsupp
    simp [s] at hz
    linarith
  have hlocal := norm_localDeflatedLogDeriv_le chi hchi hsball hsF
  have hmass := wideZeroMultiplicity_mass_le_logScale chi hprim hchi t
  let P : ℂ := ∑ rho ∈ wideZeroSupport chi t,
    (wideZeroMultiplicity chi t rho : ℂ) / (s - rho)
  have hpole : ‖P‖ ≤
      (∑ rho ∈ wideZeroSupport chi t,
        (wideZeroMultiplicity chi t rho : ℝ)) / d := by
    dsimp [P]
    calc
      ‖∑ rho ∈ wideZeroSupport chi t,
          (wideZeroMultiplicity chi t rho : ℂ) / (s - rho)‖ ≤
        ∑ rho ∈ wideZeroSupport chi t,
          ‖(wideZeroMultiplicity chi t rho : ℂ) / (s - rho)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ rho ∈ wideZeroSupport chi t,
          (wideZeroMultiplicity chi t rho : ℝ) / d := by
        apply Finset.sum_le_sum
        intro rho hrho
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd
          (hdist rho hrho)
      _ = (∑ rho ∈ wideZeroSupport chi t,
          (wideZeroMultiplicity chi t rho : ℝ)) / d := by
        rw [Finset.sum_div]
  have hpole' : ‖P‖ ≤ 5520 * Real.log (arithmeticScale q t) / d :=
    hpole.trans (div_le_div_of_nonneg_right hmass hd.le)
  have hreg : DirichletZeros.regularizedLFunction chi =
      DirichletCharacter.LFunction chi := by
    funext z
    simp [DirichletZeros.regularizedLFunction, hchi]
  rw [← hreg]
  calc
    ‖logDeriv (regularizedLFunction chi) s‖ =
        ‖(logDeriv (regularizedLFunction chi) s - P) + P‖ := by
      congr 1
      ring
    _ ≤ ‖logDeriv (regularizedLFunction chi) s - P‖ + ‖P‖ :=
      norm_add_le _ _
    _ ≤ (20 * (Real.log 21600 + 2 * Real.log (arithmeticScale q t)) +
          ∑ rho ∈ wideZeroSupport chi t,
            (wideZeroMultiplicity chi t rho : ℝ)) +
        (5520 * Real.log (arithmeticScale q t) / d) :=
      add_le_add (by simpa only [P, s] using hlocal) hpole'
    _ ≤ 20 * (Real.log 21600 + 2 * Real.log (arithmeticScale q t)) +
        5520 * Real.log (arithmeticScale q t) +
        (5520 * Real.log (arithmeticScale q t)) / d := by
      linarith

#print axioms MAPKoukExercise12TwoContourAperture.exists_exerciseContourAperture
#print axioms MAPKoukExercise12TwoContourAperture.norm_logDeriv_LFunction_le_of_wide_clearance

end

end MAPKoukExercise12TwoContourAperture
