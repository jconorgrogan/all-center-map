import WideDiskLocalMass
import ZeroFreeSiegelSpine

/-!
# Premise-free primitive logarithmic-derivative remainder

This closes the quantitative content of Koukoulopoulos, Lemma 11.4(b), in
the exact centered-window normalization used by `ZeroFreeSiegelSpine`.
The radius-three Blaschke estimate removes all local zeros; zeros outside the
centered unit window are at distance at least `1/2` from `u + it` and hence
cost at most twice their multiplicity.  The certified six-window local count
then gives one absolute logarithmic bound.
-/

namespace MAPPrimitiveLogDerivativeRemainderUnconditional

open Complex Set Metric DirichletZeros PrimitiveExplicitFormulaSpine
open MAPLocalZeroWindow MAPMellinDetectorLeaf MAPZeroFreeSiegelSpine
open WideDiskLFunctionGrowth WideDiskBlaschkeAssembly
open WideDiskLocalLogDerivative WideDiskLocalMass
open scoped BigOperators

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The arithmetic scale is at least two, a useful uniform lower bound for
absorbing all absolute constants into its logarithm. -/
theorem two_le_arithmeticScale (t : ℝ) :
    2 ≤ arithmeticScale q t := by
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  unfold arithmeticScale
  nlinarith [abs_nonneg t]

/-- Moving the height by at most three enlarges the arithmetic scale by at
most a factor three. -/
theorem arithmeticScale_le_three_mul_of_abs_sub_le_three
    {t v : ℝ} (hvt : |v - t| ≤ 3) :
    arithmeticScale q v ≤ 3 * arithmeticScale q t := by
  have habs : |v| ≤ |t| + 3 := by
    calc
      |v| = |(v - t) + t| := by ring_nf
      _ ≤ |v - t| + |t| := abs_add_le _ _
      _ ≤ |t| + 3 := by linarith
  have hq0 : (0 : ℝ) ≤ q := by positivity
  unfold arithmeticScale
  have hinner : |v| + 2 ≤ 3 * (|t| + 2) := by
    linarith [abs_nonneg t]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (mul_le_mul_of_nonneg_left hinner hq0)

/-- The logarithm of every height scale within distance three is at most
three times the logarithm of the central scale. -/
theorem log_arithmeticScale_le_three_mul_of_abs_sub_le_three
    {t v : ℝ} (hvt : |v - t| ≤ 3) :
    Real.log (arithmeticScale q v) ≤
      3 * Real.log (arithmeticScale q t) := by
  let S := arithmeticScale q t
  have hS2 : 2 ≤ S := two_le_arithmeticScale t
  have hS0 : 0 < S := by linarith
  have hv0 : 0 < arithmeticScale q v := by
    have := two_le_arithmeticScale (q := q) v
    linarith
  have hshift : arithmeticScale q v ≤ 3 * S :=
    arithmeticScale_le_three_mul_of_abs_sub_le_three hvt
  have hthree : 3 * S ≤ S ^ (3 : ℕ) := by
    nlinarith [sq_nonneg (S - 2)]
  calc
    Real.log (arithmeticScale q v) ≤ Real.log (S ^ (3 : ℕ)) :=
      Real.log_le_log hv0 (hshift.trans hthree)
    _ = 3 * Real.log S := by rw [Real.log_pow]; norm_num

/-- Every zero in the centered unit window lies in the radius-three support
used by the certified Blaschke decomposition. -/
theorem centeredUnitWindowSupport_subset_wideZeroSupport
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    centeredUnitWindowSupport χ (1 / 2) t ⊆ wideZeroSupport χ t := by
  intro ρ hρ
  have hclosed :
      ρ ∈ closedUnitWindowSupport χ (1 / 2) (t - 1 / 2) := hρ
  have hinterval := (Finset.mem_filter.mp hclosed).2
  have hrect := closedUnitWindowSupport_mem_rectangle χ hclosed
  have hreAbs : |ρ.re - 2| ≤ 3 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hrect.1.1, hrect.1.2]
  have himAbs : |ρ.im - t| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hinterval.1, hinterval.2]
  have hnorm : ‖ρ - wideCenter t‖ < 3 := by
    calc
      ‖ρ - wideCenter t‖ ≤ |(ρ - wideCenter t).re| +
          |(ρ - wideCenter t).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |ρ.re - 2| + |ρ.im - t| := by simp [wideCenter]
      _ ≤ 3 / 2 + 1 / 2 := add_le_add hreAbs himAbs
      _ < 3 := by norm_num
  have hball : ρ ∈ Metric.ball (wideCenter t) wideRadius := by
    simpa [Metric.mem_ball, dist_eq_norm, wideRadius] using hnorm
  have hzero : regularizedLFunction χ ρ = 0 :=
    regularizedLFunction_eq_zero_of_mem_zeroSupport χ (1 / 2)
      (windowHeight (t - 1 / 2)) (Finset.mem_filter.mp hclosed).1
  exact mem_wideZeroSupport_of_eq_zero_of_mem_ball χ hball hzero

/-- Multiplicity is independent of which of the two certified compact
rectangles is used once the zero lies in both. -/
theorem wideZeroMultiplicity_eq_centered
    (χ : DirichletCharacter ℂ q) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ centeredUnitWindowSupport χ (1 / 2) t) :
    wideZeroMultiplicity χ t ρ =
      zeroMultiplicity χ (1 / 2) (windowHeight (t - 1 / 2)) ρ := by
  have hwide := centeredUnitWindowSupport_subset_wideZeroSupport χ t hρ
  exact zeroMultiplicity_eq_of_mem_rectangles χ
    ((zeroDivisor χ (-1) (|t| + 3)).supportWithinDomain
      ((zeroSupport_mem_iff χ (-1) (|t| + 3) ρ).mp
        (mem_baseZeroSupport_of_mem_wideZeroSupport χ hwide)))
    (closedUnitWindowSupport_mem_rectangle χ hρ)

/-- A radius-three zero omitted by the centered unit window stays at least
`1/2` away from every evaluation point `u + it` with `u > 1`. -/
theorem half_le_norm_sub_of_mem_wide_sdiff_centered
    (χ : DirichletCharacter ℂ q) {u t : ℝ} (hu : 1 < u) {ρ : ℂ}
    (hρ : ρ ∈ wideZeroSupport χ t \
      centeredUnitWindowSupport χ (1 / 2) t) :
    1 / 2 ≤ ‖((u : ℂ) + Complex.I * t) - ρ‖ := by
  have hwide := (Finset.mem_sdiff.mp hρ).1
  have hnot := (Finset.mem_sdiff.mp hρ).2
  have hbase := mem_baseZeroSupport_of_mem_wideZeroSupport χ hwide
  have hrect := (zeroDivisor χ (-1) (|t| + 3)).supportWithinDomain
    ((zeroSupport_mem_iff χ (-1) (|t| + 3) ρ).mp hbase)
  have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport
    χ (-1) (|t| + 3) hbase
  by_cases hre : 1 / 2 ≤ ρ.re
  · have hnotInterval : ¬ (t - 1 / 2 ≤ ρ.im ∧ ρ.im ≤ t + 1 / 2) := by
      intro him
      apply hnot
      have himAbs : |ρ.im| ≤ windowHeight (t - 1 / 2) := by
        unfold windowHeight
        rw [abs_le]
        constructor <;>
          linarith [him.1, him.2, le_abs_self (t - 1 / 2),
            neg_le_abs (t - 1 / 2)]
      have htargetRect :
          ρ ∈ zeroRectangle (1 / 2) (windowHeight (t - 1 / 2)) :=
        ⟨⟨hre, hrect.1.2⟩, abs_le.mp himAbs⟩
      rw [centeredUnitWindowSupport, closedUnitWindowSupport,
        Finset.mem_filter]
      exact ⟨(MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero χ
        (1 / 2) (windowHeight (t - 1 / 2)) htargetRect).2 hzero,
          ⟨him.1, by linarith [him.2]⟩⟩
    rcases not_and_or.mp hnotInterval with hlo | hhi
    · have him : ρ.im < t - 1 / 2 := lt_of_not_ge hlo
      have hcoord := Complex.abs_im_le_norm
        (((u : ℂ) + Complex.I * t) - ρ)
      have habs : 1 / 2 <
          |(((u : ℂ) + Complex.I * t) - ρ).im| := by
        simp only [sub_im, add_im, ofReal_im, mul_im, I_re, ofReal_re,
          I_im, zero_mul, one_mul, zero_add]
        rw [abs_of_pos]
        · linarith
        · linarith
      linarith
    · have him : t + 1 / 2 < ρ.im := lt_of_not_ge hhi
      have hcoord := Complex.abs_im_le_norm
        (((u : ℂ) + Complex.I * t) - ρ)
      have habs : 1 / 2 <
          |(((u : ℂ) + Complex.I * t) - ρ).im| := by
        simp only [sub_im, add_im, ofReal_im, mul_im, I_re, ofReal_re,
          I_im, zero_mul, one_mul, zero_add]
        rw [abs_of_neg]
        · linarith
        · linarith
      linarith
  · have hre' : ρ.re < 1 / 2 := lt_of_not_ge hre
    have hcoord := Complex.abs_re_le_norm
      (((u : ℂ) + Complex.I * t) - ρ)
    have habs : 1 / 2 <
        |(((u : ℂ) + Complex.I * t) - ρ).re| := by
      simp only [sub_re, add_re, ofReal_re, mul_re, I_re, ofReal_im,
        I_im, zero_mul, sub_zero, zero_add]
      rw [abs_of_pos]
      · linarith
      · linarith
    linarith

/-- Exact cancellation of the common centered zeros before taking norms. -/
theorem widePoleSum_sub_centeredPoleSum_eq_sdiff
    (χ : DirichletCharacter ℂ q) (u t : ℝ) :
    (∑ ρ ∈ wideZeroSupport χ t,
        (wideZeroMultiplicity χ t ρ : ℂ) /
          ((u : ℂ) + Complex.I * t - ρ)) -
      centeredZeroPoleSum χ t ((u : ℂ) + Complex.I * t) =
    ∑ ρ ∈ wideZeroSupport χ t \
        centeredUnitWindowSupport χ (1 / 2) t,
      (wideZeroMultiplicity χ t ρ : ℂ) /
        ((u : ℂ) + Complex.I * t - ρ) := by
  let W := wideZeroSupport χ t
  let C := centeredUnitWindowSupport χ (1 / 2) t
  have hCW : C ⊆ W := centeredUnitWindowSupport_subset_wideZeroSupport χ t
  have hcommon :
      (∑ ρ ∈ C, (wideZeroMultiplicity χ t ρ : ℂ) /
          ((u : ℂ) + Complex.I * t - ρ)) =
        centeredZeroPoleSum χ t ((u : ℂ) + Complex.I * t) := by
    unfold centeredZeroPoleSum
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [wideZeroMultiplicity_eq_centered χ hρ]
  change (∑ ρ ∈ W, _) - _ = ∑ ρ ∈ W \ C, _
  rw [← Finset.sum_sdiff hCW, hcommon]
  ring

/-- The signed local pole mismatch costs at most twice the radius-three
multiplicity mass. -/
theorem norm_widePoleSum_sub_centeredPoleSum_le
    (χ : DirichletCharacter ℂ q) {u t : ℝ} (hu : 1 < u) :
    ‖(∑ ρ ∈ wideZeroSupport χ t,
        (wideZeroMultiplicity χ t ρ : ℂ) /
          ((u : ℂ) + Complex.I * t - ρ)) -
      centeredZeroPoleSum χ t ((u : ℂ) + Complex.I * t)‖ ≤
      2 * ∑ ρ ∈ wideZeroSupport χ t,
        (wideZeroMultiplicity χ t ρ : ℝ) := by
  rw [widePoleSum_sub_centeredPoleSum_eq_sdiff χ u t]
  calc
    ‖∑ ρ ∈ wideZeroSupport χ t \
        centeredUnitWindowSupport χ (1 / 2) t,
      (wideZeroMultiplicity χ t ρ : ℂ) /
        ((u : ℂ) + Complex.I * t - ρ)‖ ≤
      ∑ ρ ∈ wideZeroSupport χ t \
          centeredUnitWindowSupport χ (1 / 2) t,
        ‖(wideZeroMultiplicity χ t ρ : ℂ) /
          ((u : ℂ) + Complex.I * t - ρ)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ wideZeroSupport χ t \
          centeredUnitWindowSupport χ (1 / 2) t,
        2 * (wideZeroMultiplicity χ t ρ : ℝ) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      rw [norm_div, norm_natCast]
      have hd := half_le_norm_sub_of_mem_wide_sdiff_centered χ hu hρ
      have hd0 : 0 < ‖((u : ℂ) + Complex.I * t) - ρ‖ := by linarith
      have hm0 : (0 : ℝ) ≤ (wideZeroMultiplicity χ t ρ : ℝ) :=
        Nat.cast_nonneg _
      apply (div_le_iff₀ hd0).2
      nlinarith
    _ ≤ ∑ ρ ∈ wideZeroSupport χ t,
        2 * (wideZeroMultiplicity χ t ρ : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun _ _ _ => by positivity)
    _ = 2 * ∑ ρ ∈ wideZeroSupport χ t,
        (wideZeroMultiplicity χ t ρ : ℝ) := by rw [Finset.mul_sum]

/-- The six-window local mass is bounded by one absolute multiple of the
central arithmetic logarithm. -/
theorem wideZeroMultiplicity_mass_le_logScale
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (t : ℝ) :
    (∑ ρ ∈ wideZeroSupport χ t,
        (wideZeroMultiplicity χ t ρ : ℝ)) ≤
      5520 * Real.log (arithmeticScale q t) := by
  let S := arithmeticScale q t
  have hS2 : 2 ≤ S := two_le_arithmeticScale t
  have hlogS : 1 / 2 ≤ Real.log S := by
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    exact hlog2.trans (Real.log_le_log (by norm_num) hS2)
  have hbase := wideZeroMultiplicity_mass_le_explicit χ hprim hχ t
  apply hbase.trans
  calc
    (∑ j ∈ Finset.range 6,
        (1 + 153 * Real.log (arithmeticScale q (t - 3 + (j : ℝ))) +
          153 * Real.log
            (arithmeticScale q (-(t - 3 + (j : ℝ)) - 1)))) ≤
      ∑ _j ∈ Finset.range 6, 920 * Real.log S := by
        apply Finset.sum_le_sum
        intro j hj
        have hjlt : j < 6 := Finset.mem_range.mp hj
        have hjle : (j : ℝ) ≤ 5 := by exact_mod_cast (Nat.le_of_lt_succ hjlt)
        have hj0 : (0 : ℝ) ≤ j := by positivity
        have hnear : |(t - 3 + (j : ℝ)) - t| ≤ 3 := by
          rw [show t - 3 + (j : ℝ) - t = (j : ℝ) - 3 by ring]
          rw [abs_le]
          constructor <;> linarith
        have hnearNeg :
            |(-(t - 3 + (j : ℝ)) - 1) - (-t)| ≤ 3 := by
          rw [show -(t - 3 + (j : ℝ)) - 1 - (-t) =
            2 - (j : ℝ) by ring]
          rw [abs_le]
          constructor <;> linarith
        have hlog1 :=
          log_arithmeticScale_le_three_mul_of_abs_sub_le_three
            (q := q) hnear
        have hlog2 :=
          log_arithmeticScale_le_three_mul_of_abs_sub_le_three
            (q := q) hnearNeg
        have hnegScale : arithmeticScale q (-t) = S := by
          simp [S, arithmeticScale]
        rw [hnegScale] at hlog2
        nlinarith
    _ = 5520 * Real.log S := by simp; ring

/-- Explicit pointwise form of Koukoulopoulos Lemma 11.4(b). -/
theorem primitiveLogDerivativeRemainder_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {u t : ℝ} (hu : 1 < u) (hu2 : u ≤ 2) :
    ‖primitiveLogDerivativeRemainder χ u t‖ ≤
      17000 * Real.log (arithmeticScale q t) := by
  let s : ℂ := (u : ℂ) + Complex.I * t
  let W : ℂ := ∑ ρ ∈ wideZeroSupport χ t,
    (wideZeroMultiplicity χ t ρ : ℂ) / (s - ρ)
  let C : ℂ := centeredZeroPoleSum χ t s
  let M : ℝ := ∑ ρ ∈ wideZeroSupport χ t,
    (wideZeroMultiplicity χ t ρ : ℝ)
  have hs : s ∈ Metric.ball (wideCenter t) 2 := by
    rw [Metric.mem_ball, dist_eq_norm]
    dsimp [s, wideCenter]
    have huabs : |u - 2| < 2 := by
      rw [abs_lt]
      constructor <;> linarith
    rw [show (u : ℂ) + Complex.I * (t : ℂ) -
        (2 + Complex.I * (t : ℂ)) = ((u - 2 : ℝ) : ℂ) by
      push_cast
      ring]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact huabs
  have hsF : s ∉ wideZeroSupport χ t := by
    intro hmem
    have hre := re_lt_one_of_mem_zeroSupport χ
      (mem_baseZeroSupport_of_mem_wideZeroSupport χ hmem)
    dsimp [s] at hre
    simp at hre
    linarith
  have hlocal := norm_localDeflatedLogDeriv_le χ hχ hs hsF
  have hmismatch : ‖W - C‖ ≤ 2 * M := by
    simpa only [W, C, M, s] using
      norm_widePoleSum_sub_centeredPoleSum_le χ hu
  have hremEq :
      primitiveLogDerivativeRemainder χ u t =
        -(logDeriv (regularizedLFunction χ) s - C) := by
    have heq :=
      neg_logDeriv_regularizedLFunction_eq_centeredZeroSum_add_deflated
        χ t (s := s) (by dsimp [s]; simpa using hu.le)
    dsimp [primitiveLogDerivativeRemainder, C, s] at heq ⊢
    linear_combination -heq
  have hsplit :
      logDeriv (regularizedLFunction χ) s - C =
        (logDeriv (regularizedLFunction χ) s - W) + (W - C) := by ring
  have hraw :
      ‖primitiveLogDerivativeRemainder χ u t‖ ≤
        20 * (Real.log 21600 + 2 * Real.log (arithmeticScale q t)) +
          3 * M := by
    rw [hremEq, norm_neg, hsplit]
    calc
      ‖(logDeriv (regularizedLFunction χ) s - W) + (W - C)‖ ≤
          ‖logDeriv (regularizedLFunction χ) s - W‖ + ‖W - C‖ :=
        norm_add_le _ _
      _ ≤ (20 * (Real.log 21600 +
            2 * Real.log (arithmeticScale q t)) + M) + 2 * M := by
        exact add_le_add (by simpa only [W, M, s] using hlocal) hmismatch
      _ = 20 * (Real.log 21600 +
            2 * Real.log (arithmeticScale q t)) + 3 * M := by ring
  have hmass : M ≤ 5520 * Real.log (arithmeticScale q t) := by
    simpa only [M] using wideZeroMultiplicity_mass_le_logScale χ hprim hχ t
  have hscale2 := two_le_arithmeticScale (q := q) t
  have hscale0 : 0 < arithmeticScale q t := by linarith
  have h21600 :
      Real.log 21600 ≤ 15 * Real.log (arithmeticScale q t) := by
    have hpow : (21600 : ℝ) ≤ arithmeticScale q t ^ (15 : ℕ) := by
      calc
        (21600 : ℝ) ≤ 2 ^ (15 : ℕ) := by norm_num
        _ ≤ arithmeticScale q t ^ (15 : ℕ) := by
          exact pow_le_pow_left₀ (by norm_num) hscale2 15
    calc
      Real.log 21600 ≤ Real.log (arithmeticScale q t ^ (15 : ℕ)) :=
        Real.log_le_log (by norm_num) hpow
      _ = 15 * Real.log (arithmeticScale q t) := by
        rw [Real.log_pow]
        norm_num
  have hlog0 : 0 ≤ Real.log (arithmeticScale q t) :=
    Real.log_nonneg (by linarith)
  exact hraw.trans (by nlinarith)

/-- Premise-free Koukoulopoulos Lemma 11.4(b) in the exact source-facing
uniform form introduced by `ZeroFreeSiegelSpine`. -/
theorem publishedUniformPrimitiveLogDerivativeRemainderBound :
    UniformPrimitiveLogDerivativeRemainderBound := by
  refine ⟨17000, by norm_num, ?_⟩
  intro q _inst χ hprim hχ u t hu hu2
  exact primitiveLogDerivativeRemainder_le χ hprim hχ hu hu2

end

end MAPPrimitiveLogDerivativeRemainderUnconditional

#print axioms MAPPrimitiveLogDerivativeRemainderUnconditional.two_le_arithmeticScale
#print axioms MAPPrimitiveLogDerivativeRemainderUnconditional.centeredUnitWindowSupport_subset_wideZeroSupport
#print axioms MAPPrimitiveLogDerivativeRemainderUnconditional.half_le_norm_sub_of_mem_wide_sdiff_centered
#print axioms MAPPrimitiveLogDerivativeRemainderUnconditional.wideZeroMultiplicity_mass_le_logScale
#print axioms MAPPrimitiveLogDerivativeRemainderUnconditional.primitiveLogDerivativeRemainder_le
#print axioms MAPPrimitiveLogDerivativeRemainderUnconditional.publishedUniformPrimitiveLogDerivativeRemainderBound
