import UniformPsiDeterministicBridge
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Perron remainders at the paper right edge

This file keeps the manuscript right edge
`c = 1 + 1 / log (halfIntegerPoint N)`.  All estimates are deterministic
consequences of the canonical sharp Perron kernel bounds.
-/

namespace PaperEdgePerronRemainder

open scoped BigOperators ArithmeticFunction
open PrimitiveExplicitFormulaSpine PrimitiveTruncatedExplicitFormulaBridge
open TruncatedTwistedPerron

noncomputable section

/-- At the standard Perron edge, the small extra real power costs at most
`exp 1`. -/
theorem rpow_standardEdge_le
    {x y : ℝ} (hx : 1 < x) (hy0 : 0 < y) (hy1 : y ≤ x) :
    y ^ (1 + (Real.log x)⁻¹) ≤ Real.exp 1 * y := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  rw [Real.rpow_add hy0 1 (Real.log x)⁻¹, Real.rpow_one]
  calc
    y * y ^ (Real.log x)⁻¹ ≤ y * x ^ (Real.log x)⁻¹ := by
      gcongr
    _ = Real.exp 1 * y := by
      rw [Real.rpow_inv_log (lt_trans zero_lt_one hx) hx.ne']
      ring

/-- Inside the half-integer endpoint, the logarithmic denominator is bounded
by the exact arithmetic distance to the endpoint. -/
theorem one_div_abs_log_halfInteger_inside_le
    {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    1 / |Real.log (halfIntegerPoint N / (n : ℝ))| ≤
      halfIntegerPoint N / (halfIntegerPoint N - (n : ℝ)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hxpos : 0 < halfIntegerPoint N := halfIntegerPoint_pos N
  have hnle : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hnltx : (n : ℝ) < halfIntegerPoint N := by
    unfold halfIntegerPoint
    linarith
  have hfrac : 0 < (halfIntegerPoint N - (n : ℝ)) / halfIntegerPoint N :=
    div_pos (sub_pos.mpr hnltx) hxpos
  have hlog := PerronKernel.abs_log_div_ge_abs_sub_div_max hxpos hnpos
  rw [max_eq_left hnltx.le, abs_of_pos (sub_pos.mpr hnltx)] at hlog
  calc
    1 / |Real.log (halfIntegerPoint N / (n : ℝ))| ≤
        1 / ((halfIntegerPoint N - (n : ℝ)) / halfIntegerPoint N) :=
      one_div_le_one_div_of_le hfrac hlog
    _ = halfIntegerPoint N / (halfIntegerPoint N - (n : ℝ)) := by
      field_simp [(sub_pos.mpr hnltx).ne', hxpos.ne']

/-- Pointwise inside-kernel majorant at the paper edge.  Its right side is
already in partial-fraction harmonic form. -/
theorem insideKernelSummand_standardEdge_le
    (N n : ℕ) {T : ℝ} (hN : 1 ≤ N) (hT : 0 < T)
    (hn : n ∈ Finset.Icc 1 N) :
    ArithmeticFunction.vonMangoldt n *
        ((halfIntegerPoint N / n) ^
            (1 + (Real.log (halfIntegerPoint N))⁻¹) /
          (Real.pi * T *
            |Real.log (halfIntegerPoint N / n)|)) ≤
      (Real.exp 1 * halfIntegerPoint N *
          Real.log (halfIntegerPoint N) / (Real.pi * T)) *
        (1 / (n : ℝ) +
          1 / (halfIntegerPoint N - (n : ℝ))) := by
  let x := halfIntegerPoint N
  have hxpos : 0 < x := halfIntegerPoint_pos N
  have hxone : 1 < x := by
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp only [x, halfIntegerPoint]
    linarith
  have hnmem := Finset.mem_Icc.mp hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnmem.1
  have hnle : (n : ℝ) ≤ N := by exact_mod_cast hnmem.2
  have hnltx : (n : ℝ) < x := by
    dsimp only [x, halfIntegerPoint]
    linarith
  have hypos : 0 < x / (n : ℝ) := div_pos hxpos hnpos
  have hyx : x / (n : ℝ) ≤ x := by
    rw [div_le_iff₀ hnpos]
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hnmem.1]
  have hrpow :
      (x / (n : ℝ)) ^ (1 + (Real.log x)⁻¹) ≤
        Real.exp 1 * (x / (n : ℝ)) :=
    rpow_standardEdge_le hxone hypos hyx
  have hloginv :
      1 / |Real.log (x / (n : ℝ))| ≤ x / (x - (n : ℝ)) := by
    simpa only [x] using one_div_abs_log_halfInteger_inside_le hn
  have hvm : ArithmeticFunction.vonMangoldt n ≤ Real.log x := by
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hnpos hnltx.le)
  have hlog0 : 0 ≤ Real.log x := (Real.log_pos hxone).le
  have hdist : 0 < x - (n : ℝ) := sub_pos.mpr hnltx
  have hden : 0 < Real.pi * T := mul_pos Real.pi_pos hT
  have hnum :
      ArithmeticFunction.vonMangoldt n *
          (x / (n : ℝ)) ^ (1 + (Real.log x)⁻¹) *
            (1 / |Real.log (x / (n : ℝ))|) ≤
        Real.log x * (Real.exp 1 * (x / (n : ℝ))) *
          (x / (x - (n : ℝ))) := by
    gcongr
  dsimp only [x] at *
  calc
    ArithmeticFunction.vonMangoldt n *
        ((halfIntegerPoint N / n) ^
            (1 + (Real.log (halfIntegerPoint N))⁻¹) /
          (Real.pi * T *
            |Real.log (halfIntegerPoint N / n)|)) =
        (ArithmeticFunction.vonMangoldt n *
          (halfIntegerPoint N / (n : ℝ)) ^
            (1 + (Real.log (halfIntegerPoint N))⁻¹) *
          (1 / |Real.log (halfIntegerPoint N / (n : ℝ))|)) /
            (Real.pi * T) := by ring
    _ ≤ (Real.log (halfIntegerPoint N) *
          (Real.exp 1 * (halfIntegerPoint N / (n : ℝ))) *
          (halfIntegerPoint N /
            (halfIntegerPoint N - (n : ℝ)))) /
          (Real.pi * T) := div_le_div_of_nonneg_right hnum hden.le
    _ = (Real.exp 1 * halfIntegerPoint N *
          Real.log (halfIntegerPoint N) / (Real.pi * T)) *
        (1 / (n : ℝ) +
          1 / (halfIntegerPoint N - (n : ℝ))) := by
      field_simp [hnpos.ne', hdist.ne', hden.ne']
      ring

/-- Exact harmonic-form estimate for the entire finite inside-kernel error at
the paper edge.  The displayed sum is bounded by three harmonic numbers by
the involution `n ↦ N + 1 - n`. -/
theorem norm_insideKernelError_standardEdge_le_harmonicSum
    {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) {T : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) :
    ‖insideKernelError χ N
        (1 + (Real.log (halfIntegerPoint N))⁻¹) T‖ ≤
      (Real.exp 1 * halfIntegerPoint N *
          Real.log (halfIntegerPoint N) / (Real.pi * T)) *
        ∑ n ∈ Finset.Icc 1 N,
          (1 / (n : ℝ) +
            1 / (halfIntegerPoint N - (n : ℝ))) := by
  have hc : 0 < 1 + (Real.log (halfIntegerPoint N))⁻¹ := by
    have hxone : 1 < halfIntegerPoint N := by
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
      unfold halfIntegerPoint
      linarith
    have hinv : 0 < (Real.log (halfIntegerPoint N))⁻¹ :=
      inv_pos.mpr (Real.log_pos hxone)
    linarith
  refine (SharpPerronRemainderBridge.norm_insideKernelError_le_sharp
    χ N hc hT).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun n hn =>
    insideKernelSummand_standardEdge_le N n hN hT hn

/-- Real-valued form of the canonical harmonic-number identity. -/
theorem sum_Icc_one_div_eq_harmonic (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)) =
      ((harmonic N : ℚ) : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp only [one_div]

/-- Reversing the finite interval preserves its reciprocal harmonic sum. -/
theorem sum_Icc_reverse_one_div_eq_harmonic (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, 1 / ((N + 1 - n : ℕ) : ℝ)) =
      ((harmonic N : ℚ) : ℝ) := by
  rw [← sum_Icc_one_div_eq_harmonic N]
  apply Finset.sum_bij (fun n _ => N + 1 - n)
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_Icc] at ha hb
    omega
  · intro b hb
    refine ⟨N + 1 - b, ?_, ?_⟩
    · simp only [Finset.mem_Icc] at hb ⊢
      omega
    · simp only [Finset.mem_Icc] at hb
      omega
  · intro n hn
    rfl

/-- The reciprocal distance on the inside of a half-integer endpoint is at
most twice the reversed ordinary harmonic summand. -/
theorem one_div_halfInteger_sub_nat_le_reverse_harmonic
    {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    1 / (halfIntegerPoint N - (n : ℝ)) ≤
      2 / ((N + 1 - n : ℕ) : ℝ) := by
  have hnmem := Finset.mem_Icc.mp hn
  have hnle : n ≤ N + 1 := hnmem.2.trans (Nat.le_succ N)
  have hkposNat : 0 < N + 1 - n := by omega
  have hkpos : 0 < ((N + 1 - n : ℕ) : ℝ) := by exact_mod_cast hkposNat
  have hkcast : ((N + 1 - n : ℕ) : ℝ) =
      (N : ℝ) + 1 - (n : ℝ) := by
    rw [Nat.cast_sub hnle]
    norm_num
  have hhalf : ((N + 1 - n : ℕ) : ℝ) / 2 ≤
      halfIntegerPoint N - (n : ℝ) := by
    have hnleReal : (n : ℝ) ≤ N := by exact_mod_cast hnmem.2
    rw [hkcast]
    unfold halfIntegerPoint
    nlinarith
  calc
    1 / (halfIntegerPoint N - (n : ℝ)) ≤
        1 / (((N + 1 - n : ℕ) : ℝ) / 2) :=
      one_div_le_one_div_of_le (div_pos hkpos (by norm_num)) hhalf
    _ = 2 / ((N + 1 - n : ℕ) : ℝ) := by
      field_simp [hkpos.ne']

/-- The exact half-integer harmonic sum costs at most three ordinary harmonic
numbers. -/
theorem halfInteger_inside_harmonicSum_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      (1 / (n : ℝ) +
        1 / (halfIntegerPoint N - (n : ℝ)))) ≤
      3 * ((harmonic N : ℚ) : ℝ) := by
  rw [Finset.sum_add_distrib]
  have hreverse :
      (∑ n ∈ Finset.Icc 1 N,
        1 / (halfIntegerPoint N - (n : ℝ))) ≤
      ∑ n ∈ Finset.Icc 1 N,
        2 / ((N + 1 - n : ℕ) : ℝ) :=
    Finset.sum_le_sum fun n hn =>
      one_div_halfInteger_sub_nat_le_reverse_harmonic hn
  have hrhs :
      (∑ n ∈ Finset.Icc 1 N,
        2 / ((N + 1 - n : ℕ) : ℝ)) =
          2 * ((harmonic N : ℚ) : ℝ) := by
    calc
      (∑ n ∈ Finset.Icc 1 N,
        2 / ((N + 1 - n : ℕ) : ℝ)) =
          2 * ∑ n ∈ Finset.Icc 1 N,
            1 / ((N + 1 - n : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ = 2 * ((harmonic N : ℚ) : ℝ) := by
        rw [sum_Icc_reverse_one_div_eq_harmonic]
  rw [hrhs] at hreverse
  rw [sum_Icc_one_div_eq_harmonic]
  linarith

/-- Closed harmonic-number form of the paper-edge inside Perron remainder. -/
theorem norm_insideKernelError_standardEdge_le_harmonic
    {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) {T : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) :
    ‖insideKernelError χ N
        (1 + (Real.log (halfIntegerPoint N))⁻¹) T‖ ≤
      (3 * Real.exp 1 * halfIntegerPoint N *
        Real.log (halfIntegerPoint N) / (Real.pi * T)) *
          ((harmonic N : ℚ) : ℝ) := by
  have hbase := norm_insideKernelError_standardEdge_le_harmonicSum
    χ N hN hT
  have hfactor :
      0 ≤ Real.exp 1 * halfIntegerPoint N *
        Real.log (halfIntegerPoint N) / (Real.pi * T) := by
    have hxone : 1 < halfIntegerPoint N := by
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
      unfold halfIntegerPoint
      linarith
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (Real.exp_pos 1).le (halfIntegerPoint_pos N).le)
        (Real.log_pos hxone).le)
      (mul_pos Real.pi_pos hT).le
  refine hbase.trans ?_
  calc
    (Real.exp 1 * halfIntegerPoint N *
        Real.log (halfIntegerPoint N) / (Real.pi * T)) *
      ∑ n ∈ Finset.Icc 1 N,
        (1 / (n : ℝ) +
          1 / (halfIntegerPoint N - (n : ℝ))) ≤
      (Real.exp 1 * halfIntegerPoint N *
        Real.log (halfIntegerPoint N) / (Real.pi * T)) *
          (3 * ((harmonic N : ℚ) : ℝ)) := by
      gcongr
      exact halfInteger_inside_harmonicSum_le N
    _ = (3 * Real.exp 1 * halfIntegerPoint N *
        Real.log (halfIntegerPoint N) / (Real.pi * T)) *
          ((harmonic N : ℚ) : ℝ) := by ring

/-- Logarithmic closed form of the paper-edge inside Perron remainder. -/
theorem norm_insideKernelError_standardEdge_le_log
    {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) {T : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) :
    ‖insideKernelError χ N
        (1 + (Real.log (halfIntegerPoint N))⁻¹) T‖ ≤
      (3 * Real.exp 1 * halfIntegerPoint N *
        Real.log (halfIntegerPoint N) / (Real.pi * T)) *
          (1 + Real.log N) := by
  have hbase := norm_insideKernelError_standardEdge_le_harmonic χ N hN hT
  have hfactor :
      0 ≤ 3 * Real.exp 1 * halfIntegerPoint N *
        Real.log (halfIntegerPoint N) / (Real.pi * T) := by
    have hxone : 1 < halfIntegerPoint N := by
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
      unfold halfIntegerPoint
      linarith
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (Real.exp_pos 1).le)
          (halfIntegerPoint_pos N).le)
        (Real.log_pos hxone).le)
      (mul_pos Real.pi_pos hT).le
  exact hbase.trans (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) hfactor)

/-- The exact manuscript height `T = X^(13/15 - epsilon/2)`, inserted into
the standard-edge inside Perron estimate.  No restriction on the exponent is
needed for positivity of the height. -/
theorem norm_insideKernelError_paperHeight_le_log
    {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ)
    {X epsilon : ℝ} (hN : 1 ≤ N) (hX : 0 < X) :
    ‖insideKernelError χ N
        (1 + (Real.log (halfIntegerPoint N))⁻¹)
        (X ^ (13 / 15 - epsilon / 2))‖ ≤
      (3 * Real.exp 1 * halfIntegerPoint N *
        Real.log (halfIntegerPoint N) /
          (Real.pi * X ^ (13 / 15 - epsilon / 2))) *
            (1 + Real.log N) := by
  exact norm_insideKernelError_standardEdge_le_log χ N hN
    (Real.rpow_pos_of_pos hX _)

end

end PaperEdgePerronRemainder
