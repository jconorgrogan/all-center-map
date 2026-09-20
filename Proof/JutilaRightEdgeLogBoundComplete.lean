import JutilaRightEdgeLogBound
import Mathlib.Analysis.PSeries

/-!
# Completion of the logarithmic right-edge bound

This file finishes the complex Abel argument prepared in
`JutilaRightEdgeLogBound`.  The cutoff is explicit and depends on both the
modulus and ordinate.  No epsilon-dependent implied constant is used.
-/

namespace MAPJutilaRightEdgeLogBoundComplete

open Complex Set LSeries Filter Topology
open scoped BigOperators
open MAPGoldfeldSiegel
open MAPJutilaRightEdgeLogBound

noncomputable section

/-- A nonzero term of the continued Dirichlet series is exactly the
oscillatory reciprocal weight times the character. -/
theorem LSeries_term_rightBoundaryPoint_eq
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (fun m : ℕ => chi m) (rightBoundaryPoint t) n =
      rightBoundaryWeight t n * chi (n : ZMod N) := by
  rw [LSeries.term_of_ne_zero hn]
  simp only [rightBoundaryWeight, if_neg hn]
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  ring

/-- Finite reciprocal-square tail in the exact index range produced by
summation by parts. -/
theorem sum_Ioc_inv_sq_le_inv {K M : ℕ}
    (hK : K ≠ 0) (hKM : K < M) :
    (∑ i ∈ Finset.Ioc K (M - 1), (((i : ℝ) ^ 2)⁻¹)) ≤
      (K : ℝ)⁻¹ := by
  exact (sum_Ioc_inv_sq_le_sub (α := ℝ) hK (by omega)).trans
    (sub_le_self _ (by positivity))

/-- The literal finite complex-Abel tail at `Re s = 1`. -/
theorem norm_rightBoundary_tail_finite
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (t : ℝ)
    {K M : ℕ} (hK : 1 ≤ K) (hKM : K < M) :
    ‖∑ n ∈ Finset.Ioc K M,
        rightBoundaryWeight t n * chi (n : ZMod N)‖ ≤
      (N : ℝ) *
        ((M : ℝ)⁻¹ + ((K + 1 : ℕ) : ℝ)⁻¹ +
          (1 + |t|) * (K : ℝ)⁻¹) := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hraw := norm_sum_Ioc_mul_le_of_complex_variation
    (fun n => chi (n : ZMod N)) (rightBoundaryWeight t)
    hKM hN0 (fun n => nonprincipal_initialSum_norm_le_level chi hchi n)
  have hM0 : M ≠ 0 := by omega
  have hK10 : K + 1 ≠ 0 := by omega
  have hendM := norm_rightBoundaryWeight (t := t) hM0
  have hendK := norm_rightBoundaryWeight (t := t) hK10
  have hvar :
      (∑ i ∈ Finset.Ioc K (M - 1),
          ‖rightBoundaryWeight t (i + 1) - rightBoundaryWeight t i‖) ≤
        (1 + |t|) * (K : ℝ)⁻¹ := by
    calc
      (∑ i ∈ Finset.Ioc K (M - 1),
          ‖rightBoundaryWeight t (i + 1) - rightBoundaryWeight t i‖) ≤
        ∑ i ∈ Finset.Ioc K (M - 1),
          (1 + |t|) * (((i : ℝ) ^ 2)⁻¹) := by
            apply Finset.sum_le_sum
            intro i hi
            exact norm_rightBoundaryWeight_succ_sub_le (by
              have := (Finset.mem_Ioc.mp hi).1
              omega)
      _ = (1 + |t|) *
          ∑ i ∈ Finset.Ioc K (M - 1), (((i : ℝ) ^ 2)⁻¹) := by
            rw [Finset.mul_sum]
      _ ≤ (1 + |t|) * (K : ℝ)⁻¹ := by
            exact mul_le_mul_of_nonneg_left
              (sum_Ioc_inv_sq_le_inv (show K ≠ 0 by omega) hKM)
              (by positivity)
  calc
    ‖∑ n ∈ Finset.Ioc K M,
        rightBoundaryWeight t n * chi (n : ZMod N)‖ ≤
      (N : ℝ) *
        (‖rightBoundaryWeight t M‖ +
          ‖rightBoundaryWeight t (K + 1)‖ +
          ∑ i ∈ Finset.Ioc K (M - 1),
            ‖rightBoundaryWeight t (i + 1) - rightBoundaryWeight t i‖) := hraw
    _ ≤ (N : ℝ) *
        ((M : ℝ)⁻¹ + ((K + 1 : ℕ) : ℝ)⁻¹ +
          (1 + |t|) * (K : ℝ)⁻¹) := by
      gcongr
      · exact hendM.le
      · exact hendK.le

/-- Complete-block partial sums of the oscillatory reciprocal series converge
at every point of the right boundary. -/
theorem tendsto_rightBoundaryWeight_sum_blocks
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (t : ℝ) :
    Tendsto
      (fun R : ℕ => ∑ n ∈ Finset.range (N * (R + 1)),
        rightBoundaryWeight t n * chi (n : ZMod N))
      atTop (nhds (DirichletCharacter.LFunction chi
        (rightBoundaryPoint t))) := by
  let s : ℂ := rightBoundaryPoint t
  let B : ℝ := 1 + |t|
  have hsre : s.re = 1 := rightBoundaryPoint_re t
  have hB : ‖s‖ ≤ B := norm_rightBoundaryPoint_le t
  have hmajor := summable_centeredBlockMajorant
    (N := N) (a := (1 : ℝ)) (B := B) (by norm_num)
  have hnorm : Summable (fun m : ℕ => ‖centeredCharacterLBlock chi m s‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => norm_centeredCharacterLBlock_le chi
        (a := (1 : ℝ)) (B := B) (by norm_num)
        (by dsimp [s]; rw [rightBoundaryPoint_re]) hB m) hmajor
  have hsum : Summable (fun m : ℕ => centeredCharacterLBlock chi m s) :=
    summable_norm_iff.mp hnorm
  have ht : Tendsto
      (fun R : ℕ => characterLBlock chi 0 s +
        ∑ m ∈ Finset.range R, centeredCharacterLBlock chi m s)
      atTop (nhds (characterLBlock chi 0 s +
        ∑' m : ℕ, centeredCharacterLBlock chi m s)) :=
    tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat
  have hfinite : ∀ R : ℕ,
      characterLBlock chi 0 s +
          ∑ m ∈ Finset.range R, centeredCharacterLBlock chi m s =
        ∑ n ∈ Finset.range (N * (R + 1)),
          LSeries.term (fun n : ℕ => chi n) s n := by
    intro R
    calc
      characterLBlock chi 0 s +
          ∑ m ∈ Finset.range R, centeredCharacterLBlock chi m s =
        characterLBlock chi 0 s +
          ∑ m ∈ Finset.range R, characterLBlock chi (m + 1) s := by
            congr 1
            apply Finset.sum_congr rfl
            intro m hm
            exact centeredCharacterLBlock_eq chi hchi m s
      _ = ∑ m ∈ Finset.range (R + 1), characterLBlock chi m s := by
        rw [Finset.sum_range_succ']
        ring
      _ = ∑ n ∈ Finset.range (N * (R + 1)),
          LSeries.term (fun n : ℕ => chi n) s n := by
        simpa [characterLBlock] using
          (sum_range_mul_eq_sum_blocks (N := N)
            (fun n => LSeries.term (fun n : ℕ => chi n) s n) (R + 1))
  have htBlocks : Tendsto
      (fun R : ℕ => ∑ n ∈ Finset.range (N * (R + 1)),
        LSeries.term (fun n : ℕ => chi n) s n)
      atTop (nhds (conditionalCharacterLSeries chi s)) := by
    have h := ht.congr' (Filter.Eventually.of_forall fun R => hfinite R)
    simpa [conditionalCharacterLSeries] using h
  have hident := conditionalCharacterLSeries_eq_LFunction_of_pos_re
    chi hchi (s := s) (by simp [s, rightBoundaryPoint])
  rw [hident] at htBlocks
  apply htBlocks.congr'
  exact Filter.Eventually.of_forall fun R => by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [rightBoundaryWeight]
    · exact LSeries_term_rightBoundaryPoint_eq chi t hn0

/-- The norm of the initial segment is bounded by its ordinary harmonic
majorant; the phase costs nothing. -/
theorem norm_rightBoundary_initialSum_le
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (t : ℝ) (K : ℕ) :
    ‖∑ n ∈ Finset.range (K + 1),
        rightBoundaryWeight t n * chi (n : ZMod N)‖ ≤
      1 + Real.log (K : ℝ) := by
  have hsum :
      ‖∑ n ∈ Finset.range (K + 1),
          rightBoundaryWeight t n * chi (n : ZMod N)‖ ≤
        ∑ n ∈ Finset.Icc 1 K, ((n : ℝ)⁻¹) := by
    calc
      ‖∑ n ∈ Finset.range (K + 1),
          rightBoundaryWeight t n * chi (n : ZMod N)‖ ≤
        ∑ n ∈ Finset.range (K + 1),
          ‖rightBoundaryWeight t n * chi (n : ZMod N)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 K, ((n : ℝ)⁻¹) := by
        rw [show Finset.range (K + 1) = {0} ∪ Finset.Icc 1 K by
          ext n
          simp
          omega]
        rw [Finset.sum_union]
        · simp only [Finset.sum_singleton]
          have hzero :
              ‖rightBoundaryWeight t 0 * chi ((0 : ℕ) : ZMod N)‖ = 0 := by
            simp [rightBoundaryWeight]
          rw [hzero, zero_add]
          apply Finset.sum_le_sum
          intro n hn
          have hn1 := (Finset.mem_Icc.mp hn).1
          have hn0 : n ≠ 0 := by omega
          rw [norm_mul, norm_rightBoundaryWeight hn0]
          simpa using mul_le_mul_of_nonneg_left (chi.norm_le_one n)
            (inv_nonneg.mpr (Nat.cast_nonneg n))
        · simp
  calc
    ‖∑ n ∈ Finset.range (K + 1),
        rightBoundaryWeight t n * chi (n : ZMod N)‖ ≤ _ := hsum
    _ = ((harmonic K : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      norm_num
    _ ≤ 1 + Real.log (K : ℝ) := harmonic_le_one_add_log K

/-- Explicit logarithmic bound on the line `Re s = 1`.  The cutoff is
`N * ceil(1+|t|)`, so all dependence is visible and polynomially harmless. -/
theorem norm_LFunction_rightBoundary_le
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (t : ℝ) :
    let K := N * Nat.ceil (1 + |t|)
    ‖DirichletCharacter.LFunction chi (rightBoundaryPoint t)‖ ≤
      4 + Real.log (K : ℝ) := by
  dsimp only
  let K : ℕ := N * Nat.ceil (1 + |t|)
  let L : ℂ := DirichletCharacter.LFunction chi (rightBoundaryPoint t)
  let I : ℂ := ∑ n ∈ Finset.range (K + 1),
    rightBoundaryWeight t n * chi (n : ZMod N)
  have hceil : 1 ≤ Nat.ceil (1 + |t|) := by
    apply Nat.one_le_iff_ne_zero.mpr
    exact ne_of_gt (Nat.ceil_pos.mpr (by positivity))
  have hK : 1 ≤ K := by
    dsimp [K]
    have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (NeZero.ne N) (Nat.ne_of_gt hceil))
  have htotal := tendsto_rightBoundaryWeight_sum_blocks chi hchi t
  change Tendsto (fun R : ℕ => ∑ n ∈ Finset.range (N * (R + 1)),
      rightBoundaryWeight t n * chi (n : ZMod N)) atTop (nhds L) at htotal
  have hsub : Tendsto
      (fun R : ℕ =>
        (∑ n ∈ Finset.range (N * (R + 1)),
          rightBoundaryWeight t n * chi (n : ZMod N)) - I)
      atTop (nhds (L - I)) := htotal.sub tendsto_const_nhds
  have heq :
      (fun R : ℕ =>
        (∑ n ∈ Finset.range (N * (R + 1)),
          rightBoundaryWeight t n * chi (n : ZMod N)) - I) =ᶠ[atTop]
      (fun R : ℕ => ∑ n ∈ Finset.Ioc K (N * (R + 1) - 1),
        rightBoundaryWeight t n * chi (n : ZMod N)) := by
    filter_upwards [eventually_gt_atTop K] with R hR
    let E : ℕ := N * (R + 1)
    have hKE : K + 1 ≤ E := by
      dsimp [E]
      have hNpos : 0 < N := NeZero.pos N
      have hscale : R + 1 ≤ N * (R + 1) :=
        Nat.le_mul_of_pos_left (R + 1) hNpos
      omega
    have hset : Finset.Ioc K (E - 1) = Finset.Ico (K + 1) E := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [hset]
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun n => rightBoundaryWeight t n * chi (n : ZMod N)) hKE
    dsimp [I, E]
    rw [← hsplit]
    ring
  have htail : Tendsto
      (fun R : ℕ => ∑ n ∈ Finset.Ioc K (N * (R + 1) - 1),
        rightBoundaryWeight t n * chi (n : ZMod N))
      atTop (nhds (L - I)) := hsub.congr' heq
  have htailBound : ‖L - I‖ ≤ 3 := by
    apply le_of_tendsto htail.norm
    filter_upwards [eventually_gt_atTop K] with R hR
    let M : ℕ := N * (R + 1) - 1
    have hKM : K < M := by
      have hNpos : 0 < N := NeZero.pos N
      have hscale : R + 1 ≤ N * (R + 1) :=
        Nat.le_mul_of_pos_left (R + 1) hNpos
      dsimp [M]
      omega
    have hraw := norm_rightBoundary_tail_finite chi hchi t hK hKM
    have hNreal : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
    have hKreal : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
    have hNK : (N : ℝ) ≤ K := by
      exact_mod_cast (show N ≤ K by dsimp [K]; nlinarith)
    have hcut : (N : ℝ) * (1 + |t|) ≤ K := by
      dsimp [K]
      have hc : 1 + |t| ≤ (Nat.ceil (1 + |t|) : ℝ) := Nat.le_ceil _
      simpa only [Nat.cast_mul] using
        mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg N)
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hMge : (K : ℝ) ≤ M := by exact_mod_cast (show K ≤ M by omega)
    have hfirst : (N : ℝ) * (M : ℝ)⁻¹ ≤ 1 := by
      simpa [div_eq_mul_inv] using
        ((div_le_one hMpos).2 (hNK.trans hMge))
    have hsecond : (N : ℝ) * ((K + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
      have hden : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
      have hle : (N : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
        exact hNK.trans (by norm_num)
      simpa [div_eq_mul_inv] using ((div_le_one hden).2 hle)
    have hthird : (N : ℝ) * ((1 + |t|) * (K : ℝ)⁻¹) ≤ 1 := by
      calc
        (N : ℝ) * ((1 + |t|) * (K : ℝ)⁻¹) =
            ((N : ℝ) * (1 + |t|)) / (K : ℝ) := by
              rw [div_eq_mul_inv]
              ring
        _ ≤ 1 := (div_le_one hKreal).2 hcut
    calc
      ‖∑ n ∈ Finset.Ioc K M,
          rightBoundaryWeight t n * chi (n : ZMod N)‖ ≤
        (N : ℝ) * ((M : ℝ)⁻¹ + ((K + 1 : ℕ) : ℝ)⁻¹ +
          (1 + |t|) * (K : ℝ)⁻¹) := hraw
      _ = (N : ℝ) * (M : ℝ)⁻¹ +
          (N : ℝ) * ((K + 1 : ℕ) : ℝ)⁻¹ +
          (N : ℝ) * ((1 + |t|) * (K : ℝ)⁻¹) := by ring
      _ ≤ 3 := by linarith
  have hinit := norm_rightBoundary_initialSum_le chi t K
  have htriangle : ‖L‖ ≤ ‖I‖ + ‖L - I‖ := by
    calc
      ‖L‖ = ‖I + (L - I)‖ := by congr 1 <;> ring
      _ ≤ ‖I‖ + ‖L - I‖ := norm_add_le _ _
  exact htriangle.trans (by
    change ‖I‖ ≤ 1 + Real.log (K : ℝ) at hinit
    linarith)

/-- Ceiling-free form of the right-boundary logarithmic estimate.  This is
the form used by the detector: the constant is absolute, and the only growth
is logarithmic in the conductor and ordinate. -/
theorem norm_LFunction_rightBoundary_le_clean
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (t : ℝ) :
    ‖DirichletCharacter.LFunction chi (rightBoundaryPoint t)‖ ≤
      4 + Real.log ((N : ℝ) * (2 + |t|)) := by
  let K : ℕ := N * Nat.ceil (1 + |t|)
  have hraw := norm_LFunction_rightBoundary_le chi hchi t
  change ‖DirichletCharacter.LFunction chi (rightBoundaryPoint t)‖ ≤
    4 + Real.log (K : ℝ) at hraw
  have hceil : (Nat.ceil (1 + |t|) : ℝ) ≤ 2 + |t| := by
    have hlt := Nat.ceil_lt_add_one (show 0 ≤ 1 + |t| by positivity)
    linarith
  have hupper : (K : ℝ) ≤ (N : ℝ) * (2 + |t|) := by
    dsimp [K]
    push_cast
    exact mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg N)
  have hKpos : (0 : ℝ) < K := by
    exact_mod_cast (Nat.mul_pos (NeZero.pos N)
      (Nat.ceil_pos.mpr (show 0 < 1 + |t| by positivity)))
  have htargetPos : (0 : ℝ) < (N : ℝ) * (2 + |t|) := by
    exact mul_pos (by exact_mod_cast NeZero.pos N) (by positivity)
  have hlog : Real.log (K : ℝ) ≤
      Real.log ((N : ℝ) * (2 + |t|)) :=
    Real.strictMonoOn_log.monotoneOn hKpos htargetPos hupper
  exact hraw.trans (by linarith)

end
end MAPJutilaRightEdgeLogBoundComplete

#print axioms MAPJutilaRightEdgeLogBoundComplete.norm_LFunction_rightBoundary_le
#print axioms MAPJutilaRightEdgeLogBoundComplete.norm_LFunction_rightBoundary_le_clean
