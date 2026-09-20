import GoldfeldConditionalDirichletContinuation
import GoldfeldLemma11TwoLValue
import Mathlib.Analysis.PSeries

/-!
# Logarithmic right-edge bound for Jutila's zero-shift detector

For a nonprincipal character, periodicity bounds every initial character
sum by the modulus.  Complex summation by parts against `n^(-1+it)`, followed
by the already certified complete-block continuation, gives the required
logarithmic bound on `Re s = 1`.
-/

namespace MAPJutilaRightEdgeLogBound

open Complex Set LSeries Filter Topology
open scoped BigOperators
open MAPGoldfeldSiegel

noncomputable section

/-- Finite Abel summation for an arbitrary complex weight, retaining the
total variation explicitly. -/
theorem norm_sum_Ioc_mul_le_of_complex_variation
    (c w : ℕ → ℂ) {K M : ℕ} {P : ℝ}
    (hKM : K < M) (hP : 0 ≤ P)
    (hpartial : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, c i‖ ≤ P) :
    ‖∑ n ∈ Finset.Ioc K M, w n * c n‖ ≤
      P * (‖w M‖ + ‖w (K + 1)‖ +
        ∑ i ∈ Finset.Ioc K (M - 1), ‖w (i + 1) - w i‖) := by
  have hparts := Finset.sum_Ioc_by_parts w c hKM
  simp only [smul_eq_mul] at hparts
  rw [hparts]
  calc
    ‖w M * (∑ i ∈ Finset.range (M + 1), c i) -
        w (K + 1) * (∑ i ∈ Finset.range (K + 1), c i) -
        ∑ i ∈ Finset.Ioc K (M - 1),
          (w (i + 1) - w i) *
            ∑ j ∈ Finset.range (i + 1), c j‖ ≤
      ‖w M * (∑ i ∈ Finset.range (M + 1), c i)‖ +
        ‖w (K + 1) * (∑ i ∈ Finset.range (K + 1), c i)‖ +
        ‖∑ i ∈ Finset.Ioc K (M - 1),
          (w (i + 1) - w i) *
            ∑ j ∈ Finset.range (i + 1), c j‖ := by
      exact (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ ‖w M‖ * P + ‖w (K + 1)‖ * P +
        ∑ i ∈ Finset.Ioc K (M - 1), ‖w (i + 1) - w i‖ * P := by
      gcongr
      · simpa [norm_mul] using
          mul_le_mul_of_nonneg_left (hpartial (M + 1)) (norm_nonneg (w M))
      · simpa [norm_mul] using
          mul_le_mul_of_nonneg_left (hpartial (K + 1)) (norm_nonneg (w (K + 1)))
      · calc
          ‖∑ i ∈ Finset.Ioc K (M - 1),
              (w (i + 1) - w i) *
                ∑ j ∈ Finset.range (i + 1), c j‖ ≤
            ∑ i ∈ Finset.Ioc K (M - 1),
              ‖(w (i + 1) - w i) *
                ∑ j ∈ Finset.range (i + 1), c j‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.Ioc K (M - 1),
              ‖w (i + 1) - w i‖ * P := by
            apply Finset.sum_le_sum
            intro i hi
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hpartial (i + 1))
              (norm_nonneg _)
    _ = P * (‖w M‖ + ‖w (K + 1)‖ +
        ∑ i ∈ Finset.Ioc K (M - 1), ‖w (i + 1) - w i‖) := by
      rw [← Finset.sum_mul]
      ring

/-- The point on the right boundary paired with `it` by the functional
equation. -/
def rightBoundaryPoint (t : ℝ) : ℂ := 1 - (t : ℂ) * I

def rightBoundaryWeight (t : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else (n : ℂ) ^ (-rightBoundaryPoint t)

theorem rightBoundaryPoint_re (t : ℝ) : (rightBoundaryPoint t).re = 1 := by
  simp [rightBoundaryPoint]

theorem norm_rightBoundaryPoint_le (t : ℝ) :
    ‖rightBoundaryPoint t‖ ≤ 1 + |t| := by
  rw [Complex.norm_def]
  rw [Complex.normSq_apply]
  simp only [rightBoundaryPoint]
  norm_num
  have hsqrt : Real.sqrt (1 + t ^ 2) ≤ 1 + |t| := by
    rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)]
    rw [Real.sq_sqrt (by positivity)]
    nlinarith [abs_nonneg t, sq_abs t]
  simpa [pow_two] using hsqrt

theorem norm_rightBoundaryWeight {t : ℝ} {n : ℕ} (hn : n ≠ 0) :
    ‖rightBoundaryWeight t n‖ = (n : ℝ)⁻¹ := by
  rw [rightBoundaryWeight, if_neg hn,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  rw [neg_re, rightBoundaryPoint_re, Real.rpow_neg_one]

/-- One-step variation of the oscillatory reciprocal weight. -/
theorem norm_rightBoundaryWeight_succ_sub_le
    {t : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    ‖rightBoundaryWeight t (n + 1) - rightBoundaryWeight t n‖ ≤
      (1 + |t|) * (((n : ℝ) ^ 2)⁻¹) := by
  have hn0 : n ≠ 0 := by omega
  have hsucc0 : n + 1 ≠ 0 := by omega
  simp only [rightBoundaryWeight, if_neg hsucc0, if_neg hn0]
  have h := norm_cpow_neg_sub_cpow_neg_le
    (a := (1 : ℝ)) (B := 1 + |t|) (s := rightBoundaryPoint t)
    (by norm_num) (by simp [rightBoundaryPoint])
    (norm_rightBoundaryPoint_le t)
    (by exact_mod_cast hn) (by norm_num : (n : ℝ) ≤ n + 1)
  rw [norm_sub_rev]
  have h' := h
  norm_num at h'
  simpa [Nat.cast_add, Nat.cast_one] using h'

/-- The reciprocal-square total variation remaining after a positive cutoff. -/
theorem sum_Ioc_inv_sq_le_inv {K M : ℕ} (hK : K ≠ 0) (hKM : K < M) :
    (∑ i ∈ Finset.Ioc K (M - 1), (((i : ℝ) ^ 2)⁻¹)) ≤ (K : ℝ)⁻¹ := by
  exact (sum_Ioc_inv_sq_le_sub (α := ℝ) hK (by omega)).trans
    (sub_le_self _ (by positivity))

/-- At the right-boundary point, an `LSeries` term is the oscillatory
reciprocal weight used in the finite Abel estimate. -/
theorem LSeries_term_rightBoundaryPoint_eq
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (t : ℝ) (n : ℕ) :
    LSeries.term (fun m : ℕ => chi m) (rightBoundaryPoint t) n =
      rightBoundaryWeight t n * chi (n : ZMod N) := by
  by_cases hn : n = 0
  · subst n
    simp [rightBoundaryWeight]
  · rw [LSeries.term_of_ne_zero hn]
    rw [div_eq_mul_inv, ← Complex.cpow_neg]
    simp only [rightBoundaryWeight, if_neg hn]
    ring

/-- The centered complete blocks are summable at every point of the line
`Re s = 1`, with a majorant uniform enough for the right-edge estimate. -/
theorem summable_centeredCharacterLBlock_rightBoundary
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (t : ℝ) :
    Summable (fun m : ℕ =>
      centeredCharacterLBlock chi m (rightBoundaryPoint t)) := by
  have hmajor := summable_centeredBlockMajorant
    (N := N) (a := (1 / 2 : ℝ)) (B := (1 + |t| : ℝ)) (by norm_num)
  have hnorm : Summable (fun m : ℕ =>
      ‖centeredCharacterLBlock chi m (rightBoundaryPoint t)‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => by
        have h := norm_centeredCharacterLBlock_le chi
          (a := (1 / 2 : ℝ)) (B := (1 + |t| : ℝ)) (by norm_num)
          (s := rightBoundaryPoint t) (by rw [rightBoundaryPoint_re]; norm_num)
          (norm_rightBoundaryPoint_le t) m
        simpa using h)
      hmajor
  exact summable_norm_iff.mp hnorm

/-- Complete-block partial sums of the oscillatory right-boundary series
converge to the analytic Dirichlet `LFunction`. -/
theorem tendsto_rightBoundaryWeight_sum_blocks
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (t : ℝ) :
    Tendsto
      (fun R : ℕ => ∑ n ∈ Finset.range (N * (R + 1)),
        rightBoundaryWeight t n * chi (n : ZMod N))
      atTop (nhds (DirichletCharacter.LFunction chi (rightBoundaryPoint t))) := by
  have hsum := summable_centeredCharacterLBlock_rightBoundary chi t
  have ht : Tendsto
      (fun R : ℕ => characterLBlock chi 0 (rightBoundaryPoint t) +
        ∑ m ∈ Finset.range R,
          centeredCharacterLBlock chi m (rightBoundaryPoint t))
      atTop (nhds (characterLBlock chi 0 (rightBoundaryPoint t) +
        ∑' m : ℕ, centeredCharacterLBlock chi m (rightBoundaryPoint t))) :=
    tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat
  have hfinite : ∀ R : ℕ,
      characterLBlock chi 0 (rightBoundaryPoint t) +
          ∑ m ∈ Finset.range R,
            centeredCharacterLBlock chi m (rightBoundaryPoint t) =
        ∑ n ∈ Finset.range (N * (R + 1)),
          LSeries.term (fun n : ℕ => chi n) (rightBoundaryPoint t) n := by
    intro R
    calc
      characterLBlock chi 0 (rightBoundaryPoint t) +
          ∑ m ∈ Finset.range R,
            centeredCharacterLBlock chi m (rightBoundaryPoint t) =
          characterLBlock chi 0 (rightBoundaryPoint t) +
            ∑ m ∈ Finset.range R,
              characterLBlock chi (m + 1) (rightBoundaryPoint t) := by
        congr 1
        apply Finset.sum_congr rfl
        intro m hm
        exact centeredCharacterLBlock_eq chi hchi m (rightBoundaryPoint t)
      _ = ∑ m ∈ Finset.range (R + 1),
          characterLBlock chi m (rightBoundaryPoint t) := by
        rw [Finset.sum_range_succ']
        ring
      _ = ∑ n ∈ Finset.range (N * (R + 1)),
          LSeries.term (fun n : ℕ => chi n) (rightBoundaryPoint t) n := by
        simpa [characterLBlock] using
          (sum_range_mul_eq_sum_blocks (N := N)
            (fun n => LSeries.term (fun n : ℕ => chi n)
              (rightBoundaryPoint t) n) (R + 1))
  have htBlocks : Tendsto
      (fun R : ℕ => ∑ n ∈ Finset.range (N * (R + 1)),
        LSeries.term (fun n : ℕ => chi n) (rightBoundaryPoint t) n)
      atTop (nhds (conditionalCharacterLSeries chi (rightBoundaryPoint t))) := by
    have := ht.congr' (Filter.Eventually.of_forall fun R => hfinite R)
    simpa [conditionalCharacterLSeries] using this
  have hident := conditionalCharacterLSeries_eq_LFunction_of_pos_re
    chi hchi (s := rightBoundaryPoint t) (by simp [rightBoundaryPoint])
  rw [hident] at htBlocks
  apply htBlocks.congr'
  exact Filter.Eventually.of_forall fun R => by
    apply Finset.sum_congr rfl
    intro n hn
    exact LSeries_term_rightBoundaryPoint_eq chi t n

/-- Finite Abel tail on the line `Re s = 1`.  The deliberately simple
constant is sufficient once the cutoff is chosen proportional to
`N * (3 + |t|)`. -/
theorem nonprincipal_rightBoundary_tail_finite
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (t : ℝ) {K M : ℕ}
    (hK : 1 ≤ K) (hKM : K < M) :
    ‖∑ n ∈ Finset.Ioc K M,
        rightBoundaryWeight t n * chi (n : ZMod N)‖ ≤
      (N : ℝ) * (3 + |t|) * (K : ℝ)⁻¹ := by
  have hraw := norm_sum_Ioc_mul_le_of_complex_variation
    (c := fun n => chi (n : ZMod N))
    (w := rightBoundaryWeight t) (K := K) (M := M)
    (P := (N : ℝ)) hKM (by positivity)
    (fun n => nonprincipal_initialSum_norm_le_level chi hchi n)
  have hMpos : 0 < M := by omega
  have hKposR : (0 : ℝ) < K := by exact_mod_cast (Nat.zero_lt_of_lt hK)
  have hMnorm : ‖rightBoundaryWeight t M‖ ≤ (K : ℝ)⁻¹ := by
    rw [norm_rightBoundaryWeight (Nat.ne_of_gt hMpos)]
    exact (inv_le_inv₀ (by exact_mod_cast hMpos) hKposR).2 (by exact_mod_cast hKM.le)
  have hKsuccnorm : ‖rightBoundaryWeight t (K + 1)‖ ≤ (K : ℝ)⁻¹ := by
    rw [norm_rightBoundaryWeight (by omega : K + 1 ≠ 0)]
    exact (inv_le_inv₀ (by positivity) hKposR).2 (by norm_num)
  have hvariation :
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
          (∑ i ∈ Finset.Ioc K (M - 1), (((i : ℝ) ^ 2)⁻¹)) := by
        rw [Finset.mul_sum]
      _ ≤ (1 + |t|) * (K : ℝ)⁻¹ := by
        exact mul_le_mul_of_nonneg_left
          (sum_Ioc_inv_sq_le_inv (by omega) hKM) (by positivity)
  calc
    ‖∑ n ∈ Finset.Ioc K M,
        rightBoundaryWeight t n * chi (n : ZMod N)‖ ≤
      (N : ℝ) * (‖rightBoundaryWeight t M‖ +
        ‖rightBoundaryWeight t (K + 1)‖ +
        ∑ i ∈ Finset.Ioc K (M - 1),
          ‖rightBoundaryWeight t (i + 1) - rightBoundaryWeight t i‖) := hraw
    _ ≤ (N : ℝ) * ((K : ℝ)⁻¹ + (K : ℝ)⁻¹ +
        (1 + |t|) * (K : ℝ)⁻¹) := by
      gcongr
    _ = (N : ℝ) * (3 + |t|) * (K : ℝ)⁻¹ := by ring

/-- Exact right-boundary estimate before choosing the elementary cutoff. -/
theorem norm_LFunction_rightBoundary_le_initial_add_tail
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (t : ℝ) {K : ℕ} (hK : 1 ≤ K) :
    ‖DirichletCharacter.LFunction chi (rightBoundaryPoint t)‖ ≤
      ‖∑ n ∈ Finset.range (K + 1),
        rightBoundaryWeight t n * chi (n : ZMod N)‖ +
      (N : ℝ) * (3 + |t|) * (K : ℝ)⁻¹ := by
  let q : ℕ → ℂ := fun n =>
    rightBoundaryWeight t n * chi (n : ZMod N)
  let L : ℂ := DirichletCharacter.LFunction chi (rightBoundaryPoint t)
  let I : ℂ := ∑ n ∈ Finset.range (K + 1), q n
  have htotal := tendsto_rightBoundaryWeight_sum_blocks chi hchi t
  change Tendsto (fun R : ℕ => ∑ n ∈ Finset.range (N * (R + 1)), q n)
    atTop (nhds L) at htotal
  have hsub : Tendsto
      (fun R : ℕ => (∑ n ∈ Finset.range (N * (R + 1)), q n) - I)
      atTop (nhds (L - I)) := htotal.sub tendsto_const_nhds
  have heq :
      (fun R : ℕ => (∑ n ∈ Finset.range (N * (R + 1)), q n) - I) =ᶠ[atTop]
        (fun R : ℕ => ∑ n ∈ Finset.Ioc K (N * (R + 1) - 1), q n) := by
    filter_upwards [eventually_gt_atTop K] with R hR
    have hNpos : 0 < N := NeZero.pos N
    let E : ℕ := N * (R + 1)
    have hKE : K + 1 ≤ E := by
      dsimp [E]
      have hscale : R + 1 ≤ N * (R + 1) :=
        Nat.le_mul_of_pos_left (R + 1) hNpos
      omega
    have hset : Finset.Ioc K (E - 1) = Finset.Ico (K + 1) E := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [hset]
    have hsplit := Finset.sum_range_add_sum_Ico q hKE
    dsimp [I, E]
    rw [← hsplit]
    ring
  have htail : Tendsto
      (fun R : ℕ => ∑ n ∈ Finset.Ioc K (N * (R + 1) - 1), q n)
      atTop (nhds (L - I)) := hsub.congr' heq
  have htailBound : ‖L - I‖ ≤
      (N : ℝ) * (3 + |t|) * (K : ℝ)⁻¹ := by
    apply le_of_tendsto htail.norm
    filter_upwards [eventually_gt_atTop K] with R hR
    have hNpos : 0 < N := NeZero.pos N
    have hKM : K < N * (R + 1) - 1 := by
      have hscale : R + 1 ≤ N * (R + 1) :=
        Nat.le_mul_of_pos_left (R + 1) hNpos
      omega
    change ‖∑ n ∈ Finset.Ioc K (N * (R + 1) - 1),
      rightBoundaryWeight t n * chi (n : ZMod N)‖ ≤ _
    exact nonprincipal_rightBoundary_tail_finite chi hchi t hK hKM
  have htriangle : ‖L‖ ≤ ‖I‖ + ‖L - I‖ := by
    calc
      ‖L‖ = ‖(L - I) + I‖ := by congr 1 <;> ring
      _ ≤ ‖L - I‖ + ‖I‖ := norm_add_le _ _
      _ = ‖I‖ + ‖L - I‖ := add_comm _ _
  exact htriangle.trans (by
    simpa [I, add_comm] using add_le_add_left htailBound ‖I‖)

/-- The initial segment has the same harmonic majorant as at the real point
`s=1`; the oscillation only changes phases. -/
theorem norm_rightBoundary_initialSum_le
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (t : ℝ) {K : ℕ} (hK : 1 ≤ K) :
    ‖∑ n ∈ Finset.range (K + 1),
        rightBoundaryWeight t n * chi (n : ZMod N)‖ ≤
      1 + Real.log K := by
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
      · rw [Finset.sum_singleton]
        change ‖rightBoundaryWeight t 0 * chi ((0 : ℕ) : ZMod N)‖ +
          ∑ n ∈ Finset.Icc 1 K,
            ‖rightBoundaryWeight t n * chi (n : ZMod N)‖ ≤ _
        rw [rightBoundaryWeight, if_pos rfl, zero_mul, norm_zero, zero_add]
        apply Finset.sum_le_sum
        intro n hn
        have hn1 := (Finset.mem_Icc.mp hn).1
        rw [norm_mul, norm_rightBoundaryWeight (by omega)]
        simpa using mul_le_mul_of_nonneg_left (chi.norm_le_one n)
          (inv_nonneg.mpr (Nat.cast_nonneg n))
      · simp
    _ = (harmonic K : ℝ) := by rw [sum_Icc_inv_eq_harmonic_real K]
    _ ≤ 1 + Real.log K := harmonic_le_one_add_log K

/-- A completely explicit logarithmic bound on the right edge.  No
Pólya--Vinogradov estimate is needed: periodic cancellation and the cutoff
`ceil (N * (3 + |t|))` suffice. -/
theorem nonprincipal_norm_LFunction_rightBoundary_le
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (t : ℝ) :
    ‖DirichletCharacter.LFunction chi (rightBoundaryPoint t)‖ ≤
      3 * (1 + Real.log (2 * (N : ℝ) * (3 + |t|))) := by
  let R : ℝ := (N : ℝ) * (3 + |t|)
  let K : ℕ := ⌈R⌉₊
  have hNone : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hNone
  have hRthree : 3 ≤ R := by
    dsimp [R]
    nlinarith [abs_nonneg t]
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hRthree
  have hKpos : 0 < K := by
    dsimp [K]
    exact Nat.ceil_pos.mpr hRpos
  have hK : 1 ≤ K := hKpos
  have hRleK : R ≤ (K : ℝ) := by
    dsimp [K]
    exact Nat.le_ceil R
  have hKlt : (K : ℝ) < R + 1 := by
    dsimp [K]
    exact Nat.ceil_lt_add_one hRpos.le
  have hKleTwoR : (K : ℝ) ≤ 2 * R := by
    linarith
  have htail :
      (N : ℝ) * (3 + |t|) * (K : ℝ)⁻¹ ≤ 1 := by
    change R * (K : ℝ)⁻¹ ≤ 1
    rw [← div_eq_mul_inv]
    exact (div_le_one (by exact_mod_cast hKpos)).2 hRleK
  have hlog : Real.log (K : ℝ) ≤ Real.log (2 * R) := by
    have hKreal : (0 : ℝ) < K := by exact_mod_cast hKpos
    have htwoR : (0 : ℝ) < 2 * R := by positivity
    exact Real.strictMonoOn_log.monotoneOn hKreal htwoR hKleTwoR
  have hlog0 : 0 ≤ Real.log (2 * R) := by
    apply Real.log_nonneg
    nlinarith
  have hraw := norm_LFunction_rightBoundary_le_initial_add_tail
    chi hchi t (K := K) hK
  have hinit := norm_rightBoundary_initialSum_le chi t (K := K) hK
  calc
    ‖DirichletCharacter.LFunction chi (rightBoundaryPoint t)‖ ≤
        ‖∑ n ∈ Finset.range (K + 1),
          rightBoundaryWeight t n * chi (n : ZMod N)‖ +
        (N : ℝ) * (3 + |t|) * (K : ℝ)⁻¹ := hraw
    _ ≤ (1 + Real.log K) + 1 := add_le_add hinit htail
    _ ≤ 3 * (1 + Real.log (2 * R)) := by nlinarith
    _ = 3 * (1 + Real.log (2 * (N : ℝ) * (3 + |t|))) := by
      simp only [R, mul_assoc]

end

end MAPJutilaRightEdgeLogBound

#print axioms MAPJutilaRightEdgeLogBound.norm_sum_Ioc_mul_le_of_complex_variation
#print axioms MAPJutilaRightEdgeLogBound.norm_rightBoundaryWeight_succ_sub_le
#print axioms MAPJutilaRightEdgeLogBound.nonprincipal_norm_LFunction_rightBoundary_le
