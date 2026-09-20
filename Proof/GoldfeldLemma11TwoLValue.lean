import GoldfeldLemma11TwoNormalized

/-!
# The `j = 0`, `s = 1` form of Koukoulopoulos, Lemma 11.2

The complete-block continuation is combined with Pólya--Vinogradov and Abel
summation at cutoff `K = N`.
-/

namespace MAPGoldfeldSiegel

open Complex Set LSeries Filter Topology
open scoped BigOperators

noncomputable section

def zerothDerivativeWeight (n : ℕ) : ℝ := (n : ℝ)⁻¹

theorem zerothDerivativeWeight_nonneg (n : ℕ) :
    0 ≤ zerothDerivativeWeight n := by
  exact inv_nonneg.mpr (Nat.cast_nonneg n)

theorem zerothDerivativeWeight_antitone {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    zerothDerivativeWeight n ≤ zerothDerivativeWeight m := by
  unfold zerothDerivativeWeight
  exact (inv_le_inv₀
    (by exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_of_lt hm) hmn))
    (by exact_mod_cast (Nat.zero_lt_of_lt hm))).2
      (by exact_mod_cast hmn)

/-- Finite Abel tail for the undifferentiated series. -/
theorem primitive_quadratic_Lone_tail_finite
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) (hreal : chi ^ 2 = 1)
    {K M : ℕ} (hK : 1 ≤ K) (hKM : K < M) :
    ‖∑ n ∈ Finset.Ioc K M,
        (zerothDerivativeWeight n : ℂ) * chi (n : ZMod N)‖ ≤
      2 * (Real.sqrt N * (1 + Real.log N)) *
        zerothDerivativeWeight (K + 1) := by
  apply norm_sum_Ioc_mul_le_two_mul_of_antitone
  · exact hKM
  · intro n
    exact primitive_quadratic_initialSum_norm_le hN chi hprim hreal n
  · intro n _ _
    exact zerothDerivativeWeight_nonneg n
  · intro i hKi _
    exact zerothDerivativeWeight_antitone (by omega) (Nat.le_succ i)

/-- At `s = 1`, an L-series term is the reciprocal weight used above. -/
theorem LSeries_term_one_eq_zerothDerivativeWeight
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (n : ℕ) :
    LSeries.term (fun m : ℕ => chi m) (1 : ℂ) n =
      (zerothDerivativeWeight n : ℂ) * chi (n : ZMod N) := by
  by_cases hn : n = 0
  · subst n
    simp [zerothDerivativeWeight]
  · rw [LSeries.term_of_ne_zero hn]
    simp only [one_mul, Complex.cpow_one]
    rw [div_eq_mul_inv]
    simp [zerothDerivativeWeight, mul_comm]

/-- The centered complete blocks are summable at `s = 1`. -/
theorem summable_centeredCharacterLBlock_one
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) :
    Summable (fun m : ℕ => centeredCharacterLBlock chi m 1) := by
  have hmajor := summable_centeredBlockMajorant
    (N := N) (a := (1 / 2 : ℝ)) (B := (1 : ℝ)) (by norm_num)
  have hnorm : Summable (fun m : ℕ => ‖centeredCharacterLBlock chi m 1‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => by
        have h := norm_centeredCharacterLBlock_le chi
          (a := (1 / 2 : ℝ)) (B := (1 : ℝ)) (by norm_num)
          (s := (1 : ℂ)) (by norm_num) (by norm_num) m
        simpa using h)
      hmajor
  exact summable_norm_iff.mp hnorm

/-- Complete-block partial sums converge to the continued L-function at
`s = 1`. -/
theorem tendsto_zerothDerivativeWeight_sum_blocks
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    Tendsto
      (fun R : ℕ => ∑ n ∈ Finset.range (N * (R + 1)),
        (zerothDerivativeWeight n : ℂ) * chi (n : ZMod N))
      atTop (nhds (DirichletCharacter.LFunction chi 1)) := by
  have hsum := summable_centeredCharacterLBlock_one chi
  have ht : Tendsto
      (fun R : ℕ => characterLBlock chi 0 1 +
        ∑ m ∈ Finset.range R, centeredCharacterLBlock chi m 1)
      atTop (nhds (characterLBlock chi 0 1 +
        ∑' m : ℕ, centeredCharacterLBlock chi m 1)) :=
    tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat
  have hfinite : ∀ R : ℕ,
      characterLBlock chi 0 1 +
          ∑ m ∈ Finset.range R, centeredCharacterLBlock chi m 1 =
        ∑ n ∈ Finset.range (N * (R + 1)),
          LSeries.term (fun n : ℕ => chi n) 1 n := by
    intro R
    calc
      characterLBlock chi 0 1 +
          ∑ m ∈ Finset.range R, centeredCharacterLBlock chi m 1 =
          characterLBlock chi 0 1 +
            ∑ m ∈ Finset.range R, characterLBlock chi (m + 1) 1 := by
        congr 1
        apply Finset.sum_congr rfl
        intro m hm
        exact centeredCharacterLBlock_eq chi hchi m 1
      _ = ∑ m ∈ Finset.range (R + 1), characterLBlock chi m 1 := by
        rw [Finset.sum_range_succ']
        ring
      _ = ∑ n ∈ Finset.range (N * (R + 1)),
          LSeries.term (fun n : ℕ => chi n) 1 n := by
        simpa [characterLBlock] using
          (sum_range_mul_eq_sum_blocks (N := N)
            (fun n => LSeries.term (fun n : ℕ => chi n) 1 n) (R + 1))
  have htBlocks : Tendsto
      (fun R : ℕ => ∑ n ∈ Finset.range (N * (R + 1)),
        LSeries.term (fun n : ℕ => chi n) 1 n)
      atTop (nhds (conditionalCharacterLSeries chi 1)) := by
    have := ht.congr' (Filter.Eventually.of_forall fun R => hfinite R)
    simpa [conditionalCharacterLSeries] using this
  have hident := conditionalCharacterLSeries_eq_LFunction_of_pos_re
    chi hchi (s := (1 : ℂ)) (by norm_num)
  rw [hident] at htBlocks
  apply htBlocks.congr'
  exact Filter.Eventually.of_forall fun R => by
    apply Finset.sum_congr rfl
    intro n hn
    exact LSeries_term_one_eq_zerothDerivativeWeight chi n

/-- Exact `s = 1` estimate before the elementary cutoff absorption. -/
theorem norm_LFunction_one_le_initial_add_PV_tail
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (chi : DirichletCharacter ℂ N) (hprim : chi.IsPrimitive)
    (hchi : chi ≠ 1) (hreal : chi ^ 2 = 1) :
    ‖DirichletCharacter.LFunction chi 1‖ ≤
      ‖∑ n ∈ Finset.range (N + 1),
        (zerothDerivativeWeight n : ℂ) * chi (n : ZMod N)‖ +
      2 * (Real.sqrt N * (1 + Real.log N)) *
        zerothDerivativeWeight (N + 1) := by
  let q : ℕ → ℂ := fun n =>
    (zerothDerivativeWeight n : ℂ) * chi (n : ZMod N)
  let L : ℂ := DirichletCharacter.LFunction chi 1
  let I : ℂ := ∑ n ∈ Finset.range (N + 1), q n
  have htotal := tendsto_zerothDerivativeWeight_sum_blocks chi hchi
  change Tendsto (fun R : ℕ => ∑ n ∈ Finset.range (N * (R + 1)), q n)
    atTop (nhds L) at htotal
  have hsub : Tendsto
      (fun R : ℕ => (∑ n ∈ Finset.range (N * (R + 1)), q n) - I)
      atTop (nhds (L - I)) := htotal.sub tendsto_const_nhds
  have heq :
      (fun R : ℕ => (∑ n ∈ Finset.range (N * (R + 1)), q n) - I) =ᶠ[atTop]
        (fun R : ℕ => ∑ n ∈ Finset.Ioc N (N * (R + 1) - 1), q n) := by
    filter_upwards [eventually_gt_atTop N] with R hR
    have hNpos : 0 < N := NeZero.pos N
    let E : ℕ := N * (R + 1)
    have hNE : N + 1 ≤ E := by
      dsimp [E]
      have hNone : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
      nlinarith
    have hset : Finset.Ioc N (E - 1) = Finset.Ico (N + 1) E := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [hset]
    have hsplit := Finset.sum_range_add_sum_Ico q hNE
    dsimp [I, E]
    rw [← hsplit]
    ring
  have htail : Tendsto
      (fun R : ℕ => ∑ n ∈ Finset.Ioc N (N * (R + 1) - 1), q n)
      atTop (nhds (L - I)) := hsub.congr' heq
  have htailBound : ‖L - I‖ ≤
      2 * (Real.sqrt N * (1 + Real.log N)) *
        zerothDerivativeWeight (N + 1) := by
    apply le_of_tendsto htail.norm
    filter_upwards [eventually_gt_atTop N] with R hR
    have hNpos : 0 < N := NeZero.pos N
    have hNM : N < N * (R + 1) - 1 := by
      have hscale : R + 1 ≤ N * (R + 1) :=
        Nat.le_mul_of_pos_left (R + 1) hNpos
      omega
    change ‖∑ n ∈ Finset.Ioc N (N * (R + 1) - 1),
      (zerothDerivativeWeight n : ℂ) * chi (n : ZMod N)‖ ≤ _
    exact primitive_quadratic_Lone_tail_finite hN chi hprim hreal
      (show 1 ≤ N by omega) hNM
  have htriangle : ‖L‖ ≤ ‖I‖ + ‖L - I‖ := by
    calc
      ‖L‖ = ‖(L - I) + I‖ := by congr 1 <;> ring
      _ ≤ ‖L - I‖ + ‖I‖ := norm_add_le _ _
      _ = ‖I‖ + ‖L - I‖ := add_comm _ _
  exact htriangle.trans (by
    simpa [I, add_comm] using add_le_add_left htailBound ‖I‖)

/-- Trivial initial segment at cutoff `K=N`. -/
theorem norm_zerothDerivative_initialSum_le
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) :
    ‖∑ n ∈ Finset.range (N + 1),
        (zerothDerivativeWeight n : ℂ) * chi (n : ZMod N)‖ ≤
      1 + Real.log N := by
  have hNone : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  calc
    ‖∑ n ∈ Finset.range (N + 1),
        (zerothDerivativeWeight n : ℂ) * chi (n : ZMod N)‖ ≤
        ∑ n ∈ Finset.range (N + 1),
          ‖(zerothDerivativeWeight n : ℂ) * chi (n : ZMod N)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ((n : ℝ)⁻¹) := by
      rw [show Finset.range (N + 1) = {0} ∪ Finset.Icc 1 N by
        ext n
        simp
        omega]
      rw [Finset.sum_union]
      · simp only [Finset.sum_singleton, zerothDerivativeWeight,
          Nat.cast_zero, inv_zero, Complex.ofReal_zero, zero_mul, norm_zero,
          zero_add]
        apply Finset.sum_le_sum
        intro n hn
        have hn1 := (Finset.mem_Icc.mp hn).1
        rw [norm_mul, norm_real, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
        simpa using mul_le_mul_of_nonneg_left (chi.norm_le_one n)
          (inv_nonneg.mpr (Nat.cast_nonneg n))
      · simp
    _ = (harmonic N : ℝ) := by rw [sum_Icc_inv_eq_harmonic_real N]
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N

/-- Koukoulopoulos, Lemma 11.2 at `j=0`, `s=1`, specialized to primitive
quadratic characters. -/
theorem primitive_quadratic_norm_LFunction_one_le
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (chi : DirichletCharacter ℂ N) (hprim : chi.IsPrimitive)
    (hchi : chi ≠ 1) (hreal : chi ^ 2 = 1) :
    ‖DirichletCharacter.LFunction chi 1‖ ≤
      3 * (1 + Real.log N) := by
  have hraw := norm_LFunction_one_le_initial_add_PV_tail
    hN chi hprim hchi hreal
  have hinit := norm_zerothDerivative_initialSum_le chi
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsqrt : Real.sqrt (N : ℝ) ≤ N + 1 := by
    have hR := Real.sqrt_nonneg (N : ℝ)
    have hRsq := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
    nlinarith [sq_nonneg (Real.sqrt (N : ℝ) - 1)]
  have hlog0 : 0 ≤ 1 + Real.log (N : ℝ) := by
    have hNoneR : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (show 1 ≤ N by omega)
    have := Real.log_nonneg hNoneR
    linarith
  have htail :
      2 * (Real.sqrt N * (1 + Real.log N)) *
          zerothDerivativeWeight (N + 1) ≤
        2 * (1 + Real.log N) := by
    unfold zerothDerivativeWeight
    have hden : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    have hsqrt' : Real.sqrt (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      norm_num
      exact hsqrt
    have hratio : Real.sqrt (N : ℝ) / ((N + 1 : ℕ) : ℝ) ≤ 1 :=
      (div_le_one hden).2 hsqrt'
    calc
      2 * (Real.sqrt N * (1 + Real.log N)) * (((N + 1 : ℕ) : ℝ))⁻¹ =
          (2 * (1 + Real.log N)) *
            (Real.sqrt N / ((N + 1 : ℕ) : ℝ)) := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ (2 * (1 + Real.log N)) * 1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 2 * (1 + Real.log N) := by ring
  calc
    ‖DirichletCharacter.LFunction chi 1‖ ≤ _ := hraw
    _ ≤ (1 + Real.log N) + 2 * (1 + Real.log N) :=
      add_le_add hinit htail
    _ = 3 * (1 + Real.log N) := by ring

/-- A nonprincipal character has uniformly bounded incomplete sums by the
length of one complete residue block.  This elementary bound is sufficient
for the `j=0`, `s=1` estimate even when the character is imprimitive. -/
theorem nonprincipal_initialSum_norm_le_level
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    (M : ℕ) :
    ‖∑ n ∈ Finset.range M, chi (n : ZMod N)‖ ≤ N := by
  let Q := M / N
  let E := N * Q
  have hEM : E ≤ M := by
    dsimp [E, Q]
    exact Nat.mul_div_le M N
  have hME : M ≤ E + N := by
    dsimp [E, Q]
    have hmod := Nat.mod_lt M (NeZero.pos N)
    have hdiv := Nat.div_add_mod M N
    omega
  have hblocks : ∑ n ∈ Finset.range E, chi (n : ZMod N) = 0 := by
    have hdecomp := sum_range_mul_eq_sum_blocks
      (N := N) (fun n => chi (n : ZMod N)) Q
    rw [← hdecomp]
    apply Finset.sum_eq_zero
    intro m hm
    have hsum : ∑ j : ZMod N, chi j = 0 :=
      MulChar.sum_eq_zero_of_ne_one hchi
    simpa using hsum
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun n => chi (n : ZMod N)) hEM
  rw [← hsplit, hblocks, zero_add]
  calc
    ‖∑ n ∈ Finset.Ico E M, chi (n : ZMod N)‖ ≤
        ∑ n ∈ Finset.Ico E M, ‖chi (n : ZMod N)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ico E M, (1 : ℝ) := by
      gcongr with n hn
      exact chi.norm_le_one n
    _ = ((M - E : ℕ) : ℝ) := by simp
    _ ≤ N := by
      exact_mod_cast ((Nat.sub_le_iff_le_add).2 (by omega : M ≤ N + E))

/-- Finite Abel tail for an arbitrary nonprincipal character, using only one
complete residue block as the partial-sum bound. -/
theorem nonprincipal_Lone_tail_finite
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    {K M : ℕ} (hK : 1 ≤ K) (hKM : K < M) :
    ‖∑ n ∈ Finset.Ioc K M,
        (zerothDerivativeWeight n : ℂ) * chi (n : ZMod N)‖ ≤
      2 * (N : ℝ) * zerothDerivativeWeight (K + 1) := by
  apply norm_sum_Ioc_mul_le_two_mul_of_antitone
  · exact hKM
  · intro n
    exact nonprincipal_initialSum_norm_le_level chi hchi n
  · intro n _ _
    exact zerothDerivativeWeight_nonneg n
  · intro i hKi _
    exact zerothDerivativeWeight_antitone (by omega) (Nat.le_succ i)

/-- Exact `s=1` estimate for an arbitrary nonprincipal character. -/
theorem norm_LFunction_one_le_initial_add_level_tail
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖DirichletCharacter.LFunction chi 1‖ ≤
      ‖∑ n ∈ Finset.range (N + 1),
        (zerothDerivativeWeight n : ℂ) * chi (n : ZMod N)‖ +
      2 * (N : ℝ) * zerothDerivativeWeight (N + 1) := by
  let q : ℕ → ℂ := fun n =>
    (zerothDerivativeWeight n : ℂ) * chi (n : ZMod N)
  let L : ℂ := DirichletCharacter.LFunction chi 1
  let I : ℂ := ∑ n ∈ Finset.range (N + 1), q n
  have htotal := tendsto_zerothDerivativeWeight_sum_blocks chi hchi
  change Tendsto (fun R : ℕ => ∑ n ∈ Finset.range (N * (R + 1)), q n)
    atTop (nhds L) at htotal
  have hsub : Tendsto
      (fun R : ℕ => (∑ n ∈ Finset.range (N * (R + 1)), q n) - I)
      atTop (nhds (L - I)) := htotal.sub tendsto_const_nhds
  have heq :
      (fun R : ℕ => (∑ n ∈ Finset.range (N * (R + 1)), q n) - I) =ᶠ[atTop]
        (fun R : ℕ => ∑ n ∈ Finset.Ioc N (N * (R + 1) - 1), q n) := by
    filter_upwards [eventually_gt_atTop N] with R hR
    have hNpos : 0 < N := NeZero.pos N
    let E : ℕ := N * (R + 1)
    have hNE : N + 1 ≤ E := by
      dsimp [E]
      have hNone : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
      nlinarith
    have hset : Finset.Ioc N (E - 1) = Finset.Ico (N + 1) E := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [hset]
    have hsplit := Finset.sum_range_add_sum_Ico q hNE
    dsimp [I, E]
    rw [← hsplit]
    ring
  have htail : Tendsto
      (fun R : ℕ => ∑ n ∈ Finset.Ioc N (N * (R + 1) - 1), q n)
      atTop (nhds (L - I)) := hsub.congr' heq
  have htailBound : ‖L - I‖ ≤
      2 * (N : ℝ) * zerothDerivativeWeight (N + 1) := by
    apply le_of_tendsto htail.norm
    filter_upwards [eventually_gt_atTop N] with R hR
    have hNpos : 0 < N := NeZero.pos N
    have hNM : N < N * (R + 1) - 1 := by
      have hscale : R + 1 ≤ N * (R + 1) :=
        Nat.le_mul_of_pos_left (R + 1) hNpos
      omega
    change ‖∑ n ∈ Finset.Ioc N (N * (R + 1) - 1),
      (zerothDerivativeWeight n : ℂ) * chi (n : ZMod N)‖ ≤ _
    exact nonprincipal_Lone_tail_finite chi hchi
      (show 1 ≤ N by omega) hNM
  have htriangle : ‖L‖ ≤ ‖I‖ + ‖L - I‖ := by
    calc
      ‖L‖ = ‖(L - I) + I‖ := by congr 1 <;> ring
      _ ≤ ‖L - I‖ + ‖I‖ := norm_add_le _ _
      _ = ‖I‖ + ‖L - I‖ := add_comm _ _
  exact htriangle.trans (by
    simpa [I, add_comm] using add_le_add_left htailBound ‖I‖)

/-- Lemma 11.2 at `j=0`, `s=1`, for every nonprincipal character at its
current level.  This is the form used for the possibly imprimitive product in
Goldfeld's four-L residue. -/
theorem nonprincipal_norm_LFunction_one_le
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖DirichletCharacter.LFunction chi 1‖ ≤
      3 * (1 + Real.log N) := by
  have hraw := norm_LFunction_one_le_initial_add_level_tail chi hchi
  have hinit := norm_zerothDerivative_initialSum_le chi
  have hNone : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hNone)
  have htail : 2 * (N : ℝ) * zerothDerivativeWeight (N + 1) ≤ 2 := by
    unfold zerothDerivativeWeight
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((N + 1 : ℕ) : ℝ))).2
    norm_num
  calc
    ‖DirichletCharacter.LFunction chi 1‖ ≤ _ := hraw
    _ ≤ (1 + Real.log N) + 2 := add_le_add hinit htail
    _ ≤ 3 * (1 + Real.log N) := by linarith

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.primitive_quadratic_Lone_tail_finite
#print axioms MAPGoldfeldSiegel.tendsto_zerothDerivativeWeight_sum_blocks
#print axioms MAPGoldfeldSiegel.norm_LFunction_one_le_initial_add_PV_tail
#print axioms MAPGoldfeldSiegel.primitive_quadratic_norm_LFunction_one_le
#print axioms MAPGoldfeldSiegel.nonprincipal_initialSum_norm_le_level
#print axioms MAPGoldfeldSiegel.nonprincipal_norm_LFunction_one_le
